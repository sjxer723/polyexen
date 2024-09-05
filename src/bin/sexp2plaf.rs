use std::{hash::Hash, iter::Product, time::Instant, time::Duration, fs::read_to_string, env};

use polyexen::expr;

use ark_std::{end_timer, perf_trace::TimerInfo, start_timer, Zero};
use halo2_proofs::{
    dev::{cost::CircuitCost, MockProver},
    halo2curves::{bn256::{Bn256, Fr, G1Affine, G2}, group::prime::PrimeGroup},
    plonk::{create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, ProvingKey, VerifyingKey},
    poly::{commitment::ParamsProver, kzg::{
        commitment::{KZGCommitmentScheme, ParamsKZG}, multiopen::{ProverSHPLONK, VerifierSHPLONK},
        strategy::SingleStrategy,
    }},
    transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
    },
};
use num_bigint::BigUint;
use polyexen::{
    expr::{get_field_p, ColumnKind, ColumnQuery, Expr, PlonkVar as Var},
    parser::parse_expr,
    plaf::{backends::{fs,halo2::{PlafH2Circuit, PARAMS}}, ColumnFixed, ColumnWitness, CopyC, Plaf, Poly, Witness,},
};
use rand::{rngs::StdRng, SeedableRng};
use sexp::{parse, Atom, Sexp};
use once_cell::sync::Lazy;
use std::collections::HashMap;

fn parse_atom_string(a: &Atom) -> String {
    match a {
        Atom::S(s) => s.clone(),
        _ => String::from(""),
    }
}

fn parse_atom_i(a: &Atom) -> i64 {
    match a {
        Atom::I(i) => i.clone(),
        _ => 0,
    }
}

fn parse_atom_f(a: &Atom) -> f64 {
    match a {
        Atom::F(f) => f.clone(),
        _ => 0.0,
    }
}

fn parse_sexp_atom(s: &Sexp) -> Atom {
    match s {
        Sexp::Atom(a) => a.clone(),
        _ => unreachable!(),
    }
}

fn parse_sexp_list(s: &Sexp) -> Vec<Sexp> {
    match s {
        Sexp::List(l) => l.clone(),
        _ => unreachable!(),
    }
}

fn parse_sexp_expr(s: &Sexp, m: &mut HashMap<String, usize>) -> expr::Expr<expr::PlonkVar> {
    let ops = parse_sexp_list(s);
    let t = parse_atom_string(&parse_sexp_atom(&ops[0]));

    if t == "Binop" {
        let op = parse_atom_string(&parse_sexp_atom(&ops[1]));
        match op.as_str() {
            "Add" => {
                return Expr::Sum(vec![
                    parse_sexp_expr(&ops[2], m),
                    parse_sexp_expr(&ops[3], m),
                ])
            }
            "Sub" => {
                return Expr::Sum(vec![
                    parse_sexp_expr(&ops[2], m),
                    Expr::Neg(Box::new(parse_sexp_expr(&ops[3], m))),
                ])
            }
            "Mul" => {
                return Expr::Mul(vec![
                    parse_sexp_expr(&ops[2], m),
                    parse_sexp_expr(&ops[3], m),
                ])
            }
            _ => {}
        }
    } else if t == "Selector" {
        let name = parse_atom_string(&parse_sexp_atom(&ops[1]));

        return Expr::Var(Var::Query(ColumnQuery {
            column: expr::Column {
                kind: ColumnKind::Fixed,
                index: m.get(&name).unwrap().clone(),
            },
            rotation: 0,
        }));
    } else if t == "Ref" {
        let rotation = parse_atom_i(&parse_sexp_atom(&ops[1]));

        return Expr::Var(Var::Query(ColumnQuery {
            column: expr::Column {
                kind: ColumnKind::Witness,
                index: 0,
            },
            rotation: rotation as i32,
        }));
    } else if t == "Const" {
        let num = parse_atom_i(&parse_sexp_atom(&ops[1]));

        return Expr::Const(BigUint::from(num as u128));
    }

    Expr::Const(BigUint::zero())
}

#[warn(unused_assignments)]
fn parse_plaf_field(
    a: &Atom,
    kvs: &Vec<Sexp>,
    selector_index: &mut HashMap<String, usize>,
    plaf: &mut Plaf,
    wit: &mut Witness,
) {
    let s = match a {
        Atom::S(s) => s.clone(),
        _ => String::from(""),
    };

    let mut k = 0;
    let mut columns_witness = vec![];
    let mut columns_fixed = vec![];
    let mut offsets = vec![];
    let mut s_locs = vec![];
    let mut locs = vec![];
    let mut fixed_values_loc = vec![];
    let mut fixed_value_col = vec![];
    let mut witness_value_col = vec![];
    let mut fixed_values = vec![];
    let mut witness_values = vec![];
    let mut polys = vec![];

    match s.as_str() {
        "col" => {
            for v in &kvs[1..] {
                match v {
                    Sexp::Atom(a1) => {
                        columns_witness.push(ColumnWitness::new(parse_atom_string(&a1), 0))
                    }
                    _ => {}
                }
            }
        }
        "k" => match &kvs[1] {
            Sexp::Atom(a1) => k = parse_atom_i(&a1) as usize,
            _ => {}
        },
        "selectors" => match &kvs[1] {
            Sexp::List(l) => {
                for (index, selector) in l.iter().enumerate() {
                    match selector {
                        Sexp::Atom(_selector) => {
                            selector_index.insert(parse_atom_string(_selector), index);
                            columns_fixed.push(ColumnFixed::new(parse_atom_string(_selector)))
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        },
        "polynomial_gates" => match &kvs[1] {
            Sexp::List(gates) => {
                for (_idx, _gate) in gates.iter().enumerate() {
                    polys.push(Poly {
                        name: String::from(format!("gate{}", _idx)),
                        exp: parse_sexp_expr(_gate, selector_index),
                    })
                }
            }
            _ => {}
        },
        "copy_gates" => match &kvs[1] {
            Sexp::List(cps) => {
                for cp in cps {
                    offsets.push((
                        parse_atom_i(&parse_sexp_atom(&parse_sexp_list(cp)[0])) as usize,
                        parse_atom_i(&parse_sexp_atom(&parse_sexp_list(cp)[1])) as usize,
                    ))
                }
            }
            _ => {}
        },
        "selector_values" => match &kvs[1] {
            Sexp::List(svs) => {
                for _sv in svs {
                    s_locs = parse_sexp_list(_sv);
                    locs = vec![];
                    for _v in parse_sexp_list(&s_locs[1]) {
                        locs.push(parse_atom_i(&parse_sexp_atom(&_v)) as u64);
                    }
                    fixed_values_loc.push(locs.clone())
                }
            }
            _ => {}
        },
        "witness_values" => {
            match &kvs[1] {
                Sexp::List(wvs) => {
                    for _wv in wvs {
                        witness_value_col
                            .push(Some(BigUint::from(parse_atom_i(&parse_sexp_atom(
                                &parse_sexp_list(_wv)[1],
                            )) as u128)))
                    }
                }
                _ => {}
            }
            witness_values.push(witness_value_col)
        }
        _ => println!("The string is something else"),
    }

    // Update plaf
    match s.as_str() {
        "col" => {
            plaf.columns.witness = columns_witness.clone();
            wit.columns = columns_witness.clone();
        }
        "k" => {
            plaf.info.num_rows = k;
            wit.num_rows = k;
        }
        "polynomial_gates" => plaf.polys = polys,
        "selectors" => plaf.columns.fixed = columns_fixed,
        "selector_values" => {
            for loc_col in fixed_values_loc {
                fixed_value_col = vec![Some(BigUint::from(0 as u8)); plaf.info.num_rows];
                for _loc in loc_col {
                    fixed_value_col[_loc as usize] = Some(BigUint::from(1 as u8));
                }
                fixed_values.push(fixed_value_col)
            }
            plaf.fixed = fixed_values;
        }
        "copy_gates" => {
            plaf.copys = vec![CopyC {
                columns: (
                    expr::Column {
                        kind: ColumnKind::Witness,
                        index: 0,
                    },
                    expr::Column {
                        kind: ColumnKind::Witness,
                        index: 0,
                    },
                ),
                offsets: offsets,
            }]
        }
        "witness_values" => {
            wit.witness = witness_values;
        }
        _ => {}
    }
}

fn parse_plaf_field_list(l: Vec<Sexp>, plaf: &mut Plaf, wit: &mut Witness) {
    let mut selector_index: HashMap<String, usize> = HashMap::new();

    for s in l {
        if let Sexp::List(kvs) = s {
            match &kvs[0] {
                Sexp::Atom(a) => parse_plaf_field(a, &kvs, &mut selector_index, plaf, wit),
                _ => unreachable!(),
            }
        }
    }
}

/// Helper function to generate a proof with real prover using SHPLONK KZG multi-open polynomical commitment scheme
/// and Blake2b as the hash function for Fiat-Shamir.
pub fn gen_proof_with_instances(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: impl Circuit<Fr>,
    instances: &[&[Fr]],
) -> Vec<u8> {
    let rng = StdRng::seed_from_u64(0);
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    create_proof::<
        KZGCommitmentScheme<Bn256>,
        ProverSHPLONK<'_, Bn256>,
        Challenge255<_>,
        _,
        Blake2bWrite<Vec<u8>, G1Affine, _>,
        _,
    >(params, pk, &[circuit], &[instances], rng, &mut transcript)
    .expect("prover should not fail");
    transcript.finalize()
}

/// For testing use only: Helper function to generate a proof **without public instances** with real prover using SHPLONK KZG multi-open polynomical commitment scheme
/// and Blake2b as the hash function for Fiat-Shamir.
pub fn gen_proof(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: impl Circuit<Fr>,
) -> Vec<u8> {
    gen_proof_with_instances(params, pk, circuit, &[])
}

/// Helper function to verify a proof (generated using [`gen_proof_with_instances`]) using SHPLONK KZG multi-open polynomical commitment scheme
/// and Blake2b as the hash function for Fiat-Shamir.
pub fn check_proof_with_instances(
    params: &ParamsKZG<Bn256>,
    vk: &VerifyingKey<G1Affine>,
    proof: &[u8],
    instances: &[&[Fr]],
    expect_satisfied: bool,
) {
    let verifier_params = params.verifier_params();
    let strategy = SingleStrategy::new(params);
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(proof);
    let res = verify_proof::<
        KZGCommitmentScheme<Bn256>,
        VerifierSHPLONK<'_, Bn256>,
        Challenge255<G1Affine>,
        Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>,
        SingleStrategy<'_, Bn256>,
    >(verifier_params, vk, strategy, &[instances], &mut transcript);
    // Just FYI, because strategy is `SingleStrategy`, the output `res` is `Result<(), Error>`, so there is no need to call `res.finalize()`.

    if expect_satisfied {
        res.unwrap();
    } else {
        assert!(res.is_err());
    }
}

/// For testing only: Helper function to verify a proof (generated using [`gen_proof`]) without public instances using SHPLONK KZG multi-open polynomical commitment scheme
/// and Blake2b as the hash function for Fiat-Shamir.
pub fn check_proof(
    params: &ParamsKZG<Bn256>,
    vk: &VerifyingKey<G1Affine>,
    proof: &[u8],
    expect_satisfied: bool,
) {
    check_proof_with_instances(params, vk, proof, &[], expect_satisfied);
}


#[derive(Debug)]
struct Cost <G: PrimeGroup, PlafH2Circuit: Circuit<G::Scalar>>{
    mockprover_verified: bool,
    // Circuit cost
    circuit_cost: CircuitCost::<G, PlafH2Circuit>,
    // Time cost
    vk_time: f64,
    pk_time: f64,
    proof_time: f64,
    proof_size: usize,
    verify_time: f64,
}

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        println!("Usage: {} <sexp_file_path>", args[0]);
        return;
    } 
    let sexp_file_path = &args[1];
    let input: String;
    
    if let Ok(sexp_content) = read_to_string(sexp_file_path) {
        input = sexp_content.clone();
    } else {
        println!("Fail to read the file {}", sexp_file_path);
        return;
    }
    // let input = "((col w)  2) (9 1) (10 2) (11 0) (12 1))))";
    // let input = "((col w) (k 10) (selectors (q0 q1))
    // (polynomial_gates
    //  ((Binop Mul (Selector q0) (Binop Sub (Ref -3) (Ref -1)))
    //   (Binop Mul (Selector q1)
    //    (Binop Sub (Ref 0) (Binop Add (Ref -2) (Ref -1))))))
    // (copy_gates ((8 0))) (selector_values ((q0 (9)) (q1 (3 4 5 6 7))))
    // (witness_values ((0 5) (1 0) (2 1) (3 1) (4 2) (5 3) (6 5) (7 8) (8 5))))";

    let mut plaf: Plaf = Plaf::default();
    plaf.info.p = get_field_p::<Fr>();
    let mut wit: Witness = Witness {
        num_rows: 0,
        columns: vec![],
        witness: vec![],
    };
    match parse(input.as_str()) {
        Ok(sexp) => match sexp {
            Sexp::Atom(_) => unreachable!(),
            Sexp::List(l) => parse_plaf_field_list(l, &mut plaf, &mut wit),
        },
        Err(e) => {
            eprintln!("Failed to parse S-expression: {:?}", e);
        }
    }
    // match "21888242871839275222246405745257275088548364400416034343698204186575808495616".parse::<BigUint>() {
    //     Ok(n) => {
    //         wit.witness[0][3] = Some(n)
    //     },
    //     _ => {}
    // };
    println!("{:?}", wit.witness[0][3]);
    println!("{:#?}", plaf);
    println!("{:#?}", wit);

    let k = ((plaf.info.num_rows as f32).log2().ceil() + (1 as f32)) as u32;
    let plaf_circuit = PlafH2Circuit {
        plaf: plaf.clone(),
        wit: wit,
    };
    unsafe {
        *PARAMS = plaf.clone();
        // println!("{:#?}", &*PARAMS);
    }

    let prover_plaf = MockProver::<Fr>::run(k, &plaf_circuit, Vec::new()).unwrap();

    let result_plaf = prover_plaf.verify();
    println!("result = {:#?}", result_plaf);
    let circuit_cost = CircuitCost::<G2, PlafH2Circuit>::measure(k, &plaf_circuit);
    // println!("cost = {:#?}", circuit_cost);

    let params = fs::gen_srs(k);

    // Generating vkey
    let vk_start_time = Instant::now();
    let vk = keygen_vk(&params, &plaf_circuit).unwrap();
    let vk_time = vk_start_time.elapsed();

    // Generating pkey
    let pk_start_time = Instant::now();
    let pk = keygen_pk(&params, vk, &plaf_circuit).unwrap();
    let pk_time = pk_start_time.elapsed();

    // Creating the proof
    let proof_start_time = Instant::now();
    let proof = gen_proof(&params, &pk, plaf_circuit);
    let proof_time = proof_start_time.elapsed();
    let proof_size = proof.len();
    
    // Verifying
    let verify_start_time = Instant::now();
    check_proof(&params, pk.get_vk(), &proof, true);
    let verify_time = verify_start_time.elapsed();
    
    let cost = Cost {
        mockprover_verified: true,
        circuit_cost: circuit_cost,
        pk_time: pk_time.as_secs_f64(),
        vk_time: vk_time.as_secs_f64(),
        proof_time: proof_time.as_secs_f64(),
        proof_size: proof_size,
        verify_time: verify_time.as_secs_f64(),
    };
    
    println!("{:#?}", cost);
}
