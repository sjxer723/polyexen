use core::num;
use std::{env, fs::read_to_string, hash::Hash, iter::Product, str::FromStr, time::{Duration, Instant}};

use nom::Offset;
use polyexen::expr;
use rand_chacha::rand_core::le;
use regex::Regex;

use ark_std::{end_timer, perf_trace::TimerInfo, start_timer, Zero};
use halo2_proofs::{
    dev::{cost::CircuitCost, metadata::Column, MockProver},
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


fn parse_sexp_to_column_offset(s: &Sexp, num_of_fixed: usize, m: &mut HashMap<String, usize>) -> (expr::Column, usize) {
    if let Sexp::List(l) = s {
        let offset_atom =  parse_sexp_atom(&l[1]);
        let offset = parse_atom_i(&offset_atom);
        let mut fixed_column_str = String::from("");
        
        return match l[0].clone() {
            Sexp::Atom(_) => 
                (expr::Column { kind: ColumnKind::Witness, index: 0}, offset as usize),
            Sexp::List(l) => {
                fixed_column_str =  parse_atom_string(&parse_sexp_atom(&l[1]));
                (expr::Column { kind: ColumnKind::Fixed, 
                    index: m.get(&fixed_column_str).unwrap().clone()}, offset as usize)
            } 
        }
    }   
    (expr::Column {kind: ColumnKind::Witness, index: 0}, 0)
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
    } else if t == "Ref" {
        // let rotation = parse_atom_i(&parse_sexp_atom(&ops[1]));
        // TODO: constant cell in polynomial gates
        let column_offset = parse_sexp_to_column_offset(&ops[1], 0, m);

        return Expr::Var(Var::Query(ColumnQuery {
            column: column_offset.0,
            rotation: column_offset.1 as i32,
        }));
    } else if t == "Const" {
        let mut num = BigUint::zero();
        let s = parse_atom_string(&parse_sexp_atom(&ops[1]));
        
        if let Ok(n) = BigUint::from_str(&s.as_str()[1..]){
            num = n;
        }
        return Expr::Const(num);
    }

    Expr::Const(BigUint::zero())
}


// l is a list of sexp and contains the following two kind of sexp
// * ((Witness row_index) value)
// * ((Fixed column_str) row_index) value)
fn parse_values(l: &Vec<Sexp>, row_num: usize, map: &mut HashMap<String, usize>)
    -> (Vec<Option<BigUint>>, Vec<Vec<Option<BigUint>>>) {
    let mut witness_values: Vec<Option<BigUint>> = vec![None; row_num];
    let mut fixed_columns_values: Vec<Vec<Option<BigUint>>> = vec![];    
    let mut column_name_with_idx;
    let mut val = None;
    let mut fixed_column_name;
    let mut row_idx = 0;

    for _ in map.keys() {
        fixed_columns_values.insert(0, vec![None; row_num]);
    }

    for s in l {
        match s {
            Sexp::Atom(_) => unreachable!(),
            Sexp::List(elements) => {
                if let Ok(n) = BigUint::from_str(
                    &parse_atom_string(&parse_sexp_atom(&elements[1])).as_str()[1..]) {
                    val = Some(n);
                }
                column_name_with_idx = parse_sexp_list(&elements[0]);
                match column_name_with_idx[0].clone() {
                    // fixed column
                    Sexp::List(fixed_with_name) => {
                        fixed_column_name = parse_atom_string(
                            &parse_sexp_atom(&fixed_with_name[1]));
                        row_idx = parse_atom_i(
                            &parse_sexp_atom(&column_name_with_idx[1])) as usize;
                        fixed_columns_values[map.get(&fixed_column_name).unwrap().clone()][row_idx] = 
                            val.clone();
                    },
                    // witness column
                    Sexp::Atom(_) => {
                        // println!("{:#?}", witness_values);
                        witness_values[parse_atom_i(
                            &parse_sexp_atom(&column_name_with_idx[1])) as usize] = val.clone();
                    },
                }
            }
        }
    }
    return (witness_values, fixed_columns_values)

}

// l is a list of sexp and contains the following two kind of sexp
// * ((Witness row_index) value)
// * ((Fixed column_str) row_index) value)
fn get_num_of_row(l: &Vec<Sexp>)
    -> usize {
    let mut length = 0;
    let mut column_name_with_idx;
    
    for s in l {
        match s {
            Sexp::Atom(_) => unreachable!(),
            Sexp::List(elements) => {
                column_name_with_idx = parse_sexp_list(&elements[0]);
                match column_name_with_idx[0].clone() {
                    // fixed column
                    Sexp::List(_) => {},
                    // witness column
                    Sexp::Atom(_) => {length +=1;},
                }
            }
        }
    }
    return length;
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

    let mut fixed_column_sexp = Sexp::Atom(Atom::S(String::from("")));
    let mut columns_fixed = vec![];
    let mut wit_wit_offsets = vec![];
    let mut wit_const_offsets = vec![];
    // let mut s_locs = vec![];
    // let mut locs = vec![];
    // let mut fixed_values_loc = vec![];
    // let mut fixed_value_col = vec![];
    let mut witness_value_col = vec![Some(BigUint::zero()); plaf.info.num_rows];
    let mut fixed_values = vec![];
    let mut row_idx = 0;
    let mut witness_values = vec![];
    let mut polys = vec![];
    let mut copy_gate_column_0 = expr::Column {kind: ColumnKind::Witness, index: 0};
    let mut copy_gate_column_1 = expr::Column {kind: ColumnKind::Witness, index: 0};
    let mut copy_offset0 = 0;
    let mut copy_offset1 = 0;
    let mut constants = vec![Some(BigUint::zero()); plaf.info.num_rows];


    println!("{:#?}", s.as_str());
    match s.as_str() {
        "num_rows" => match &kvs[1] {
            Sexp::Atom(a1) => plaf.info.num_rows = parse_atom_i(&a1) as usize,
            _ => {}
        },
        "fixed_columns" => match &kvs[1] {
            Sexp::List(l) => {
                for (index, fixed_column) in l.iter().enumerate() {
                    fixed_column_sexp = parse_sexp_list(fixed_column)[1].clone();
                    match fixed_column_sexp {
                        Sexp::Atom(_selector) => {
                            selector_index.insert(parse_atom_string(&_selector), index);
                            columns_fixed.push(ColumnFixed::new(parse_atom_string(&_selector)))
                        }
                        _ => {}
                    }
                }
                // columns_fixed.push(ColumnFixed::new(String::from("Constant")))
            }
            _ => {}
        },
        "polynomial_gates" => match &kvs[1] {
            Sexp::List(gates) => {
                for (_idx, _gate) in gates.iter().enumerate() {
                    // if (_idx >= 1) {
                    //     break;
                    // }
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
                    (copy_gate_column_0, copy_offset0) = parse_sexp_to_column_offset(&parse_sexp_list(cp)[0], plaf.columns.fixed.len(), selector_index);
                    (copy_gate_column_1, copy_offset1) = parse_sexp_to_column_offset(&parse_sexp_list(cp)[1], plaf.columns.fixed.len(), selector_index);
                    
                    if copy_gate_column_0.kind == expr::ColumnKind::Witness && copy_gate_column_1.kind == expr::ColumnKind::Witness {
                        wit_wit_offsets.push((copy_offset0, copy_offset1));
                    } else {
                        wit_const_offsets.push((copy_offset0, copy_offset1));
                    }
                }
            }
            _ => {}
        },
        // "selector_values" => match &kvs[1] {
        //     Sexp::List(svs) => {
        //         for _sv in svs {
        //             s_locs = parse_sexp_list(_sv);
        //             locs = vec![];
        //             for _v in parse_sexp_list(&s_locs[1]) {
        //                 locs.push(parse_atom_i(&parse_sexp_atom(&_v)) as u64);
        //             }
        //             fixed_values_loc.push(locs.clone())
        //         }
        //     }
        //     _ => {}
        // },
        "values" => {
            match &kvs[1] {
                Sexp::List(wvs) => {
                    (witness_values, fixed_values) = parse_values(wvs, plaf.info.num_rows, selector_index);
                }
                _ => {}
            }
        }
        // "constants" => {
        //     match &kvs[1] {
        //         Sexp::List(wvs) => {
        //             for (i,_wv) in wvs.iter().enumerate() {
        //                 if let Ok(n) = BigUint::from_str(
        //                     &parse_atom_string(
        //                         &parse_sexp_atom(&parse_sexp_list(_wv)[1])
        //                     ).as_str()[1..]) {
        //                     constants[i] = Some(n)
        //                 }
        //             }
        //         }
        //         _ => {}
        //     }
        // }

        _ => println!("The {:#?} is something else", s.as_str()),
    }

    // Update plaf
    match s.as_str() {
        "polynomial_gates" => plaf.polys = polys,
        "fixed_columns" => {
            plaf.columns.fixed = columns_fixed;
        }
        "values" => {
            // for loc_col in fixed_values_loc {
            //     fixed_value_col = vec![Some(BigUint::from(0 as u8)); plaf.info.num_rows];
            //     for _loc in loc_col {
            //         fixed_value_col[_loc as usize] = Some(BigUint::from(1 as u8));
            //     }
            //     fixed_values.push(fixed_value_col)
            // }
            plaf.fixed = fixed_values;
            // TODO: support multiple witness columns
            wit.witness = vec![witness_values];
        }
        // "copy_gates" => {
        //     plaf.copys = vec![
        //         CopyC {
        //             columns: (expr::Column {kind: ColumnKind::Witness, index: 0}, expr::Column {kind: ColumnKind::Witness, index: 0}),
        //             offsets: wit_wit_offsets,
        //         },
        //         // CopyC {
        //         //     columns: (expr::Column {kind: ColumnKind::Witness, index: 0}, expr::Column {kind: ColumnKind::Fixed, index: plaf.columns.fixed.len() - 1}),
        //         //     offsets: wit_const_offsets,
        //         // }
        //     ]
        // }
        // "witness_values" => {
        //     wit.witness = witness_values;
        // }
        // "constants" => {
        //     plaf.fixed.push(constants);
        // }
        _ => {}
    }
}


fn set_plaf_num_rows(l: Vec<Sexp>, plaf: &mut Plaf, wit: &mut Witness) {
    let mut length = 0;

    for s in l {
        if let Sexp::List(kvs) = s {
            match &kvs[0] {
                Sexp::Atom(a) => {
                    if parse_atom_string(a) == "values" {
                        length = get_num_of_row(&parse_sexp_list(&kvs[1])) as usize;
                        plaf.info.num_rows = length;
                        wit.num_rows = length;
                    }
                }
                _ => unreachable!(),
            }
        }
    }
}

fn parse_plaf_field_list(l: Vec<Sexp>, plaf: &mut Plaf, wit: &mut Witness) {
    let mut selector_index: HashMap<String, usize> = HashMap::new();
    let mut columns_witness = vec![];

    set_plaf_num_rows(l.clone(), plaf, wit);
    // TODO: only consider single witness column currently
    columns_witness.push(ColumnWitness::new(String::from("w"), 0));
    wit.columns = columns_witness.clone();
    plaf.columns.witness = columns_witness;
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
    // mockprover_verified: bool,
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
    // println!("{:?}", wit.witness[0].len());
    // println!("{:#?}", plaf.polys);
    // for (f_idx, f) in plaf.fixed.iter().enumerate() {
    //     for (i, v) in f.iter().enumerate() {
    //         match v.clone().as_mut() {
    //             Some(v1) => {
    //                 println!("{:#?}: {:#?}: {:#?}", f_idx, i,v.clone().as_mut().unwrap());
    //             }
    //             None => {}
    //         }
    //     }    
    // }
    // println!("{:#?}", plaf.fixed);
    // println!("{:#?}", plaf.copys );

    let k = ((plaf.info.num_rows as f32).log2().ceil() + (1 as f32)) as u32;
    let plaf_circuit = PlafH2Circuit {
        plaf: plaf.clone(),
        wit: wit,
    };
    unsafe {
        *PARAMS = plaf.clone();
        // println!("{:#?}", &*PARAMS);
    }
    // println!("{:#?}", plaf.info.num_rows);
    // println!("{:#?}", plaf.columns.fixed.len());
    // println!("{:#?}", plaf);
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
        // mockprover_verified: true,
        circuit_cost: circuit_cost,
        pk_time: pk_time.as_secs_f64(),
        vk_time: vk_time.as_secs_f64(),
        proof_time: proof_time.as_secs_f64(),
        proof_size: proof_size,
        verify_time: verify_time.as_secs_f64(),
    };
    
    let cost_data = format!("{:#?}", cost);

    let filtered_data: Vec<&str> = cost_data
        .lines()
        .filter(|line| !line.contains("_marker"))
        .collect();

    let filtered_data = filtered_data.join("\n");

    let re = Regex::new(r"[-+]?\d*\.\d+|\d+").unwrap();
    let numbers: Vec<&str> = re.find_iter(&filtered_data).map(|mat| mat.as_str()).collect();

    for num in &numbers {
        if num.contains('.') {
            if let Ok(parsed_num) = num.parse::<f64>() {
                println!("{}", parsed_num);
            }
        } else {
            if let Ok(parsed_num) = num.parse::<i64>() {
                println!("{}", parsed_num);
            }
        }
    }
}
