use std::{
    env::var,
    fs::{self, File},
    io::{BufReader, BufWriter},
};

use halo2_proofs::{
    halo2curves::{
        bn256::{Bn256, G1Affine},
        CurveAffine,
    },
    poly::{
        commitment::{Params, ParamsProver},
        kzg::commitment::ParamsKZG,
    },
};
use rand_chacha::{rand_core::SeedableRng, ChaCha20Rng};

/// Reads the srs from a file found in `./params/kzg_bn254_{k}.srs` or `{dir}/kzg_bn254_{k}.srs` if `PARAMS_DIR` env var is specified.
/// * `k`: degree that expresses the size of circuit (i.e., 2^<sup>k</sup> is the number of rows in the circuit)
pub fn read_params(k: u32) -> ParamsKZG<Bn256> {
    let dir = var("PARAMS_DIR").unwrap_or_else(|_| "./params".to_string());
    ParamsKZG::<Bn256>::read(&mut BufReader::new(
        File::open(format!("{dir}/kzg_bn254_{k}.srs").as_str())
            .expect("Params file does not exist"),
    ))
    .unwrap()
}

/// Attempts to read the srs from a file found in `./params/kzg_bn254_{k}.srs` or `{dir}/kzg_bn254_{k}.srs` if `PARAMS_DIR` env var is specified, creates a file it if it does not exist.
/// * `k`: degree that expresses the size of circuit (i.e., 2^<sup>k</sup> is the number of rows in the circuit)
/// * `setup`: a function that creates the srs
pub fn read_or_create_srs<'a, C: CurveAffine, P: ParamsProver<'a, C>>(
    k: u32,
    setup: impl Fn(u32) -> P,
) -> P {
    let dir = var("PARAMS_DIR").unwrap_or_else(|_| "./params".to_string());
    let path = format!("{dir}/kzg_bn254_{k}.srs");
    match File::open(path.as_str()) {
        Ok(f) => {
            #[cfg(feature = "display")]
            println!("read params from {path}");
            let mut reader = BufReader::new(f);
            P::read(&mut reader).unwrap()
        }
        Err(_) => {
            #[cfg(feature = "display")]
            println!("creating params for {k}");
            fs::create_dir_all(dir).unwrap();
            let params = setup(k);
            params
                .write(&mut BufWriter::new(File::create(path).unwrap()))
                .unwrap();
            params
        }
    }
}

/// Generates the SRS for the KZG scheme and writes it to a file found in "./params/kzg_bn2_{k}.srs` or `{dir}/kzg_bn254_{k}.srs` if `PARAMS_DIR` env var is specified, creates a file it if it does not exist"
/// * `k`: degree that expresses the size of circuit (i.e., 2^<sup>k</sup> is the number of rows in the circuit)
pub fn gen_srs(k: u32) -> ParamsKZG<Bn256> {
    read_or_create_srs::<G1Affine, _>(k, |k| {
        ParamsKZG::<Bn256>::setup(k, ChaCha20Rng::from_seed(Default::default()))
    })
}
