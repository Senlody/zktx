use bellman::groth16::*;
use pairing::*;
use pairing::bls12_381::{Fr, FrRepr, Bls12};
use bellman::*;
use rand::thread_rng;

use jubjub::*;

use common_verify::*;

use std::fs::File;
use std::path::Path;

struct RangeCircuit {
    //upper bound
    up: Assignment<Fr>,
    //value
    va: Assignment<Fr>,
    //lower bound
    low: Assignment<Fr>,
}

impl RangeCircuit{
    fn blank() -> RangeCircuit {
        RangeCircuit {
            up: Assignment::unknown(),
            va: Assignment::unknown(),
            low: Assignment::unknown()
        }
    }

    fn new(
        up: Fr,
        va: Fr,
        low: Fr
    ) -> RangeCircuit {
        RangeCircuit {
            up: Assignment::known(up),
            va: Assignment::known(va),
            low: Assignment::known(low)
        }
    }
}

struct RangeCircuitInput {
    //upper bound
    up: Num<Bls12>,
    //lower bound
    low: Num<Bls12>,
}

impl<'a> Input<Bls12> for RangeCircuitInput {
    fn synthesize<CS: PublicConstraintSystem<Bls12>>(self, cs: &mut CS) -> Result<(), Error> {
        let up_input = cs.alloc_input(|| Ok(*self.up.getvalue().get()?))?;
        let low_input = cs.alloc_input(|| Ok(*self.low.getvalue().get()?))?;

        cs.enforce(
            LinearCombination::zero() + self.up.getvar(),
            LinearCombination::zero() + CS::one(),
            LinearCombination::zero() + up_input,
        );
        cs.enforce(
            LinearCombination::zero() + self.low.getvar(),
            LinearCombination::zero() + CS::one(),
            LinearCombination::zero() + low_input,
        );

        Ok(())
    }
}

impl<'a> Circuit<Bls12> for RangeCircuit {
    type InputMap = RangeCircuitInput;

    fn synthesize<CS: ConstraintSystem<Bls12>>(self, cs: &mut CS) -> Result<Self::InputMap, Error> {
        let up_num = Num::new(cs, self.up)?;
        let up = up_num.unpack_sized(cs,256)?;
        let low_num = Num::new(cs, self.low)?;
        let low = low_num.unpack_sized(cs,256)?;

        let va_num = Num::new(cs, self.va)?;
        let va = va_num.unpack_sized(cs,256)?;

        let Mp = Num::new(cs,Assignment::known(Fr::from_repr(FrRepr::from_serial([0, 0, 1, 0])).unwrap()))?.unpack_sized(cs,256)?;
        let mut Mm = Fr::from_repr(FrRepr::from_serial([0, 0, 1, 0])).unwrap();
        Mm.negate();
        let Mm = Num::new(cs,Assignment::known(Mm))?.unpack_sized(cs,256)?;

        assert_nonless_with_minus(&up,&va,&Mp,&Mm,cs)?;
        assert_nonless_with_minus(&va,&low,&Mp,&Mm,cs)?;

        Ok(RangeCircuitInput {up:up_num,low:low_num})
    }
}

pub fn range_info(
    up: ([u64; 2],bool),
    va: ([u64; 2],bool),
    low: ([u64; 2],bool)
) -> Result<
    (([u64; 6], [u64; 6], bool),
      (([u64; 6], [u64; 6]), ([u64; 6], [u64; 6]), bool),
      ([u64; 6], [u64; 6], bool)),
    Error>
{
    let rng = &mut thread_rng();
    let up = {
        let mut res = Fr::from_repr(FrRepr::from_serial([(up.0)[0], (up.0)[1], 0, 0])).unwrap();
        if !up.1 {res.negate();}
        res
    };
    let va = {
        let mut res = Fr::from_repr(FrRepr::from_serial([(va.0)[0], (va.0)[1], 0, 0])).unwrap();
        if !va.1 {res.negate();}
        res
    };
    let low = {
        let mut res = Fr::from_repr(FrRepr::from_serial([(low.0)[0], (low.0)[1], 0, 0])).unwrap();
        if !low.1 {res.negate();}
        res
    };
    let proof = create_random_proof::<Bls12, _, _, _>(
        RangeCircuit::new(
            up,
            va,
            low
        ),
        range_param()?,
        rng,
    )?.serial();
    Ok(proof)
}

pub fn range_verify(
    up: ([u64; 2],bool),
    low: ([u64; 2],bool),
    proof: (([u64; 6], [u64; 6], bool),
            (([u64; 6], [u64; 6]), ([u64; 6], [u64; 6]), bool),
            ([u64; 6], [u64; 6], bool)),
) -> Result<bool, Error> {
    verify_proof(&range_vk()?, &Proof::from_serial(proof), |cs| {
        let up = {
            let mut res = Fr::from_repr(FrRepr::from_serial([(up.0)[0], (up.0)[1], 0, 0])).unwrap();
            if !up.1 {res.negate();}
            res
        };
        let low = {
            let mut res = Fr::from_repr(FrRepr::from_serial([(low.0)[0], (low.0)[1], 0, 0])).unwrap();
            if !low.1 {res.negate();}
            res
        };
        Ok(RangeCircuitInput {
            up: Num::new(cs, Assignment::known(up))?,
            low: Num::new(cs, Assignment::known(low))?
        })
    })
}

pub fn ensure_range_param() -> Result<(), Error> {
    if !Path::new(PARAMPATH).exists() {
        use std::fs::create_dir;
        create_dir(Path::new(PARAMPATH)).unwrap();
    }
    if !Path::new(RANGEPARAMPATH).exists() {
        println!("Creating the parameters");
        let rng = &mut thread_rng();
        let params = generate_random_parameters::<Bls12, _, _>(
            RangeCircuit::blank(),
            rng,
        )?;
        params
            .write(&mut File::create(RANGEPARAMPATH).unwrap())
            .unwrap();
        println!("Just wrote the parameters to disk!");
    }
    Ok(())
}

fn range_param() -> Result<ProverStream, Error> {
    ensure_range_param()?;
    let params = ProverStream::new(RANGEPARAMPATH).unwrap();
    Ok(params)
}

fn range_vk() -> Result<(PreparedVerifyingKey<Bls12>), Error> {
    ensure_range_param()?;
    let mut params = ProverStream::new(RANGEPARAMPATH)?;
    let vk2 = params.get_vk(3)?;
    let vk = prepare_verifying_key(&vk2);
    Ok(vk)
}
