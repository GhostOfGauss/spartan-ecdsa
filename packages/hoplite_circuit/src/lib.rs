#![allow(non_snake_case)]
mod chips;
mod transcript;

use chips::{
    dotprod::ZKDotProdChip,
    eval_poly::EvalMLPolyChip,
    pedersen_commit::PedersenCommitChip,
    poly_eval_proof::{AssignN, PolyEvalProofChip},
    proof_bullet_reduce::BulletReduceChip,
    proof_log_of_dotprod::ProofLogOfDotProdChip,
    proof_of_eq::ProofOfEqChip,
    proof_of_opening::ZKKnowledgeProofChip,
    proof_of_prod::ProofOfProdChip,
    secq256k1::Secq256k1Chip,
    sumcheck::{AssignZKSumCheckProof, ZKSumCheckChip},
    utils::{Assign, AssignArray},
};
use halo2_base::utils::{modulus, PrimeField};
use halo2_ecc::fields::FieldChip;
use halo2_ecc::{
    ecc::{fixed_base::FixedEcPoint, EccChip},
    fields::fp::{FpConfig, FpStrategy},
};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    plonk,
    plonk::{Circuit, Column, ConstraintSystem, Instance},
};
use hoplite::circuit_vals::{FromCircuitVal, ToCircuitVal};
use hoplite::{
    circuit_vals::{
        CVEqualityProof, CVKnowledgeProof, CVPolyCommitment, CVPolyEvalProof, CVProductProof,
        CVSumCheckProof,
    },
    commitments::{Commitments, MultiCommitGens},
};
use libspartan::{
    group::CompressedGroup,
    transcript::{ProofTranscript, Transcript},
};
use libspartan::{NIZKGens, NIZK};
use num_bigint::BigUint;
use num_traits::{One, Zero};

use secpq_curves::{group::Curve, Secq256k1};
use transcript::HopliteTranscript;

pub type Fp = secpq_curves::Fq;
pub type Fq = secpq_curves::Fp;

pub type FqChip<F> = FpConfig<F, secpq_curves::Fp>;
pub type FpChip<F> = FpConfig<F, secpq_curves::Fq>;

#[derive(Clone, Debug)]
pub struct HopliteCircuitConfig<F: PrimeField> {
    field_config: FpChip<F>,
    /// Public inputs
    instance: Column<Instance>,
    window_bits: usize,
}

/// SpartanNIZK verification circuit
pub struct HopliteCircuit<
    const NUM_INPUTS: usize,
    const NUM_CONSTRAINTS: usize,
    const NUM_CONSTRAINTS_LOG: usize,
    const NUM_VARS: usize,
    const NUM_VARS_LOG: usize,
    const NUM_VARS_LOG_MINUS_ONE: usize,
    const Z_MATRIX_ROWS: usize, // TODO: Is this really part of circuit description? It does influence vk's size
    const Z_MATRIX_ROWS_LOG: usize,
    const Z_MATRIX_COLS: usize,
    const Z_MATRIX_COLS_LOG: usize,
> {
    pub inst: Vec<u8>, // digest of the R1CS instance
    pub input: [Fq; NUM_INPUTS],
    pub comm_vars: CVPolyCommitment<Z_MATRIX_ROWS>,
    pub sc_proof_phase1: CVSumCheckProof<NUM_CONSTRAINTS_LOG, 4>,
    pub claims_phase2: (
        Option<Secq256k1>,
        Option<Secq256k1>,
        Option<Secq256k1>,
        Option<Secq256k1>,
    ),
    pub pok_claims_phase2: (CVKnowledgeProof, CVProductProof),
    pub proof_eq_sc_phase1: CVEqualityProof,
    pub sc_proof_phase2: CVSumCheckProof<NUM_VARS_LOG, 3>,
    pub comm_vars_at_ry: Option<Secq256k1>, // TODO: Why option?
    pub proof_eval_vars_at_ry: CVPolyEvalProof<Z_MATRIX_COLS_LOG>,
    pub proof_eq_sc_phase2: CVEqualityProof,
    pub gens_sc_1: MultiCommitGens,
    pub gens_sc_3: MultiCommitGens,
    pub gens_sc_4: MultiCommitGens,
    pub gens_pc_1: MultiCommitGens,
    pub gens_pc_n: MultiCommitGens,
}

pub struct CircuitParams {
    strategy: FpStrategy,
    degree: u32,
    num_advice: usize,
    num_lookup_advice: usize,
    num_fixed: usize,
    lookup_bits: usize,
    limb_bits: usize,
    num_limbs: usize,
}

impl<
        const NUM_INPUTS: usize,
        const NUM_CONSTRAINTS: usize,
        const NUM_CONSTRAINTS_LOG: usize,
        const NUM_VARS: usize,
        const NUM_VARS_LOG: usize,
        const NUM_VARS_LOG_MINUS_ONE: usize,
        const Z_MATRIX_ROWS: usize,
        const Z_MATRIX_ROWS_LOG: usize,
        const Z_MATRIX_COLS: usize,
        const Z_MATRIX_COLS_LOG: usize,
        // F: PrimeField,
    >
    HopliteCircuit<
        NUM_INPUTS,
        NUM_CONSTRAINTS,
        NUM_CONSTRAINTS_LOG,
        NUM_VARS,
        NUM_VARS_LOG,
        NUM_VARS_LOG_MINUS_ONE,
        Z_MATRIX_ROWS,
        Z_MATRIX_ROWS_LOG,
        Z_MATRIX_COLS,
        Z_MATRIX_COLS_LOG,
    >
{
    /// Construct an instance of the verifier circuit from the verifier data: proof, public input,
    /// commitment generators, and R1CS instance digest.
    pub fn new(proof: NIZK, input: [Fq; NUM_INPUTS], gens: NIZKGens, digest: Vec<u8>) -> Self {
        Self {
            inst: digest,
            input,
            comm_vars: proof.r1cs_sat_proof.comm_vars.to_circuit_val(),
            sc_proof_phase1: proof.r1cs_sat_proof.sc_proof_phase1.to_circuit_val(),
            claims_phase2: (
                Some(proof.r1cs_sat_proof.claims_phase2.0.to_circuit_val()),
                Some(proof.r1cs_sat_proof.claims_phase2.1.to_circuit_val()),
                Some(proof.r1cs_sat_proof.claims_phase2.2.to_circuit_val()),
                Some(proof.r1cs_sat_proof.claims_phase2.3.to_circuit_val()),
            ),
            pok_claims_phase2: (
                proof.r1cs_sat_proof.pok_claims_phase2.0.to_circuit_val(),
                proof.r1cs_sat_proof.pok_claims_phase2.1.to_circuit_val(),
            ),
            proof_eq_sc_phase1: proof.r1cs_sat_proof.proof_eq_sc_phase1.to_circuit_val(),
            sc_proof_phase2: proof.r1cs_sat_proof.sc_proof_phase2.to_circuit_val(),
            comm_vars_at_ry: Some(proof.r1cs_sat_proof.comm_vars_at_ry.to_circuit_val()),
            proof_eval_vars_at_ry: proof.r1cs_sat_proof.proof_eval_vars_at_ry.to_circuit_val(),
            proof_eq_sc_phase2: proof.r1cs_sat_proof.proof_eq_sc_phase2.to_circuit_val(),
            gens_sc_1: gens.gens_r1cs_sat.gens_sc.gens_1.into(),
            gens_sc_3: gens.gens_r1cs_sat.gens_sc.gens_3.into(),
            gens_sc_4: gens.gens_r1cs_sat.gens_sc.gens_4.into(),
            gens_pc_1: gens.gens_r1cs_sat.gens_pc.gens.gens_1.into(),
            gens_pc_n: gens.gens_r1cs_sat.gens_pc.gens.gens_n.into(),
        }
    }
}

impl<
        const NUM_INPUTS: usize,
        const NUM_CONSTRAINTS: usize,
        const NUM_CONSTRAINTS_LOG: usize,
        const NUM_VARS: usize,
        const NUM_VARS_LOG: usize,
        const NUM_VARS_LOG_MINUS_ONE: usize,
        const Z_MATRIX_ROWS: usize,
        const Z_MATRIX_ROWS_LOG: usize,
        const Z_MATRIX_COLS: usize,
        const Z_MATRIX_COLS_LOG: usize,
        F: PrimeField,
    > Circuit<F>
    for HopliteCircuit<
        NUM_INPUTS,
        NUM_CONSTRAINTS,
        NUM_CONSTRAINTS_LOG,
        NUM_VARS,
        NUM_VARS_LOG,
        NUM_VARS_LOG_MINUS_ONE,
        Z_MATRIX_ROWS,
        Z_MATRIX_ROWS_LOG,
        Z_MATRIX_COLS,
        Z_MATRIX_COLS_LOG,
    >
{
    type Config = HopliteCircuitConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let params = CircuitParams {
            strategy: FpStrategy::Simple,
            degree: 21,
            num_advice: 120, // TODO: How many is enough? at least 30
            num_lookup_advice: 6,
            num_fixed: 1,
            lookup_bits: 17,
            limb_bits: 88,
            num_limbs: 3,
        };

        let field_config = FpChip::<F>::configure(
            meta,
            params.strategy,
            &[params.num_advice],
            &[params.num_lookup_advice],
            params.num_fixed,
            params.lookup_bits,
            params.limb_bits,
            params.num_limbs,
            modulus::<Fp>(),
            0,
            params.degree as usize,
        );

        let instance = meta.instance_column();

        meta.enable_equality(instance);

        HopliteCircuitConfig {
            instance,
            field_config,
            window_bits: 4,
        }
    }

    fn without_witnesses(&self) -> Self {
        HopliteCircuit::<
            NUM_INPUTS,
            NUM_CONSTRAINTS,
            NUM_CONSTRAINTS_LOG,
            NUM_VARS,
            NUM_VARS_LOG,
            NUM_VARS_LOG_MINUS_ONE,
            Z_MATRIX_ROWS,
            Z_MATRIX_ROWS_LOG,
            Z_MATRIX_COLS,
            Z_MATRIX_COLS_LOG,
        > {
            comm_vars: CVPolyCommitment::<Z_MATRIX_ROWS>::default(),
            inst: vec![],
            input: [Fq::zero(); NUM_INPUTS],
            sc_proof_phase1: CVSumCheckProof::<NUM_CONSTRAINTS_LOG, 4>::default(),
            claims_phase2: (None, None, None, None),
            pok_claims_phase2: (CVKnowledgeProof::default(), CVProductProof::default()),
            proof_eq_sc_phase1: CVEqualityProof::default(),
            sc_proof_phase2: CVSumCheckProof::<NUM_VARS_LOG, 3>::default(),
            comm_vars_at_ry: None,
            proof_eval_vars_at_ry: CVPolyEvalProof::<Z_MATRIX_COLS_LOG>::default(),
            proof_eq_sc_phase2: CVEqualityProof::default(),
            gens_sc_1: MultiCommitGens::default(),
            gens_sc_3: MultiCommitGens::default(),
            gens_sc_4: MultiCommitGens::default(),
            gens_pc_1: MultiCommitGens::default(),
            gens_pc_n: MultiCommitGens::default(),
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), plonk::Error> {
        // Scalar mult
        let n_rounds = 1;
        let _ = config.instance; // just to kill unused warning

        let fp_chip = config.field_config;
        fp_chip.range.load_lookup_table(&mut layouter)?;

        // Actually perform the calculation

        let limb_bits = fp_chip.limb_bits;
        let num_limbs = fp_chip.num_limbs;
        let _num_fixed = fp_chip.range.gate.constants.len();
        let _lookup_bits = fp_chip.range.lookup_bits;
        let _num_advice = fp_chip.range.gate.num_advice;

        // We can construct the fp_chip from the config of the fp_chip
        // (fp_chip can use the same columns as the fp_chip)
        let fq_chip =
            FqChip::<F>::construct(fp_chip.range.clone(), limb_bits, num_limbs, modulus::<Fq>());

        let ecc_chip = EccChip::construct(fp_chip.clone());
        let secq_chip = Secq256k1Chip::construct(ecc_chip.clone(), fq_chip.clone());

        let pedersen_chip = PedersenCommitChip::construct(ecc_chip.clone(), fp_chip.clone());
        let phase_1_zkdotprod_chip: ZKDotProdChip<4, F> =
            ZKDotProdChip::construct(ecc_chip.clone(), fq_chip.clone(), pedersen_chip.clone());

        let phase_1_zksumcheck_chip = ZKSumCheckChip::construct(
            ecc_chip.clone(),
            fp_chip.clone(),
            fq_chip.clone(),
            pedersen_chip.clone(),
            phase_1_zkdotprod_chip,
        );

        let knowledge_proof_chip = ZKKnowledgeProofChip::construct(
            ecc_chip.clone(),
            fp_chip.clone(),
            fq_chip.clone(),
            pedersen_chip.clone(),
            config.window_bits,
        );

        let proof_of_prod_chip = ProofOfProdChip::construct(
            secq_chip.clone(),
            pedersen_chip.clone(),
            config.window_bits,
        );

        let proof_of_eq_chip = ProofOfEqChip::construct(secq_chip.clone(), config.window_bits);

        let eval_poly_chip =
            EvalMLPolyChip::<F, NUM_VARS_LOG_MINUS_ONE>::construct(fp_chip.clone());

        //  let mut results = Vec::new();

        layouter.assign_region(
            || "",
            |region| {
                let mut ctx = fp_chip.new_context(region);

                let mut transcript = Transcript::new(b"test_verify");

                transcript.append_protocol_name(b"Spartan NIZK proof");
                transcript.append_message(b"R1CSInstanceDigest", &self.inst);

                transcript.append_protocol_name(b"R1CS proof");

                // Append input to the transcript
                transcript.append_message(b"input", b"begin_append_vector");
                for item in &self.input {
                    transcript.append_message(b"input", &item.to_bytes());
                }
                transcript.append_message(b"input", b"end_append_vector");

                // Append poly commitment to the transcript
                transcript.append_message(b"poly_commitment", b"poly_commitment_begin");
                for comm_var in self.comm_vars.C {
                    transcript.append_point(
                        b"poly_commitment_share",
                        &CompressedGroup::from_circuit_val(&comm_var.unwrap()),
                    );
                }
                transcript.append_message(b"poly_commitment", b"poly_commitment_end");

                let phase1_expected_sum = Fq::zero().commit(&Fq::zero(), &self.gens_sc_1); // So 0?

                let phase1_expected_sum =
                    FixedEcPoint::from_curve(phase1_expected_sum.to_affine(), num_limbs, limb_bits);

                let phase1_expected_sum = FixedEcPoint::assign(
                    phase1_expected_sum,
                    &fp_chip,
                    &mut ctx,
                    fp_chip.native_modulus(),
                );

                // TODO: Unused
                let _tau: Vec<Fq> = transcript
                    .challenge_vector(b"challenge_tau", n_rounds)
                    .iter()
                    .map(|tau_i| tau_i.to_circuit_val())
                    .collect();

                let phase1_sc_proof = self.sc_proof_phase1.assign(&mut ctx, &secq_chip);
                let (comm_claim_post_phase1, _rx) = phase_1_zksumcheck_chip.verify(
                    &mut ctx,
                    &phase1_sc_proof,
                    &self.gens_sc_4,
                    &self.gens_sc_1,
                    phase1_expected_sum,
                    true,
                    &mut transcript,
                );

                // Verify Az * Bz = Cz
                let (comm_Az_claim, comm_Bz_claim, comm_Cz_claim, comm_prod_Az_Bz_claims) =
                    &self.claims_phase2;

                let (pok_Cz_claim, proof_prod) = &self.pok_claims_phase2;
                let pok_Cz_claim = pok_Cz_claim.assign(&mut ctx, &secq_chip);
                let proof_prod = proof_prod.assign(&mut ctx, &secq_chip);
                let comm_Cz_claim = comm_Cz_claim.assign(&mut ctx, &secq_chip);

                // Assign points
                let comm_Az_claim = comm_Az_claim.assign(&mut ctx, &secq_chip);
                let comm_Bz_claim = comm_Bz_claim.assign(&mut ctx, &secq_chip);

                let comm_prod_Az_Bz_claims = comm_prod_Az_Bz_claims.assign(&mut ctx, &secq_chip);

                knowledge_proof_chip.verify(
                    // TODO: Why only an opening proof for C but not A, B?
                    &mut ctx,
                    &comm_Cz_claim,
                    pok_Cz_claim,
                    &self.gens_sc_1,
                    &mut transcript,
                );

                proof_of_prod_chip.verify(
                    &mut ctx,
                    &comm_Az_claim,
                    &comm_Bz_claim,
                    &comm_Cz_claim,
                    proof_prod,
                    &self.gens_sc_1,
                    &mut transcript,
                );
                transcript.append_circuit_point(b"comm_Az_claim", comm_Az_claim.clone());
                transcript.append_circuit_point(b"comm_Bz_claim", comm_Bz_claim.clone());
                transcript.append_circuit_point(b"comm_Cz_claim", comm_Cz_claim.clone());
                transcript.append_circuit_point(
                    b"comm_prod_Az_Bz_claims",
                    comm_prod_Az_Bz_claims.clone(),
                );

                // eq_eval
                let expected_claim_post_phase1 =
                    ecc_chip.sub_unequal(&mut ctx, &comm_prod_Az_Bz_claims, &comm_Cz_claim, true);
                // eq_tau_rx;

                let proof_eq_sc_phase1 = self.proof_eq_sc_phase1.assign(&mut ctx, &secq_chip);

                proof_of_eq_chip.verify(
                    &mut ctx,
                    &expected_claim_post_phase1,
                    &comm_claim_post_phase1,
                    proof_eq_sc_phase1,
                    &self.gens_sc_1,
                    &mut transcript,
                );

                let r_A = transcript.challenge_scalar(b"challenege_Az");
                let r_B = transcript.challenge_scalar(b"challenege_Bz");
                let r_C = transcript.challenge_scalar(b"challenege_Cz");

                let r_A = Some(r_A.to_circuit_val()).assign(&mut ctx, &secq_chip);
                let r_B = Some(r_B.to_circuit_val()).assign(&mut ctx, &secq_chip);
                let r_C = Some(r_C.to_circuit_val()).assign(&mut ctx, &secq_chip);

                // M(r_y) = r_A * comm_Az_claim + r_B * comm_Bz_claim + r_C * comm_Cz_claim;
                let r_A_comm_Az = ecc_chip.scalar_mult(
                    &mut ctx,
                    &comm_Az_claim,
                    &r_A.truncation.limbs,
                    limb_bits,
                    config.window_bits,
                );
                let r_B_comm_Bz = ecc_chip.scalar_mult(
                    &mut ctx,
                    &comm_Bz_claim,
                    &r_B.truncation.limbs,
                    limb_bits,
                    config.window_bits,
                );
                let r_C_comm_Cz = ecc_chip.scalar_mult(
                    &mut ctx,
                    &comm_Cz_claim,
                    &r_C.truncation.limbs,
                    limb_bits,
                    config.window_bits,
                );

                let r_AB_comm_ABz =
                    ecc_chip.add_unequal(&mut ctx, &r_A_comm_Az, &r_B_comm_Bz, true);
                let comm_claim_phase2 =
                    ecc_chip.add_unequal(&mut ctx, &r_AB_comm_ABz, &r_C_comm_Cz, true);

                let phase_2_zkdotprod_chip: ZKDotProdChip<3, F> = ZKDotProdChip::construct(
                    ecc_chip.clone(),
                    fq_chip.clone(),
                    pedersen_chip.clone(),
                );

                let phase_2_zksumcheck_chip = ZKSumCheckChip::construct(
                    ecc_chip.clone(),
                    fp_chip.clone(),
                    fq_chip.clone(),
                    pedersen_chip.clone(),
                    phase_2_zkdotprod_chip,
                );

                let sc_proof_phase2 = self.sc_proof_phase2.assign(&mut ctx, &secq_chip);

                let (_comm_claim_post_phase2, ry) = phase_2_zksumcheck_chip.verify(
                    &mut ctx,
                    &sc_proof_phase2,
                    &self.gens_sc_3,
                    &self.gens_sc_1,
                    comm_claim_phase2,
                    false,
                    &mut transcript,
                );

                let comm_vars = self.comm_vars.C.assign(&mut ctx, &secq_chip);
                let bullet_reduce_chip = BulletReduceChip::construct(
                    secq_chip.clone(),
                    pedersen_chip.clone(),
                    config.window_bits,
                );

                let proof_of_log_dotprod_chip = ProofLogOfDotProdChip::construct(
                    secq_chip.clone(),
                    bullet_reduce_chip,
                    config.window_bits,
                );

                let eval_rows_chip =
                    EvalMLPolyChip::<_, Z_MATRIX_ROWS_LOG>::construct(fp_chip.clone());
                let eval_cols_chip =
                    EvalMLPolyChip::<_, Z_MATRIX_COLS_LOG>::construct(fp_chip.clone());

                let poly_eval_proof_chip = PolyEvalProofChip::<
                    _,
                    Z_MATRIX_ROWS,
                    Z_MATRIX_ROWS_LOG,
                    Z_MATRIX_COLS,
                    Z_MATRIX_COLS_LOG,
                >::construct(
                    secq_chip.clone(),
                    eval_rows_chip,
                    eval_cols_chip,
                    proof_of_log_dotprod_chip,
                    config.window_bits,
                );

                let poly_eval_proof = self.proof_eval_vars_at_ry.assign(&mut ctx, &secq_chip);
                let comm_vars_at_ry = self.comm_vars_at_ry.assign(&mut ctx, &secq_chip);

                poly_eval_proof_chip.verify(
                    &mut ctx,
                    &ry[1..],
                    &comm_vars_at_ry,
                    comm_vars,
                    poly_eval_proof,
                    &self.gens_pc_1,
                    &self.gens_pc_n,
                    &mut transcript,
                );

                // Interpolate the input as a multilinear polynomial and evaluate at ry[1..]
                let mut input_with_one = vec![fp_chip.load_constant(&mut ctx, BigUint::one())];
                for i in 1..self.input.len() {
                    input_with_one.push(fp_chip.load_constant(
                        &mut ctx,
                        BigUint::from_bytes_le(&self.input[i].to_bytes()),
                    ));
                }
                println!("Length of ry is {:?}", ry.len());
                println!("Size of eval_poly_chip is {NUM_VARS_LOG_MINUS_ONE}");
                let poly_input_eval = eval_poly_chip.interpolate(
                    &mut ctx,
                    &input_with_one,
                    ry[1..].try_into().unwrap(),
                );
                // Form "blinded" commitment to input -- note blinding factor is 0.
                let blinder = fp_chip.load_constant(&mut ctx, BigUint::zero());
                pedersen_chip.commit(&mut ctx, &poly_input_eval, &blinder, &self.gens_pc_1);

                // TODO: TBD

                Ok(())
            },
        )?;

        Ok(())
    }
}

#[cfg(test)]
#[allow(non_camel_case_types)]
mod tests {
    use super::*;
    use ark_std::{end_timer, start_timer};
    use circuit_reader::load_as_spartan_inst;
    use halo2_base::utils::{decompose_biguint, fs::gen_srs};
    use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};
    use halo2_proofs::{
        halo2curves::bn256::{Bn256, G1Affine},
        plonk::{create_proof, keygen_pk, keygen_vk, verify_proof},
        poly::{
            commitment::ParamsProver,
            kzg::{
                commitment::{KZGCommitmentScheme, ParamsVerifierKZG},
                multiopen::{ProverSHPLONK, VerifierSHPLONK},
                strategy::SingleStrategy,
            },
        },
        transcript::{
            Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
        },
    };
    use hoplite::circuit_vals::ToCircuitVal;
    use libspartan::{
        r1csinstance::R1CSInstance, transcript::Transcript, InputsAssignment, Instance, NIZKGens,
        VarsAssignment, NIZK,
    };
    use rand_core::OsRng;
    use secpq_curves::group::cofactor::CofactorCurveAffine;
    use secpq_curves::Secq256k1Affine;
    use serde::de::DeserializeOwned;
    use serde::Serialize;
    use std::fs::File;
    use std::io::{Read, Write};
    use std::path::PathBuf;

    /// Randomly samples an R1CS instance, produces a witness, generates a NIZK proof.
    /// Returns instance, proof, public inputs, and commitment generators.
    fn sample_nizk_proof(
        num_constraints: usize,
        num_vars: usize,
        num_inputs: usize,
    ) -> (Instance, NIZK, InputsAssignment, NIZKGens) {
        let (instance, witness, inputs) =
            R1CSInstance::produce_synthetic_r1cs(num_constraints, num_vars, num_inputs);
        let digest = instance.get_digest();
        let instance = Instance {
            inst: instance,
            digest,
        };
        let assignment_inputs = InputsAssignment { assignment: inputs };
        let assignment_vars = VarsAssignment {
            assignment: witness,
        };
        // let res = instance.is_sat(&assignment_vars, &assignment_inputs);
        // assert!(res.unwrap(), "should be satisfied");
        let gens = NIZKGens::new(num_constraints, num_vars, num_inputs);
        let mut prover_transcript = Transcript::new(b"test_verify");
        let proof = NIZK::prove(
            &instance,
            assignment_vars,
            &assignment_inputs,
            &gens,
            &mut prover_transcript,
        );
        (instance, proof, assignment_inputs, gens)
    }

    // cargo test  --release --package hoplite_circuit --lib --all-features -- tests::generate_small_proof_files --exact --nocapture
    #[test]
    fn generate_small_proof_files() {
        const NUM_INPUTS: usize = 2;
        const NUM_CONSTRAINTS: usize = 16;
        const NUM_CONSTRAINTS_LOG: usize = 4;
        const NUM_VARS: usize = 16;
        /// This is actually one more because we pad the witness to a higher power of two
        const NUM_VARS_LOG: usize = 5;
        const NUM_VARS_LOG_MINUS_ONE: usize = 4;
        const Z_MATRIX_ROWS: usize = 4;
        const Z_MATRIX_ROWS_LOG: usize = 2;
        const Z_MATRIX_COLS: usize = 4;
        const Z_MATRIX_COLS_LOG: usize = 2;

        let root = PathBuf::from("./prover");
        let instance_filename = "small_circuit_instance";
        let proof_filename = "small_circuit_proof";
        let inputs_filename = "small_circuit_inputs";
        let gens_filename = "small_circuit_gens";
        let vk_filename = "small_circuit_vk";
        let pk_filename = "small_circuit_pk";

        type SmallProofCircuit = HopliteCircuit<
            NUM_INPUTS,
            NUM_CONSTRAINTS,
            NUM_CONSTRAINTS_LOG,
            NUM_VARS,
            NUM_VARS_LOG,
            NUM_VARS_LOG_MINUS_ONE,
            Z_MATRIX_ROWS,
            Z_MATRIX_ROWS_LOG,
            Z_MATRIX_COLS,
            Z_MATRIX_COLS_LOG,
        >;

        let (instance, proof, input, gens) =
            sample_nizk_proof(NUM_CONSTRAINTS, NUM_VARS, NUM_INPUTS);
        write_to_file(&instance, root.join(instance_filename));
        write_to_file(&proof, root.join(proof_filename));
        write_to_file(&input, root.join(inputs_filename));
        write_to_file(&gens, root.join(gens_filename));

        let input: Vec<Fq> = input
            .assignment
            .iter()
            .map(|input| input.to_circuit_val())
            .collect();
        let circuit =
            SmallProofCircuit::new(proof, input.try_into().unwrap(), gens, instance.digest);
        let params_gen_timer = start_timer!(|| "Parameters generation");
        let params = gen_srs(21);
        end_timer!(params_gen_timer);

        let vkey_gen_timer = start_timer!(|| "Verification key generation");
        let vk = keygen_vk(&params, &circuit).expect("Unable to generate key");
        end_timer!(vkey_gen_timer); // This took 8 mins
        let mut vk_file = File::create(root.join(vk_filename)).expect("Unable to create file");
        vk.write(&mut vk_file, halo2_proofs::SerdeFormat::RawBytesUnchecked)
            .expect("Unable to serialize");

        let pkey_gen_timer = start_timer!(|| "Proving key generation");
        let pk = keygen_pk(&params, vk, &circuit).expect("Unable to generate key");
        end_timer!(pkey_gen_timer);
        let mut pk_file = File::create(root.join(pk_filename)).expect("Unable to create file");
        pk.write(&mut pk_file, halo2_proofs::SerdeFormat::RawBytesUnchecked)
            .expect("Unable to serialize");
    }

    // cargo test  --release --package hoplite_circuit --lib --all-features -- tests::generate_pk_from_other --exact --nocapture
    #[test]
    fn generate_pk_from_other() {
        const NUM_INPUTS: usize = 2;
        const NUM_CONSTRAINTS: usize = 16;
        const NUM_CONSTRAINTS_LOG: usize = 4;
        const NUM_VARS: usize = 16;
        /// This is actually one more because we pad the witness to a higher power of two
        const NUM_VARS_LOG: usize = 5;
        const NUM_VARS_LOG_MINUS_ONE: usize = 4;
        const Z_MATRIX_ROWS: usize = 4;
        const Z_MATRIX_ROWS_LOG: usize = 2;
        const Z_MATRIX_COLS: usize = 4;
        const Z_MATRIX_COLS_LOG: usize = 2;

        let root = PathBuf::from("./prover");
        let instance_filename = "small_circuit_instance";
        let proof_filename = "small_circuit_proof";
        let inputs_filename = "small_circuit_inputs";
        let gens_filename = "small_circuit_gens";
        let vk_filename = "small_circuit_vk";
        let pk_filename = "small_circuit_pk";

        type SmallProofCircuit = HopliteCircuit<
            NUM_INPUTS,
            NUM_CONSTRAINTS,
            NUM_CONSTRAINTS_LOG,
            NUM_VARS,
            NUM_VARS_LOG,
            NUM_VARS_LOG_MINUS_ONE,
            Z_MATRIX_ROWS,
            Z_MATRIX_ROWS_LOG,
            Z_MATRIX_COLS,
            Z_MATRIX_COLS_LOG,
        >;

        let instance: Instance = read_from_file(root.join(instance_filename));
        let proof: NIZK = read_from_file(root.join(proof_filename));
        let input: libspartan::Assignment = read_from_file(root.join(inputs_filename));
        let gens: NIZKGens = read_from_file(root.join(gens_filename));

        let input: Vec<Fq> = input
            .assignment
            .iter()
            .map(|input| input.to_circuit_val())
            .collect();
        let circuit =
            SmallProofCircuit::new(proof, input.try_into().unwrap(), gens, instance.digest);
        let params_gen_timer = start_timer!(|| "Parameters generation");
        let params = gen_srs(21); // these are deterministically generated, right?
        end_timer!(params_gen_timer);

        let mut vk_file = File::open(root.join(vk_filename)).expect("Unable to read vk");
        let vk = plonk::VerifyingKey::<G1Affine>::read::<_, SmallProofCircuit>(
            &mut vk_file,
            halo2_proofs::SerdeFormat::RawBytesUnchecked,
        )
        .expect("Unable to read vk from file");

        let pkey_gen_timer = start_timer!(|| "Proving key generation");
        let pk = keygen_pk(&params, vk, &circuit).expect("Unable to generate key");
        end_timer!(pkey_gen_timer);
        let mut pk_file = File::create(root.join(pk_filename)).expect("Unable to create file");
        pk.write(&mut pk_file, halo2_proofs::SerdeFormat::RawBytesUnchecked)
            .expect("Unable to serialize");
    }

    /// Writes `data` to a new file at `path`. Panics if anything goes wrong.
    fn write_to_file<T: Serialize>(data: &T, path: PathBuf) {
        let mut file = File::create(path).expect("Cannot create file");
        file.write_all(&bincode::serialize(data).expect("Unable to serialize"))
            .expect("Unable to write to file");
    }

    fn read_from_file<T: DeserializeOwned>(path: PathBuf) -> T {
        let mut file = File::open(path).expect("Unable to open file");
        let mut bytes = vec![];
        file.read_to_end(&mut bytes).unwrap();
        bincode::deserialize(&bytes).unwrap()
    }

    // TODO: Make this a macro
    const NUM_INPUTS: usize = 5;
    const NUM_CONSTRAINTS: usize = 8076;
    const NUM_CONSTRAINTS_LOG: usize = 13;
    const NUM_VARS: usize = 8097;
    /// This is actually one more because we pad the witness to a higher power of two
    const NUM_VARS_LOG: usize = 14;
    const NUM_VARS_LOG_MINUS_ONE: usize = 13;
    const Z_MATRIX_ROWS: usize = 64;
    const Z_MATRIX_ROWS_LOG: usize = 6;
    const Z_MATRIX_COLS: usize = 128;
    const Z_MATRIX_COLS_LOG: usize = 7;
    type SPARTAN_ECDSA_CIRCUIT = HopliteCircuit<
        NUM_INPUTS,
        NUM_CONSTRAINTS,
        NUM_CONSTRAINTS_LOG,
        NUM_VARS,
        NUM_VARS_LOG,
        NUM_VARS_LOG_MINUS_ONE,
        Z_MATRIX_ROWS,
        Z_MATRIX_ROWS_LOG,
        Z_MATRIX_COLS,
        Z_MATRIX_COLS_LOG,
    >;

    fn spartan_ecdsa_circuit() -> SPARTAN_ECDSA_CIRCUIT {
        let mut proof_file = File::open("./prover/proof.bin").expect("Proof file not found.");
        let mut input_file = File::open("./prover/input.bin").expect("Input file not found");
        let mut proof = vec![];
        let mut input = vec![];
        proof_file.read_to_end(&mut proof).unwrap();
        input_file.read_to_end(&mut input).unwrap();
        let proof: NIZK = bincode::deserialize(&proof).unwrap();

        println!("Decoded a NIZK proof with:");
        println!(
            "proof.comm_vars.C length = {:?}",
            proof.r1cs_sat_proof.comm_vars.C.len()
        );
        println!(
            "proof.r1cs_sat_proof.sc_proof_phase1.comm_evals.len() = {:?}",
            proof.r1cs_sat_proof.sc_proof_phase1.comm_evals.len()
        );
        println!(
            "proof.r1cs_sat_proof.sc_proof_phase2.comm_evals.len() = {:?}",
            proof.r1cs_sat_proof.sc_proof_phase2.comm_evals.len()
        );
        println!(
            "proof.r1cs_sat_proof.proof_eval_vars_at_ry.proof.bullet_reduction_proof.L_vec.len() = {:?}",
            proof.r1cs_sat_proof.proof_eval_vars_at_ry.proof.bullet_reduction_proof.L_vec.len()
        );
        println!(
            "proof.r1cs_sat_proof.proof_eval_vars_at_ry.proof.bullet_reduction_proof.R_vec.len() = {:?}",
            proof.r1cs_sat_proof.proof_eval_vars_at_ry.proof.bullet_reduction_proof.R_vec.len()
        );
        let inst = load_as_spartan_inst(
            "../circuits/build/pubkey_membership/pubkey_membership.r1cs".into(),
            5,
        );

        let _sc_proof_phase1: CVSumCheckProof<NUM_CONSTRAINTS_LOG, 4> =
            proof.r1cs_sat_proof.sc_proof_phase1.to_circuit_val();

        let r1cs_sat_proof = &proof.r1cs_sat_proof;

        let _claims_phase2 = &r1cs_sat_proof.claims_phase2;

        let mut inputs = Vec::new();
        for i in 0..NUM_INPUTS {
            inputs.push(input[(i * 32)..((i + 1) * 32)].try_into().unwrap());
        }

        let assignment_inputs = InputsAssignment::new(&inputs).unwrap();

        let input: Vec<Fq> = assignment_inputs
            .assignment
            .iter()
            .map(|x| x.to_circuit_val())
            .collect();

        let gens = NIZKGens::new(NUM_CONSTRAINTS, NUM_VARS, NUM_INPUTS); // TODO: The parameter gen guesses the size of Z-matrix itself instead of taking as input

        SPARTAN_ECDSA_CIRCUIT::new(proof, input.try_into().unwrap(), gens, inst.digest)
    }

    // cargo test --release --package hoplite_circuit --lib --all-features -- tests::test_spartan_ecdsa_mock_prove --exact --nocapture
    #[test]
    fn test_spartan_ecdsa_mock_prove() {
        let circuit = spartan_ecdsa_circuit();
        let k = 21;
        let prover = MockProver::<Fr>::run(k, &circuit, vec![vec![]]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    // cargo test --release --package hoplite_circuit --lib --all-features -- tests::test_spartan_ecdsa_prove --exact --nocapture
    #[test]
    fn test_spartan_ecdsa_prove() -> Result<(), Box<dyn std::error::Error>> {
        let circuit = spartan_ecdsa_circuit();
        let params_gen_timer = start_timer!(|| "Parameters generation");
        let params = gen_srs(21);
        end_timer!(params_gen_timer);

        let vkey_gen_timer = start_timer!(|| "Verification key generation");
        let vk = keygen_vk(&params, &circuit)?;
        end_timer!(vkey_gen_timer);

        let pkey_gen_timer = start_timer!(|| "Proving key generation");
        let pk = keygen_pk(&params, vk, &circuit)?;
        end_timer!(pkey_gen_timer);
        let mut rng = OsRng;

        let target = Secq256k1Affine::generator() * secpq_curves::Fp::one();

        let x_limbs: Vec<Fr> =
            decompose_biguint(&BigUint::from_bytes_le(&target.x.to_bytes()), 3, 88);
        let y_limbs: Vec<Fr> =
            decompose_biguint(&BigUint::from_bytes_le(&target.y.to_bytes()), 3, 88);

        let instances = vec![x_limbs, y_limbs].concat();

        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        let proving_timer = start_timer!(|| "Proving");
        create_proof::<
            KZGCommitmentScheme<Bn256>,
            ProverSHPLONK<'_, Bn256>,
            Challenge255<G1Affine>,
            _,
            Blake2bWrite<Vec<u8>, G1Affine, Challenge255<_>>,
            _,
        >(
            &params,
            &pk,
            &[circuit],
            &[&[instances.as_slice()]],
            &mut rng,
            &mut transcript,
        )
        .expect("prover should not fail");

        let proof = transcript.finalize();
        end_timer!(proving_timer);
        println!("proof size: {}", proof.len());

        let mut verifier_transcript = Blake2bRead::<_, G1Affine, Challenge255<_>>::init(&proof[..]);
        let strategy = SingleStrategy::new(&params);

        let verifier_params: ParamsVerifierKZG<Bn256> = params.verifier_params().clone();

        verify_proof::<
            KZGCommitmentScheme<Bn256>,
            VerifierSHPLONK<'_, Bn256>,
            Challenge255<G1Affine>,
            Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>,
            SingleStrategy<'_, Bn256>,
        >(
            &verifier_params,
            pk.get_vk(),
            strategy,
            &[&[instances.as_slice()]],
            &mut verifier_transcript,
        )
        .expect("failed to verify bench circuit");

        Ok(())
    }
}
