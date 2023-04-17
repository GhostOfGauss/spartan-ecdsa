use super::{
    proof_log_of_dotprod::{AssignedDotProductProofLog, ProofLogOfDotProdChip},
    utils::{Assign, AssignArray},
};
use crate::chips::eval_poly::EvalMLPolyChip;
use crate::chips::{proof_bullet_reduce::AssignedBulletReductionProof, secq256k1::Secq256k1Chip};
use halo2_base::{utils::PrimeField, Context};
use halo2_ecc::bigint::CRTInteger;
use halo2_ecc::ecc::EcPoint;
use hoplite::{circuit_vals::CVPolyEvalProof, commitments::MultiCommitGens};
use libspartan::transcript::{ProofTranscript, Transcript};
use secpq_curves::{
    group::{Curve, Group},
    Secq256k1,
};

pub trait AssignN<'v, F: PrimeField, const N_LOG: usize> {
    fn assign(
        &self,
        ctx: &mut Context<'v, F>,
        secq_chip: &Secq256k1Chip<F>,
    ) -> AssignedPolyEvalProof<'v, F, N_LOG>;
}

pub struct AssignedPolyEvalProof<'v, F: PrimeField, const N_LOG: usize> {
    pub proof: AssignedDotProductProofLog<'v, F, N_LOG>,
}

impl<'v, F: PrimeField, const N_LOG: usize> AssignN<'v, F, N_LOG> for CVPolyEvalProof<N_LOG> {
    fn assign(
        &self,
        ctx: &mut Context<'v, F>,
        secq_chip: &Secq256k1Chip<F>,
    ) -> AssignedPolyEvalProof<'v, F, N_LOG> {
        let z1 = self.proof.z1.assign(ctx, secq_chip);
        let z2 = self.proof.z2.assign(ctx, secq_chip);
        let beta = self.proof.beta.assign(ctx, secq_chip);
        let delta = self.proof.delta.assign(ctx, secq_chip);

        let L_vec = self
            .proof
            .bullet_reduction_proof
            .L_vec
            .assign(ctx, secq_chip);

        let R_vec = self
            .proof
            .bullet_reduction_proof
            .R_vec
            .assign(ctx, secq_chip);

        let bullet_reduction_proof = AssignedBulletReductionProof { L_vec, R_vec };

        let proof = AssignedDotProductProofLog {
            bullet_reduction_proof,
            delta,
            beta,
            z1,
            z2,
        };

        AssignedPolyEvalProof { proof }
    }
}

/// Chip for verifying Hyrax-style multilinear polynomial proofs. Here `NUM_ROWS` and `NUM_COLS`
/// refer to the casting of a vector `Z` into a matrix. These are expected to be powers of 2 whose
/// product is `Z.len()`.
/// We specify these sizes as logs because this is the number of variables used by the [EvalMLPolyChip].
pub struct PolyEvalProofChip<
    F: PrimeField,
    const Z_MATRIX_ROWS: usize,
    const Z_MATRIX_ROWS_LOG: usize,
    const Z_MATRIX_COLS: usize,
    const Z_MATRIX_COLS_LOG: usize,
> {
    secq_chip: Secq256k1Chip<F>,
    eval_ml_poly_chip_rows: EvalMLPolyChip<F, Z_MATRIX_ROWS_LOG>,
    eval_ml_poly_chip_cols: EvalMLPolyChip<F, Z_MATRIX_COLS_LOG>,
    proof_log_dotprod_chip: ProofLogOfDotProdChip<F, Z_MATRIX_COLS_LOG>,
    window_bits: usize,
}

impl<
        'v,
        F: PrimeField,
        const Z_MATRIX_ROWS: usize,
        const Z_MATRIX_ROWS_LOG: usize,
        const Z_MATRIX_COLS: usize,
        const Z_MATRIX_COLS_LOG: usize,
    > PolyEvalProofChip<F, Z_MATRIX_ROWS, Z_MATRIX_ROWS_LOG, Z_MATRIX_COLS, Z_MATRIX_COLS_LOG>
{
    pub fn construct(
        secq_chip: Secq256k1Chip<F>,
        eval_ml_poly_chip_rows: EvalMLPolyChip<F, Z_MATRIX_ROWS_LOG>,
        eval_ml_poly_chip_cols: EvalMLPolyChip<F, Z_MATRIX_COLS_LOG>,
        proof_log_dotprod_chip: ProofLogOfDotProdChip<F, Z_MATRIX_COLS_LOG>,
        window_bits: usize,
    ) -> Self {
        Self {
            secq_chip,
            eval_ml_poly_chip_rows,
            eval_ml_poly_chip_cols,
            proof_log_dotprod_chip,
            window_bits,
        }
    }

    /// This is checking the evaluation of `Z(r)`, so `comm_polys` represents the
    /// commitments to rows in the matrix form of `Z`.
    #[allow(clippy::too_many_arguments)]
    pub fn verify(
        &self,
        ctx: &mut Context<'v, F>,
        r: &[CRTInteger<'v, F>],
        C_Zr: &EcPoint<F, CRTInteger<'v, F>>,
        comm_polys: [EcPoint<F, CRTInteger<'v, F>>; Z_MATRIX_ROWS], // Commitments to the rows of Z as a matrix.
        proof: AssignedPolyEvalProof<'v, F, Z_MATRIX_COLS_LOG>,     // TODO: Size?
        gens_1: &MultiCommitGens,
        gens_n: &MultiCommitGens,
        transcript: &mut Transcript,
    ) {
        // assert_eq!(
        //     NUM_COLS + NUM_ROWS,
        //     r.len(),
        //     "Matrix size does not match vector length"
        // ); // TODO: Reinstate a size check
        let limbs_bits = self.secq_chip.ecc_chip.field_chip.limb_bits;
        transcript.append_protocol_name(b"polynomial evaluation proof");

        // Evaluate the eq poly wrt the first/last LOG_NUM_ROWS bits of r
        let r_left = &r[0..Z_MATRIX_ROWS_LOG];
        let r_right = &r[Z_MATRIX_ROWS_LOG..];
        let L = self
            .eval_ml_poly_chip_rows
            .evals(ctx, r_left.try_into().unwrap());
        let R = self.eval_ml_poly_chip_cols.evals(
            ctx,
            r_right
                .try_into()
                .expect("Has correct length because r.len() = NUM_COLS + NUM_ROWS."),
        );

        // The commitment to L * Z
        let mut C_LZ = self
            .secq_chip
            .ecc_chip
            .assign_constant_point(ctx, Secq256k1::identity().to_affine());

        for row in 0..Z_MATRIX_ROWS {
            let comm_poly_L = self.secq_chip.ecc_chip.scalar_mult(
                ctx,
                &comm_polys[row],
                &L[row].truncation.limbs,
                limbs_bits,
                self.window_bits,
            );

            C_LZ = self
                .secq_chip
                .ecc_chip
                .add_unequal(ctx, &comm_poly_L, &C_LZ, true);
        }

        println!(
            "In polyevalproof, R.len() = {:?} and Z_MATRIX_COLS = {Z_MATRIX_COLS}",
            R.len()
        );

        self.proof_log_dotprod_chip.verify::<Z_MATRIX_COLS>(
            ctx,
            R.try_into().unwrap(),
            &C_LZ,
            C_Zr,
            &proof.proof,
            gens_1,
            gens_n,
            transcript,
        );
    }
}
