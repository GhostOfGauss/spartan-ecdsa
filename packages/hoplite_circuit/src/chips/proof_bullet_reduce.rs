use super::utils::Assign;
use crate::{chips::secq256k1::Secq256k1Chip, transcript::HopliteTranscript, Fq};
use ff::Field;
use halo2_base::{utils::PrimeField, Context};
use halo2_ecc::bigint::CRTInteger;
use halo2_ecc::ecc::EcPoint;
use halo2_ecc::fields::FieldChip;
use hoplite::circuit_vals::ToCircuitVal;
use libspartan::math::Math;
use libspartan::transcript::{ProofTranscript, Transcript};
use num_bigint::BigUint;
use num_traits::identities::Zero;
use secpq_curves::group::{Curve, Group};
use secpq_curves::Secq256k1;

use super::pedersen_commit::PedersenCommitChip;

#[derive(Clone)]
pub struct AssignedBulletReductionProof<'v, F: PrimeField, const N_LOG: usize> {
    pub L_vec: [EcPoint<F, CRTInteger<'v, F>>; N_LOG],
    pub R_vec: [EcPoint<F, CRTInteger<'v, F>>; N_LOG],
}

#[derive(Clone)]
pub struct BulletReduceChip<F: PrimeField, const N_LOG: usize> {
    pub secq_chip: Secq256k1Chip<F>,
    pub pedersen_chip: PedersenCommitChip<F>,
    pub window_bits: usize,
}

impl<'v, F: PrimeField, const N_LOG: usize> BulletReduceChip<F, N_LOG> {
    pub fn construct(
        secq_chip: Secq256k1Chip<F>,
        pedersen_chip: PedersenCommitChip<F>,
        window_bits: usize,
    ) -> Self {
        Self {
            secq_chip,
            pedersen_chip,
            window_bits,
        }
    }

    // fn batch_invert<const N: usize>(&self, ctx: &mut Context<'v, F>, a: [CRTInteger<'v, F>; N]) {}

    /// TODO: What computations on challenge points really need to be done in-circuit?
    /// TODO: Generators input -- should they already be allocated? They're probably used elsewhere
    #[allow(clippy::too_many_arguments, clippy::type_complexity)]
    pub fn verify<const N: usize>(
        &self,
        ctx: &mut Context<'v, F>,
        upsilon: &EcPoint<F, CRTInteger<'v, F>>, // The upsilon calculated in this func should equal this
        a: &[CRTInteger<'v, F>; N],
        G: &[Secq256k1; N],
        proof: &AssignedBulletReductionProof<'v, F, N_LOG>,
        transcript: &mut Transcript,
    ) -> (
        EcPoint<F, CRTInteger<'v, F>>,
        CRTInteger<'v, F>,
        EcPoint<F, CRTInteger<'v, F>>,
    ) {
        let limb_bits = self.secq_chip.ecc_chip.field_chip.limb_bits;
        // #####
        // 1: Compute the verification scalars
        // #####

        // Compute challenges
        let mut challenges = Vec::with_capacity(N_LOG);
        let mut challenges_inv = Vec::with_capacity(N_LOG);
        for (L, R) in proof.L_vec.iter().zip(proof.R_vec.iter()) {
            transcript.append_circuit_point(b"L", L.clone());
            transcript.append_circuit_point(b"R", R.clone());
            let c = transcript.challenge_scalar(b"u").to_circuit_val();
            let c_inv = c.invert().unwrap();
            let c = Some(c).assign(ctx, &self.secq_chip);
            let c_inv = Some(c_inv).assign(ctx, &self.secq_chip);
            challenges.push(c);
            challenges_inv.push(c_inv);
        }

        // 2. Compute the vector of challenge products
        let s = self.process_challenges(
            ctx,
            &challenges.clone().try_into().unwrap(),
            &challenges_inv.clone().try_into().unwrap(),
        );

        // 3. Compute the square of the challenges
        let mut challenges_sq = vec![];
        for c in challenges.clone() {
            let c_i_squared = self.secq_chip.fq_chip.mul(ctx, &c, &c);
            challenges_sq.push(c_i_squared.clone());
        }

        let mut challenges_inv_sq = vec![];
        for c in challenges_inv.clone() {
            let c_i_squared = self.secq_chip.fq_chip.mul(ctx, &c, &c);
            challenges_inv_sq.push(c_i_squared.clone());
        }

        let mut upsilon_hat = upsilon.clone();

        for i in 0..N_LOG {
            let p_i_l = self.secq_chip.ecc_chip.scalar_mult(
                ctx,
                &proof.L_vec[i],
                &challenges_sq[i].truncation.limbs,
                limb_bits,
                4,
            );
            let p_i_r = self.secq_chip.ecc_chip.scalar_mult(
                ctx,
                &proof.R_vec[i],
                &challenges_inv_sq[i].truncation.limbs,
                limb_bits,
                4,
            );

            let p_i = self
                .secq_chip
                .ecc_chip
                .add_unequal(ctx, &p_i_l, &p_i_r, true);

            upsilon_hat = self
                .secq_chip
                .ecc_chip
                .add_unequal(ctx, &p_i, &upsilon_hat, true);
        }

        let mut a_hat = self.secq_chip.fq_chip.load_constant(ctx, BigUint::zero());
        let mut g_hat = self
            .secq_chip
            .ecc_chip
            .assign_constant_point(ctx, Secq256k1::identity().to_affine());

        for ((a, g), s) in a.iter().zip(G.iter()).zip(s.iter()) {
            let a_s = self.secq_chip.fq_chip.mul(ctx, a, s);
            let g = self
                .secq_chip
                .ecc_chip
                .assign_constant_point(ctx, g.to_affine());
            let g_s =
                self.secq_chip
                    .ecc_chip
                    .scalar_mult(ctx, &g, &s.truncation.limbs, limb_bits, 4);
            a_hat = self.secq_chip.fq_chip.add_no_carry(ctx, &a_hat, &a_s);
            a_hat = self.secq_chip.fq_chip.carry_mod(ctx, &a_hat);
            g_hat = self.secq_chip.ecc_chip.add_unequal(ctx, &g_hat, &g_s, true);
        }

        (upsilon_hat, a_hat, g_hat)
    }

    /// Constrains `challenges` and `challenges_inv` to be inverses and
    /// returns `s` vector for verifier MSM.
    fn process_challenges(
        &self,
        ctx: &mut Context<'v, F>,
        challenges: &[CRTInteger<'v, F>; N_LOG],
        challenges_inv: &[CRTInteger<'v, F>; N_LOG],
    ) -> Vec<CRTInteger<'v, F>> {
        let one = Some(Fq::one()).assign(ctx, &self.secq_chip);
        for (c, c_inv) in challenges.iter().zip(challenges_inv.iter()) {
            let prod = self.secq_chip.fq_chip.mul(ctx, c, c_inv);
            self.secq_chip.fq_chip.assert_equal(ctx, &prod, &one); // TODO: Do you even need to assert this? The verifier computed the inverses himself...
        }
        let mut s = Vec::new();

        for i in 0..N_LOG.pow2() {
            let mut acc = one.clone();
            for j in 0..N_LOG {
                if ((i >> j) & 1) != 0 {
                    acc = self
                        .secq_chip
                        .fq_chip
                        .mul(ctx, &challenges[N_LOG - 1 - j], &acc);
                } else {
                    acc = self
                        .secq_chip
                        .fq_chip
                        .mul(ctx, &challenges_inv[N_LOG - 1 - j], &acc);
                }
            }
            s.push(acc);
        }
        s
    }
}
