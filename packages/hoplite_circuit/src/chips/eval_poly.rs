use crate::FpChip;
use halo2_base::{utils::PrimeField, Context};
use halo2_ecc::{bigint::CRTInteger, fields::FieldChip};
use libspartan::math::Math;
use num_bigint::BigUint;
use num_traits::{identities::One, Zero};

pub struct EvalMLPolyChip<F: PrimeField, const N_VARS: usize> {
    pub fp_chip: FpChip<F>,
}

impl<'v, F: PrimeField, const N_VARS: usize> EvalMLPolyChip<F, N_VARS> {
    pub fn construct(fp_chip: FpChip<F>) -> Self {
        Self { fp_chip }
    }

    /// Returns Sum_i a[i]*b[i]
    pub fn _dot_product(
        &self,
        ctx: &mut Context<'v, F>,
        a: &[CRTInteger<'v, F>],
        b: &[CRTInteger<'v, F>],
    ) -> CRTInteger<'v, F> {
        assert_eq!(a.len(), b.len(), "Vectors must have same length");
        let mut acc = self.fp_chip.load_constant(ctx, BigUint::zero());
        for (a, b) in a.iter().zip(b.iter()) {
            let term = self.fp_chip.mul(ctx, a, b);
            acc = self.fp_chip.add_no_carry(ctx, &term, &acc);

            self.fp_chip.carry_mod(ctx, &acc);
        }
        acc
    }

    /// Return the evaluations of the MLE `eq(x,point)` for all `x`
    /// in the `N_VARS`-dimensional boolean cube. Output has length `2^N_VARS`.
    pub fn evals(
        &self,
        ctx: &mut Context<'v, F>,
        point: &[CRTInteger<'v, F>; N_VARS],
    ) -> Vec<CRTInteger<'v, F>> {
        let mut evals = vec![self.fp_chip.load_constant(ctx, BigUint::one()); N_VARS.pow2()]; // TODO: Is this the right way to allocate these 1's?
        let mut size = 1;
        for j in 0..N_VARS {
            size *= 2;
            for i in (0..size).rev().step_by(2) {
                let scalar = evals[i / 2].clone();
                evals[i] = self.fp_chip.mul(ctx, &scalar, &point[j]);
                evals[i - 1] = self.fp_chip.sub_no_carry(ctx, &scalar, &evals[i]);
                self.fp_chip.carry_mod(ctx, &evals[i - 1]); // TODO: Is this the right way to do CRT arithmetic?
            }
        }
        evals
    }

    /// TODO: Is it ok for `a` to be constant, i.e. not a circuit variable ?
    pub fn compute_eq(
        &self,
        ctx: &mut Context<'v, F>,
        index: usize, // index of point
        point: &[CRTInteger<'v, F>; N_VARS],
    ) -> CRTInteger<'v, F> {
        let one = self.fp_chip.load_constant(ctx, BigUint::one());
        let mut eq = one.clone();
        for i in 0..N_VARS {
            if ((index >> i) & 1) != 0 {
                eq = self.fp_chip.mul(ctx, &eq, &point[i]);
            } else {
                let one_minus_r = self.fp_chip.sub_no_carry(ctx, &one.clone(), &point[i]);
                eq = self.fp_chip.mul(ctx, &eq, &one_minus_r);
            }
        }
        eq
    }

    /// Interpolates the MLE with prescribed `values` and evaluates at `point`.
    /// NOTE: This assumes the values are ordered, starting with the 0 index.
    pub fn interpolate(
        &self,
        ctx: &mut Context<'v, F>,
        values: &[CRTInteger<'v, F>],
        point: &[CRTInteger<'v, F>; N_VARS],
    ) -> CRTInteger<'v, F> {
        assert!(values.len() <= num_traits::pow(2, N_VARS));
        let mut acc = self.fp_chip.load_constant(ctx, BigUint::zero());
        for (i, value) in values.iter().enumerate() {
            let eq = self.compute_eq(ctx, i, point);
            let term = self.fp_chip.mul(ctx, value, &eq);
            acc = self.fp_chip.add_no_carry(ctx, &term, &acc);
            self.fp_chip.carry_mod(ctx, &acc);
        }
        acc
    }
}

#[test]
fn usize_bits() {
    let six = 6usize;
    println!("{:b}", six);
    for i in 0..3 {
        println!("Bit {i} is {:?}", (six >> i) & 1);
    }
}
