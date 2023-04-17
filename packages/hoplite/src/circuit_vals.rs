use crate::{Fp, Fq};
use libspartan::nizk::DotProductProofLog;
use libspartan::{
    dense_mlpoly::{PolyCommitment, PolyEvalProof},
    group::CompressedGroup,
    nizk::{BulletReductionProof, DotProductProof, EqualityProof, KnowledgeProof, ProductProof},
    scalar::Scalar,
    sumcheck::ZKSumcheckInstanceProof,
};
use secpq_curves::{
    group::{prime::PrimeCurveAffine, Curve},
    CurveAffine, Secq256k1, Secq256k1Affine,
};
use secq256k1::{
    affine::Group,
    elliptic_curve::{
        subtle::{Choice, ConditionallySelectable, ConstantTimeEq},
        Field, PrimeField,
    },
};

use std::option::Option;

// ############################
// `CV` stands for `Circuit Value`.
// ############################

#[derive(Debug)]
pub struct CVSumCheckProof<const N_ROUNDS: usize, const DIMENSION: usize> {
    pub comm_polys: [Option<Secq256k1>; N_ROUNDS],
    pub comm_evals: [Option<Secq256k1>; N_ROUNDS],
    pub proofs: [CVDotProdProof<DIMENSION>; N_ROUNDS],
}

impl<const N_ROUNDS: usize, const DIMENSION: usize> CVSumCheckProof<N_ROUNDS, DIMENSION> {
    pub fn without_witness(_num_rounds: usize, poly_degree: usize) -> Self {
        Self {
            comm_polys: [None; N_ROUNDS],
            comm_evals: [None; N_ROUNDS],
            // We pass poly_degree + 1 because we're counting the degree 0 term as well.
            proofs: vec![CVDotProdProof::without_witness(poly_degree + 1); N_ROUNDS]
                .try_into()
                .unwrap(), // TODO: Fix this unwrap and remove unused `num_rounds`
        }
    }
}

impl<const N_ROUNDS: usize, const DIMENSION: usize> Default
    for CVSumCheckProof<N_ROUNDS, DIMENSION>
{
    fn default() -> Self {
        Self::without_witness(N_ROUNDS, DIMENSION) // TODO: is DIMENSION right here ?
    }
}

pub struct CVBulletReductionProof<const N_LOG: usize> {
    pub L_vec: [Option<Secq256k1>; N_LOG],
    pub R_vec: [Option<Secq256k1>; N_LOG],
}

impl<const N_LOG: usize> CVBulletReductionProof<N_LOG> {
    // TODO: N is vec_len/2
    fn without_witness(vec_len: usize) -> Self {
        assert!(vec_len % 2 == 0, "vec_len must be even"); // TODO: how to replace vec_len?

        Self {
            L_vec: [None; N_LOG],
            R_vec: [None; N_LOG],
        }
    }
}

#[derive(Debug, Clone)]
pub struct CVDotProdProof<const DIMENSION: usize> {
    pub delta: Option<Secq256k1>,
    pub beta: Option<Secq256k1>,
    pub z: [Option<Fq>; DIMENSION],
    pub z_delta: Option<Fq>,
    pub z_beta: Option<Fq>,
}

impl<const DIMENSION: usize> CVDotProdProof<DIMENSION> {
    fn without_witness(_vec_len: usize) -> Self {
        // TODO: Removed unused args
        Self {
            delta: None,
            beta: None,
            z: [None; DIMENSION],
            z_delta: None,
            z_beta: None,
        }
    }
}

#[derive(Default)]
pub struct CVEqualityProof {
    pub alpha: Option<Secq256k1>,
    pub z: Option<Fq>,
}

#[derive(Default)]
pub struct CVKnowledgeProof {
    pub alpha: Option<Secq256k1>,
    pub z1: Option<Fq>,
    pub z2: Option<Fq>,
}

#[derive(Default)]
pub struct CVProductProof {
    pub alpha: Option<Secq256k1>,
    pub beta: Option<Secq256k1>,
    pub delta: Option<Secq256k1>,
    pub z: [Option<Fq>; 5],
}

/// A `DotProductProofLog` proves a relation `<a, x> = y` for
/// private witness `x, y` using an `N_LOG`-step Bulletproof
/// reduction, where `N` is the length of `a` and `x`.
pub struct CVDotProductProofLog<const N_LOG: usize> {
    pub bullet_reduction_proof: CVBulletReductionProof<N_LOG>,
    pub delta: Option<Secq256k1>,
    pub beta: Option<Secq256k1>,
    pub z1: Option<Fq>,
    pub z2: Option<Fq>,
}

impl<const N_LOG: usize> CVDotProductProofLog<N_LOG> {
    fn without_witness(vec_len: usize) -> Self {
        Self {
            bullet_reduction_proof: CVBulletReductionProof::without_witness(vec_len),
            delta: None,
            beta: None,
            z1: None,
            z2: None,
        }
    }
}

pub struct CVPolyEvalProof<const N_LOG: usize> {
    pub proof: CVDotProductProofLog<N_LOG>,
}

impl<const N_LOG: usize> CVPolyEvalProof<N_LOG> {
    pub fn without_witness(vec_len: usize) -> Self {
        Self {
            proof: CVDotProductProofLog::without_witness(vec_len),
        }
    }
}

impl<const N_LOG: usize> Default for CVPolyEvalProof<N_LOG> {
    fn default() -> Self {
        Self::without_witness(N_LOG) // TODO: right size?
    }
}

pub struct CVPolyCommitment<const N: usize> {
    pub C: [Option<Secq256k1>; N],
}

impl<const N: usize> CVPolyCommitment<N> {
    pub fn without_witness(_vec_len: usize) -> Self {
        // TODO: remove unused arg
        Self { C: [None; N] }
    }
}

impl<const N: usize> Default for CVPolyCommitment<N> {
    fn default() -> Self {
        Self::without_witness(N)
    }
}

// Convert the types defined in the `secq256k1` crate
// to the types defined in the `secpq_curves` crate.
// This conversion is necessary because,
// `libspartan` uses `secq256k1` for curve/field operations
// whereas halo2 uses `secpq_curves`

// In general, we need to do the following two conversions
// `CompressedGroup` -> `Secq256k1`
// `Scalar` -> `Fq`
pub trait ToCircuitVal<V> {
    fn to_circuit_val(&self) -> V;
}

pub trait FromCircuitVal<V> {
    fn from_circuit_val(v: &V) -> Self;
}

impl FromCircuitVal<Secq256k1> for CompressedGroup {
    fn from_circuit_val(point: &Secq256k1) -> CompressedGroup {
        if point.is_identity().into() {
            return CompressedGroup::identity();
        }

        let coords = point.to_affine().coordinates().unwrap();
        let mut x = coords.x().to_bytes();
        let mut y = coords.y().to_bytes();

        x.reverse();
        y.reverse();

        CompressedGroup::from_affine_coordinates(&x.into(), &y.into(), true)
    }
}

impl ToCircuitVal<Fq> for Scalar {
    fn to_circuit_val(&self) -> Fq {
        let bytes = self.to_bytes();
        Fq::from_bytes(&bytes).unwrap()
    }
}

impl ToCircuitVal<CVEqualityProof> for EqualityProof {
    fn to_circuit_val(&self) -> CVEqualityProof {
        let alpha = Some(self.alpha.to_circuit_val());
        let z = Some(self.z.to_circuit_val());

        CVEqualityProof { alpha, z }
    }
}

impl ToCircuitVal<CVKnowledgeProof> for KnowledgeProof {
    fn to_circuit_val(&self) -> CVKnowledgeProof {
        let alpha = Some(self.alpha.to_circuit_val());
        let z1 = Some(self.z1.to_circuit_val());
        let z2 = Some(self.z2.to_circuit_val());

        CVKnowledgeProof { alpha, z1, z2 }
    }
}

impl ToCircuitVal<CVProductProof> for ProductProof {
    fn to_circuit_val(&self) -> CVProductProof {
        let alpha = Some(self.alpha.to_circuit_val());
        let beta = Some(self.beta.to_circuit_val());
        let delta = Some(self.delta.to_circuit_val());
        let z: [Option<Fq>; 5] = self
            .z
            .iter()
            .map(|z_i| Some(z_i.to_circuit_val()))
            .collect::<Vec<Option<Fq>>>()
            .try_into()
            .unwrap();

        CVProductProof {
            alpha,
            beta,
            delta,
            z,
        }
    }
}

impl<const N_LOG: usize> ToCircuitVal<CVDotProductProofLog<N_LOG>> for DotProductProofLog {
    fn to_circuit_val(&self) -> CVDotProductProofLog<N_LOG> {
        let beta = Some(self.beta.to_circuit_val());
        let delta = Some(self.delta.to_circuit_val());
        let z1 = Some(self.z1.to_circuit_val());
        let z2 = Some(self.z2.to_circuit_val());

        let cv_bullet_reduction_proof = CVBulletReductionProof {
            L_vec: self
                .bullet_reduction_proof
                .L_vec
                .iter()
                .map(|val| Some(val.compress().to_circuit_val()))
                .collect::<Vec<Option<Secq256k1>>>()
                .try_into()
                .unwrap(),
            R_vec: self
                .bullet_reduction_proof
                .R_vec
                .iter()
                .map(|val| Some(val.compress().to_circuit_val()))
                .collect::<Vec<Option<Secq256k1>>>()
                .try_into()
                .unwrap(),
        };

        CVDotProductProofLog {
            delta,
            beta,
            z1,
            z2,
            bullet_reduction_proof: cv_bullet_reduction_proof,
        }
    }
}

impl<const N_LOG: usize> ToCircuitVal<CVPolyEvalProof<N_LOG>> for PolyEvalProof {
    fn to_circuit_val(&self) -> CVPolyEvalProof<N_LOG> {
        let dotprod_proof_log = &self.proof;
        let beta = Some(dotprod_proof_log.beta.to_circuit_val());
        let delta = Some(dotprod_proof_log.delta.to_circuit_val());
        let z1 = Some(dotprod_proof_log.z1.to_circuit_val());
        let z2 = Some(dotprod_proof_log.z2.to_circuit_val());

        let cv_bullet_reduction_proof = CVBulletReductionProof {
            L_vec: dotprod_proof_log
                .bullet_reduction_proof
                .L_vec
                .iter()
                .map(|val| Some(val.compress().to_circuit_val()))
                .collect::<Vec<Option<Secq256k1>>>()
                .try_into()
                .unwrap(),
            R_vec: dotprod_proof_log
                .bullet_reduction_proof
                .R_vec
                .iter()
                .map(|val| Some(val.compress().to_circuit_val()))
                .collect::<Vec<Option<Secq256k1>>>()
                .try_into()
                .unwrap(),
        };

        let cv_dotprod_proof_log = CVDotProductProofLog {
            delta,
            beta,
            z1,
            z2,
            bullet_reduction_proof: cv_bullet_reduction_proof,
        };

        CVPolyEvalProof {
            proof: cv_dotprod_proof_log,
        }
    }
}

impl<const N: usize> ToCircuitVal<CVPolyCommitment<N>> for PolyCommitment {
    fn to_circuit_val(&self) -> CVPolyCommitment<N> {
        let C = self
            .C
            .iter()
            .map(|c| Some(c.to_circuit_val()))
            .collect::<Vec<Option<Secq256k1>>>()
            .try_into()
            .unwrap();

        CVPolyCommitment { C }
    }
}

impl ToCircuitVal<Secq256k1> for CompressedGroup {
    fn to_circuit_val(&self) -> Secq256k1 {
        if self.is_identity() {
            return Secq256k1::identity();
        }

        let mut x_bytes: [u8; 32] = (*self.x().unwrap()).try_into().unwrap();
        // x_bytes is in big-endian!
        x_bytes.reverse();

        let x = Fp::from_bytes(&x_bytes).unwrap();

        let coords = self.coordinates();
        let y_odd: Choice = match coords.tag() {
            secq256k1::elliptic_curve::sec1::Tag::CompressedOddY => Choice::from(1),
            secq256k1::elliptic_curve::sec1::Tag::CompressedEvenY => Choice::from(0),
            _ => Choice::from(0),
        };

        let x3 = x.square() * x;
        let b = Fp::from_raw([7, 0, 0, 0]);
        let y = (x3 + b).sqrt();

        y.map(|y| {
            let y = Fp::conditional_select(&-y, &y, y.is_odd().ct_eq(&y_odd));
            let p = Secq256k1Affine::from_xy(x, y).unwrap();
            p.to_curve()
        })
        .unwrap()
    }
}

impl<const DIMENSION: usize> ToCircuitVal<CVDotProdProof<DIMENSION>> for DotProductProof {
    fn to_circuit_val(&self) -> CVDotProdProof<DIMENSION> {
        CVDotProdProof {
            delta: Some(self.delta.to_circuit_val()),
            beta: Some(self.beta.to_circuit_val()),
            z_beta: Some(self.z_beta.to_circuit_val()),
            z_delta: Some(self.z_delta.to_circuit_val()),
            z: self
                .z
                .iter()
                .map(|z_i| Some(z_i.to_circuit_val()))
                .collect::<Vec<Option<Fq>>>()
                .try_into()
                .unwrap(),
        }
    }
}

impl<const N_ROUNDS: usize, const DIMENSION: usize>
    ToCircuitVal<CVSumCheckProof<N_ROUNDS, DIMENSION>> for ZKSumcheckInstanceProof
{
    fn to_circuit_val(&self) -> CVSumCheckProof<N_ROUNDS, DIMENSION> {
        let mut proofs = vec![];
        let mut comm_polys = vec![];
        let mut comm_evals = vec![];
        for i in 0..self.proofs.len() {
            proofs.push(self.proofs[i].to_circuit_val());
            comm_polys.push(Some(self.comm_polys[i].to_circuit_val()));
            comm_evals.push(Some(self.comm_evals[i].to_circuit_val()));
        }

        CVSumCheckProof {
            comm_polys: comm_polys.try_into().unwrap(),
            comm_evals: comm_evals.try_into().unwrap(),
            proofs: proofs.try_into().unwrap(),
        }
    }
}

impl<const N: usize> ToCircuitVal<CVBulletReductionProof<N>> for BulletReductionProof {
    fn to_circuit_val(&self) -> CVBulletReductionProof<N> {
        let mut L_vec = vec![];
        let mut R_vec = vec![];
        for i in 0..self.L_vec.len() {
            L_vec.push(Some(self.L_vec[i].to_circuit_val()));
            R_vec.push(Some(self.R_vec[i].to_circuit_val()));
        }

        CVBulletReductionProof {
            L_vec: L_vec.try_into().unwrap(),
            R_vec: R_vec.try_into().unwrap(), // TODO: Change type of BulletReductionProof ?
        }
    }
}
