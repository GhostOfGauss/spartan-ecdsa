use crate::{
    circuit_vals::{FromCircuitVal, ToCircuitVal},
    Fq,
};
use libspartan::math::Math;
use libspartan::{
    group::CompressedGroup,
    scalar::Scalar,
    transcript::{ProofTranscript, Transcript},
};
use secpq_curves::{group::Group, Secq256k1};

/// Performs Verifier side of a Bulletproof reduction. Specifically, given the
/// commitment `upsilon`, public vector `a`, and commitment generators `G` of
/// length `N` in an inner product argument, this iteratively reduces `a` and `G`
/// to vectors of length 1 using `N_LOG` steps. The supplied `upsilon_L`, `upsilon_R`
/// are the cross-term commitments sent by the Prover in each round. Their length
/// is therefore `N_LOG`.
pub fn verify<const N: usize, const N_LOG: usize>(
    upsilon: &Secq256k1,
    a: &[Fq; N],
    G: &[Secq256k1; N],
    upsilon_L: &[Secq256k1; N_LOG],
    upsilon_R: &[Secq256k1; N_LOG],
    transcript: &mut Transcript,
) -> (Secq256k1, Fq, Secq256k1) {
    // #####
    // 1: Compute the verification scalars
    // #####

    // Compute challenges
    let mut challenges = vec![];
    for (L, R) in upsilon_L.iter().zip(upsilon_R.iter()) {
        transcript.append_point(b"L", &CompressedGroup::from_circuit_val(L));
        transcript.append_point(b"R", &CompressedGroup::from_circuit_val(R));
        //        CompressedGroup::from_circuit_val(R).append_to_transcript(b"R", transcript);
        challenges.push(transcript.challenge_scalar(b"u"));
    }

    // 2. Compute the invert of the challenges
    let (challenges_inv, _s) =
        process_challenges::<N, N_LOG>(&challenges.clone().try_into().unwrap());

    // 3. Compute the square of the challenges
    let challenges_sq = challenges
        .iter()
        .map(|c| c.square())
        .collect::<Vec<Scalar>>();
    let challenges_inv_sq = challenges_inv
        .iter()
        .map(|c| c.square())
        .collect::<Vec<Scalar>>();

    let mut upsilon_hat = Secq256k1::identity();
    upsilon_hat += upsilon;

    let n = upsilon_L.len();
    for i in 0..n {
        upsilon_hat += upsilon_L[i] * challenges_sq[i].to_circuit_val()
            + upsilon_R[i] * challenges_inv_sq[i].to_circuit_val();
    }

    let mut a = &mut a.to_owned()[..];
    let mut G = &mut G.to_owned()[..];

    let mut n = G.len();
    while n != 1 {
        let round_number = challenges.len() - n.log_2();
        n /= 2;
        let (a_L, a_R) = a.split_at_mut(n);
        let (G_L, G_R) = G.split_at_mut(n);
        let u = challenges[round_number];
        let u_inv = challenges_inv[round_number];

        for i in 0..n {
            a_L[i] = a_L[i] * u_inv.to_circuit_val() + a_R[i] * u.to_circuit_val();

            G_L[i] = G_L[i] * u_inv.to_circuit_val() + G_R[i] * u.to_circuit_val();
        }

        a = a_L;
        G = G_L;
    }

    let a_hat = a[0];
    let g_hat = G[0];

    (upsilon_hat, a_hat, g_hat)
}

/// Optimization to the [verify] function using MSM.
/// TODO: Currently this doesn't use an optimized MSM.
pub fn verify_fast<const N: usize, const N_LOG: usize>(
    upsilon: &Secq256k1,
    a: &[Fq; N],
    G: &[Secq256k1; N],
    upsilon_L: &[Secq256k1; N_LOG],
    upsilon_R: &[Secq256k1; N_LOG],
    transcript: &mut Transcript,
) -> (Secq256k1, Fq, Secq256k1) {
    // #####
    // 1: Compute the verification scalars
    // #####

    // Compute challenges
    let mut challenges = vec![];
    for (L, R) in upsilon_L.iter().zip(upsilon_R.iter()) {
        transcript.append_point(b"L", &CompressedGroup::from_circuit_val(L));
        transcript.append_point(b"R", &CompressedGroup::from_circuit_val(R));
        //        CompressedGroup::from_circuit_val(R).append_to_transcript(b"R", transcript);
        challenges.push(transcript.challenge_scalar(b"u"));
    }
    let challenges: [Scalar; N_LOG] = challenges.try_into().unwrap();

    // 2. Compute the invert of the challenges
    let (challenges_inv, s) = process_challenges::<N, N_LOG>(&challenges);

    // 3. Compute the square of the challenges
    let challenges_sq = challenges
        .iter()
        .map(|c| c.square())
        .collect::<Vec<Scalar>>();
    let challenges_inv_sq = challenges_inv
        .iter()
        .map(|c| c.square())
        .collect::<Vec<Scalar>>();

    let mut upsilon_hat = Secq256k1::identity();
    upsilon_hat += upsilon;

    let n = upsilon_L.len();
    for i in 0..n {
        upsilon_hat += upsilon_L[i] * challenges_sq[i].to_circuit_val()
            + upsilon_R[i] * challenges_inv_sq[i].to_circuit_val();
    }
    // TODO: Use actual MSM
    let mut a_hat = Fq::zero();
    let mut g_hat = Secq256k1::identity();
    let _ = a
        .iter()
        .zip(G.iter().zip(s.iter()))
        .map(|(a, (g, s))| {
            a_hat += a * s.to_circuit_val();
            g_hat += g * s.to_circuit_val();
        })
        .collect::<Vec<_>>();

    (upsilon_hat, a_hat, g_hat)
}

/// Returns `(challenges_inverse, s)`, where `s` is as in Bulletproof paper.
fn process_challenges<const N: usize, const N_LOG: usize>(
    challenges: &[Scalar; N_LOG],
) -> ([Scalar; N_LOG], [Scalar; N]) {
    let mut challenges_inv = *challenges;
    Scalar::batch_invert(&mut challenges_inv);
    let s: Vec<Scalar> = (0..N)
        .map(|i| {
            let mut acc = Scalar::one();
            for j in 0..N_LOG {
                if ((i >> j) & 1) != 0 {
                    acc *= challenges[N_LOG - 1 - j];
                } else {
                    acc *= challenges_inv[N_LOG - 1 - j];
                }
            }
            acc
        })
        .collect();
    (challenges_inv, s.try_into().unwrap())
}
