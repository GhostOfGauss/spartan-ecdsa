use crate::{
    circuit_vals::{CVDotProductProofLog, FromCircuitVal},
    commitments::MultiCommitGens,
    proof_bullet_reduce,
    utils::to_fq,
    Fq,
};
use libspartan::{
    group::CompressedGroup,
    transcript::{AppendToTranscript, ProofTranscript, Transcript},
};
use secpq_curves::Secq256k1;

// https://eprint.iacr.org/2017/1132.pdf
// P.19 proof_log-of-dot-prod
pub fn verify<const N: usize, const N_LOG: usize>(
    gens_1: &MultiCommitGens,
    gens_n: &MultiCommitGens,
    a: &[Fq; N],
    Cx: &Secq256k1, // commitment to the evaluation (Cy)
    Cy: &Secq256k1, // commitment to the evaluation (Cy)
    proof: &CVDotProductProofLog<N_LOG>,
    transcript: &mut Transcript,
) {
    transcript.append_protocol_name(b"dot product proof (log)");
    CompressedGroup::from_circuit_val(Cx).append_to_transcript(b"Cx", transcript);
    CompressedGroup::from_circuit_val(Cy).append_to_transcript(b"Cy", transcript);

    transcript.append_message(b"a", b"begin_append_vector");
    for a_i in a {
        transcript.append_message(b"a", &a_i.to_bytes());
    }
    transcript.append_message(b"a", b"end_append_vector");

    // sample a random base and scale the generator used for
    // the output of the inner product
    let r = to_fq(&transcript.challenge_scalar(b"r"));
    let gens_1_scaled = gens_1.scale(&r);

    // Upsilon
    let Gamma = Cx + Cy * r;

    let L: [Secq256k1; N_LOG] = proof
        .bullet_reduction_proof
        .L_vec
        .iter()
        .map(|L_i| L_i.unwrap())
        .collect::<Vec<Secq256k1>>()
        .try_into()
        .unwrap();

    let R: [Secq256k1; N_LOG] = proof
        .bullet_reduction_proof
        .R_vec
        .iter()
        .map(|R_i| R_i.unwrap())
        .collect::<Vec<Secq256k1>>()
        .try_into()
        .unwrap();

    let (Gamma_hat, a_hat, g_hat) = proof_bullet_reduce::verify_fast(
        &Gamma,
        a,
        &gens_n.G.clone().try_into().unwrap(),
        &L,
        &R,
        transcript,
    );

    CompressedGroup::from_circuit_val(&proof.delta.unwrap())
        .append_to_transcript(b"delta", transcript);
    CompressedGroup::from_circuit_val(&proof.beta.unwrap())
        .append_to_transcript(b"beta", transcript);

    let c = to_fq(&transcript.challenge_scalar(b"c"));

    let lhs = (Gamma_hat * c + proof.beta.unwrap()) * a_hat + proof.delta.unwrap();
    let rhs = (g_hat + gens_1_scaled.G[0] * a_hat) * proof.z1.unwrap()
        + gens_1_scaled.h * proof.z2.unwrap();

    assert!(rhs == lhs, "Proof (log) of dot prod verification failed");
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit_vals::ToCircuitVal;
    use libspartan::nizk::DotProductProofLog;
    use libspartan::random::RandomTape;
    use libspartan::scalar::Scalar;
    use rand_core::OsRng;

    #[test]
    fn check_dotproductproof_log() {
        const N: usize = 256;
        const N_LOG: usize = 8;
        let mut csprng: OsRng = OsRng;

        let gens = libspartan::nizk::DotProductProofGens::new(N, b"test-N");

        let x: Vec<Scalar> = (0..N).map(|_i| Scalar::random(&mut csprng)).collect();
        let a: Vec<Scalar> = (0..N).map(|_i| Scalar::random(&mut csprng)).collect();
        let y = libspartan::nizk::DotProductProof::compute_dotproduct(&x, &a);

        let r_x = Scalar::random(&mut csprng);
        let r_y = Scalar::random(&mut csprng);

        let mut random_tape = RandomTape::new(b"proof");
        let mut prover_transcript = Transcript::new(b"example");
        let (proof, Cx, Cy) = DotProductProofLog::prove(
            &gens,
            &mut prover_transcript,
            &mut random_tape,
            &x,
            &r_x,
            &a,
            &y,
            &r_y,
        );

        // Perform some conversion to CV types:
        let a: Vec<Fq> = a.iter().map(|a| a.to_circuit_val()).collect();
        let mut verifier_transcript = Transcript::new(b"example");
        verify::<N, N_LOG>(
            &gens.gens_1.into(),
            &gens.gens_n.into(),
            &a.try_into().unwrap(),
            &Cx.to_circuit_val(),
            &Cy.to_circuit_val(),
            &proof.to_circuit_val(),
            &mut verifier_transcript,
        );
    }
}
