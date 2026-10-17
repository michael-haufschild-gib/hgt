# PA: signed compact completions of the moment tower collapse to RH (2026-10-17, [L])

Module: `formal/GaloisForLFunctions/RHTower/PrimeArchSignedCompactCompletionCollapse.lean` (wired into `RHTower.lean`; axioms propext/Classical.choice/Quot.sound).
Card: `docs/drafts/pipeline/3-formalized/pa-signed-compact-completion-collapse-2026-10-17.md`.

Theorem `riemannHypothesis_of_signedCompactPrimeArchMoments`: finite measures `μ ν` on `[−B, B]` with `normalizedPrimeArchMoment n = ∫x^n dμ − ∫x^n dν` for all `n` imply RH. `exists_signedCompactPrimeArchMoments_iff_riemannHypothesis`: such a pair exists iff RH (canonical compact Xi measure under RH).

Closes the frontier's PA open item "nonpassive source-faithful completion with both added and removed mass" as a measure programme, for every support radius (including Stokes nodes beyond the endpoint radius). Survivor: non-RH-hard completions must be distributions of unbounded variation/support.

Mechanism: moment germ = atom resolvent sum `F(z) = Σ_q x_q/(1 − z x_q)` (`xiAtomResolventSum_eq_tsum_moment`); transform `∫dμ/(1 − zx)` of a real-supported measure is holomorphic on the upper half-plane (`differentiableOn_markovIntegral`, via `‖1 − zx‖ ≥ |Im z|/‖z‖`); off-line zero ⇒ atom with `Im x < 0` ⇒ pole of `F` in the UHP; maximal-modulus pole, identity theorem on the convex half-disc below it, blow-up along the ray (`exists_norm_xiAtomResolventSum_gt`).

Reusable: `xiAtomResolventSum`, `differentiableAt_xiAtomResolventSum`, `markovIntegral`, `markovIntegral_eq_tsum`, `summable_moment_series`, `finite_xiZeroCopy_norm_ge`, `norm_xiZeroCopyReciprocalSquare_le_two_div_fortyOne`, `xiZeroCopyReciprocalSquare_im_eq_zero_iff`.

Process note: STATUS.md is a short route-independent constraints brief; results like this go only in cards/memory (user correction 2026-10-17).
