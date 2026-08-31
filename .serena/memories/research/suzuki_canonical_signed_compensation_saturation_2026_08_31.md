# Suzuki canonical signed-compensation saturation (2026-08-31)

## Qualifying advance

Discharged the exact signed linear-admission premise left by `mem:research/suzuki_transition_core_linear_compensation_rigidity_2026_08_31` for the coefficient-faithful Suzuki atomic-before-continuous source.

Let
- `A_N = unitRieszCoherentPrimeOutgoingCharge N`,
- `G_N = suzukiNaturalApertureCompletedLowerHardyAmplitude N`,
- `C_N = suzukiNaturalApertureTransitionCoreCauchyEnergy N`,
- `E_N = suzukiTransitionCoreAlignedGammaCompletedEnergy N`,
- `K_N = C_N - E_N`.

Closed unconditionally in Lean:
1. `G_N / A_N -> 0`.
2. `E_N / C_N -> 0`.
3. `K_N / C_N -> 1`.
4. Eventually `n / 576 <= K_(8n)`.
5. `C_N - K_N = E_N` exactly.
6. RH iff the canonically signed-corrected transition core is eventually bounded.

Thus the actual coefficient-faithful signed correction supplies the mandatory linear compensation forced by the prior no-go. Remaining source burden is sharply isolated:
`E_N = o(C_N)` is unconditional; upgrading to `E_N = O(1)` is exactly equivalent to RH. Further correction-scale optimization cannot close this branch.

## Proof idea

Internal corpus PNT/de la Vallée Poussin gives
`q(h)=exp(-h/2)*criticalMellinNormalizedChebyshevError h -> 0`.
Prove `q` globally bounded (negative half-line exactly -1, compact positive interval via corpus error bound, tail via convergence). Rewrite the normalized causal resolvent as
`∫ exp(-3t/2) q(h-t) dt`; dominated convergence makes it vanish. Corpus source identities then yield completed outgoing charge/`sqrt N -> 0`, prime outgoing charge/`sqrt N -> 1/3`, bounded corrections yield completed Suzuki amplitude/`sqrt N -> 0`, hence `G_N/A_N -> 0`. Exact aligned-energy identity gives `E_N/C_N=(G_N/A_N)^2`. Combine `K_N/C_N -> 1` with `C_(8n) >= n/288` to obtain the exact `n/576` admission threshold.

## RH chain

Canonical signed admission -> corrected core equals aligned residual `E_N` -> eventual boundedness iff RH -> shared completed Suzuki source feeds HB/FZZ-P/RBH/PW-B.

## Files

- Lean: `formal/GaloisForLFunctions/RHTower/SuzukiCanonicalSignedCompensationSaturation.lean`
- Umbrella import: `formal/GaloisForLFunctions/RHTower.lean`
- Formalized card: `docs/drafts/pipeline/3-formalized/suzuki-canonical-signed-compensation-saturation.md`

Frontier map remained read-only.

## Principal theorem names

- `tendsto_exp_neg_half_mul_criticalMellinChebyshevResolventSource_atTop_zero`
- `tendsto_suzukiCompletedAmplitude_div_primeOutgoingCharge_atTop_zero`
- `tendsto_suzukiAlignedEnergy_div_transitionCore_atTop_zero`
- `tendsto_suzukiTransitionCoreCanonicalSignedCorrection_div_core_atTop_one`
- `eventually_linear_le_suzukiTransitionCoreCanonicalSignedCorrection_eight_mul`
- `suzukiTransitionCore_sub_canonicalSignedCorrection_eq_alignedEnergy`
- `riemannHypothesis_iff_suzukiCanonicalSignedCorrectedTransitionCoreEventuallyBounded`

## Audits

- Direct Lean check passed.
- Targeted build passed: 13732/13732.
- Five capstones use only `propext`, `Classical.choice`, `Quot.sound`.
- Formal lint reports no issue in this module and sees it reachable. Global lint remains red due unrelated unwired shared-tree modules `HedenmalmCriticalFeatureFirstOrderWindingReduction` and `HedenmalmCriticalFeaturePoleGammaVerticalFTC`.
