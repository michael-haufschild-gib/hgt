# CTF uniform taper energy and squareful charge mask

User cleared the ongoing research goal, then requested completion of already-started work. Bounded completion is finished; no claim that the significant CTF/RH objective was achieved. Earlier finite-mass results are in `mem:rh/ctf-selberg-coefficient-mass-2026-10-18`.

## Verified leaves

All paths below are relative to `formal/GaloisForLFunctions/RHTower/`.

- `Sieve/LogarithmicHarmonicSampling.lean`: finite log-band harmonic mass ≤ exp(1); a squared inverse-log envelope has uniformly bounded harmonic sampling energy; window mass ≤ 1+log(Y/X).
- `Sieve/CoprimeLogMoebiusHarmonicDifference.lean`: global log-square rate for T(Y)=coprimeLogMoebius 1 Y; uniform finite-set error energy; `exists_sum_sq_coprimeLogMoebius_difference_div_le` bounds the two-cutoff harmonic energy by C(1+log(Y/X)) for every 0<X≤Y and finite cutoff.
- `Sieve/SelbergWeightedConvolutionModel.lean`: exact arbitrary-weight bivariate Selberg convolution into Euler correction and a principal harmonic model.
- `ChronologicalSelbergTaperEnergy.lean`: `exists_selberg_arithmeticCoeff_le_inv_log_span` proves Q_N(arithmeticCoeff M N) ≤ K/(log N-log M), uniformly for 1≤M<N with log span ≥1. The weighted transform is exactly (T(N/q)-T(M/q))/(log N-log M).
- `ChronologicalSquarefulChargeCorrection.lean`: squarefulTailMask N d is the indicator of multiples of four in (floor(N/2),N]. It vanishes below the half cutoff and above N; its nonzero slots have μ(d)=0. Charge ≥1/16 for N≥16. For N≥2 and e>0, multiples coordinates lie in [0,3/e], hence Q_N(mask_N)≤9(1+log N). `selbergTotientDiagonalForm_eq_of_support_le` proves exact cutoff-extension invariance for any supported row; `selberg_squarefulTailMask_le_of_le` transfers the mask bound to larger ambient cutoffs.

## Verification

All five leaves passed direct `lake --old env lean <leaf> -o <leaf olean>` checks without final diagnostics. Four core results from sampling through taper energy and all eleven public squareful-mask theorems passed import-only /tmp axiom audits: exactly `[propext, Classical.choice, Quot.sound]`. The earlier three finite-mass leaves also passed their own checks and axiom audit. All eight leaves occur exactly once in `RHTower.lean`. No full/umbrella build, heartbeat increase, commit, push, or external search was performed. Source checks found no sorry/admit/axiom/opaque/unsafe declarations or heartbeat overrides in the eight leaves. Owned temporary Lean, search JSON, and lint-output files were removed after audit.

Final repository lint exited 1 on unrelated ownership errors: unreachable BiScaleUncertainty.SixthReadoutStability; three unreachable BezoutValuationIncidence leaves (ArbitraryDepthBezoutShellsAndRoutePMSecondLayerProfile, CompensatedHarmonicPredecessorPeakDriftAndDiagonalBudget, PronicPotentialSelfCancellationAndInteriorGradientConservation); package-root research leaf TransHorizonIncidenceMechanics.lean. These supersede the earlier four-error snapshot. No lint error concerns these eight CTF leaves.

## Exact limits / future research

These are finite Selberg results, not chronological signed-remainder control. The CTF origin-window gap remains open. No full corrected unit-row producer, asymptotic feasibility classification, or squareful-mask chronological-norm transfer was implemented. The paper plan repairs charge at inner scale L=2*max(M,16), rather than outer N: this preserves the exact prefix and avoids an unnecessarily large physical scale. Its assembly and physical transfer need their own future proof/formalization; do not treat the mask lemmas as that producer.

Current source/proof record: `docs/drafts/pipeline/1-in-progress/ctf-signed-origin-tail-2026-10-18.md`. Research searches were non-partial but reported background indexing/older coverage; exact applicability was established by the direct Lean checks.