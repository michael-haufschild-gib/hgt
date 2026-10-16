# EWU minimum sign: attempted, NOT solved

Latest target is unconditional nonnegativity of `ccmRestrictedWeilSourceQuadratic a u.1` for every positive aperture and every `EvenSector.BlindUnitSource a`. Attainment and exact Gamma integral are in `EvenSectorBlindVariationalAttainment`; neither determines sign. See `mem:rh/ewu-energy-completion-purification-2026-10-16`.

This attempt added no Lean theorem. Current card: `docs/drafts/pipeline/1-in-progress/ewu-blind-minimum-sign-2026-10-16.md`. Status remains open. Do not report an obstruction removed or minimum sign established.

Checked mechanisms:
- Squaring the actual real-even profile preserves log zeros but creates positive polar Laplace integral, so is infeasible. Integer compression moves the polar evaluation.
- Existing first-zero/null rigidity needs global Weil positivity or RH; finite-window nonnegativity does not supply it.
- `BlindArchimedeanNodeTwoCertificate.not_blindSymbolSlack_of_nonpos` unconditionally refutes nonnegative Gamma on the larger blind cone. Does NOT refute sign for actual even-polar sources.
- `EvenSectorCompactBoundaryRigidity.exists_full_mixture_strict_descent` preserves traces but not mass/window, so cannot contradict the normalized fixed-window minimum.
- Mellin/cosine-Fourier transport does not provide the required compact-window/log-even-polar admissible variation; no such bridge proved. `CCMGammaSoninNormalForm` is a bounded scattering commutator, not actual unbounded Gamma energy.
- Phi Doob ground-state cancellation is exact but retains a negative mass term and unproved Poincare sign.
- Blindness of f against its integer translates does not make all integer translates pairwise orthogonal: cross-pairings involve nonintegral rational ratios.
- Prime-power folded-symbol estimates retain slack. Shifted positive Gamma forms change objective.

No numerical experiments or web used. Corpus research searches were followed by source checks. Latest symbol searches found BlindUnitSource only in its attainment module; no sign theorem found. No new Lean build/audit necessary since source unchanged. Searches and failed mechanisms are not a mathematical contribution satisfying user request.