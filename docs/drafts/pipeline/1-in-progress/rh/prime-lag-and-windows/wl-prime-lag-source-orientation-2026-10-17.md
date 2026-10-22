# WL — prime-lag source orientation

- **ID:** WL-prime-lag-source-orientation-2026-10-17
- **Stage:** 1-in-progress
- **Type:** ROUTE
- **Source:** Read-only current frontier, WL; current local Lean corpus.
- **Statement:** Remove a hard obstruction in the complete prime-lag source, retaining its affine charge and full signed arithmetic remainder.

## Goal

Produce a substantive unconditional source theorem for WL. Improved bounds, new RH receivers, sampling reformulations, and renamed sign targets do not qualify. This pass produced no qualifying contribution; WL remains unresolved. Cross-route qualifying progress stays 2/44 (PM, SZ).

## Plan

1. Inspect the literal prime-lag, curvature, Cayley, and source-comparison results.
2. Conjecture and attack source mechanisms; prove a substantive survivor on paper before Lean.
3. Verify exact declarations and axioms, run final direct source compilation, wire any new modules, and clean owned scratch.

## Constraints

No web, numerical experiments, novelty audit, old research Markdown, frontier edits, added axioms, or unproved analytic premises. One owned foreground Lean process at a time. Preserve concurrent edits; no full or umbrella builds.

## Conjecture ledger

1. **Corrected curvature positivity supplies native lag orientation.** Rejected: `WeilLagDiscretePrimeCurvature.corrected_second_difference` removes the nonlinear logarithmic and full trivial-zero terms. Native curvature has both signs; `WeilLagNativeCurvatureSign.eventually_scaledCurvature_odd_prime_power_sign` identifies them exactly. Positive survivor: literal prime-power recovery, already formalized.
2. **Summable archimedean error may be discarded before Green inversion.** Rejected: `WeilLagCurvatureGreenRegularization.integerLag_centered_prime_green_bound` retains `N * tsum archCurvatureCorrection`. Omitting this changes the affine slope. Positive survivor: full first-moment renormalization and bounded Green remainder, already formalized; another error estimate would not qualify.
3. **Compact phase observations, unitarity, or critical Schatten residue fix the missing orientation.** Rejected: `PaperLagCayleyGreenBoundary` changes one source coordinate without changing compact-quotient observations, yet changes the lag by `δ N / (3 sqrt(N+3))`. Positive survivor: exact compensating affine charge, already formalized. Critical residue also survives this change (`PaperLagCayleyCriticalResidue`).
4. **Relative determinants have not yet recovered the full source.** Rediscovery: `PaperLagCayleyDeterminantReconstruction` already recovers each source coordinate and the original lag from consecutive tail determinants, retaining both affine charges. Reconstruction supplies no new sign.
5. **Strict negative archimedean tail or relative-angle sign supplies arithmetic orientation.** Insufficient: these orient only source-minus-arithmetic; arithmetic is still `Λ(n+3)-1`. Exact negative tail, cubic coefficient `-1/6`, and signed relative-angle tails already exist.
6. **Prime jumps or an unidentified Mertens constant obstruct first-order source transport.** Rediscovery: `MertensConstantAndCesaroIntegerLagBridge.lagBracket_succ_sub_eq` already cancels the jumps exactly. Its source estimates retain the identified Euler constant. Improving these estimates is excluded by the objective.
7. **Centering local Chebyshev error can remove the chord defect.** Rejected: `WeilLagLocalChebyshevChord.lagPrimeChordDefect_eq_centered_local_chebyshevWork` proves invariance under every constant centering. Positive survivor: exact finite signed work after cancellation of the shared infinite tail, already formalized.
8. **Signed Huxley-window means are an available source cancellation mechanism.** Receiver only: `WeilLagPrimeWindowMeanReceiver.riemannHypothesis_iff_forall_primeWindowMean` is already an equivalence. Its proof starts from the required signed mean estimate; it does not establish it.

9. **The Chebyshev endpoint term still prevents an exact tail representation.** Rediscovery: `SuzukiWeilLagTailBridge.sqrt_mul_integerLag_eq_neg_mul_weilLagChebyshevTail_add_arch` already cancels that endpoint. With `T(n) = integral_(n,infinity) (psi(t)-t)/t^2`, the exact numerator is `-n T(n) - log(2 pi) + S(n)`. The missing fact is still orientation of this full signed tail.
10. **Unconditional positive-real lag transform can supply the undamped sign.** Insufficient: `WeilLagFunctionHerglotz` proves the sign at damping at least `13/25`; positivity at every positive damping is already RH-equivalent. No source passage to zero damping was found.
11. **Sharpening the canonical reflected-pair algebra could close that damping gap.** Rediscovery and no-go: completing the square gives `4 a^4 gamma^2 <= X^2(sigma^2-a^2)`, where `X=gamma^2+1/4-a^2`. `WeilLagPairDetection.all_nonneg_iff` already proves this exact boundary. Its off-line quartet passes the fixed damping gate at arbitrary multiplicity and height. Positive survivor: sharp negative-frequency region and necessary radial resolution, already formalized. These are model spectra, not actual zeta zeros.
12. **Clipping to the positive part provides a cancellation mechanism.** Receiver only: subexponential mass of that part is already RH-equivalent (`WeilLagFunctionPositivePart`). Clipping does not establish the required mass law.
13. **Positive weights, reflection symmetry, and bounded single-base samples exclude a non-attained off-line top.** Rejected for abstract configurations by `WeilLagSingleBaseWolffConfiguration`, including symmetric vanishing samples. Its freely chosen positive weights are not zeta's canonical reciprocal weights; no counterexample to the actual source is claimed.
14. **Two incommensurable progressions or countably many one-sided tests fix the abstract obstruction.** Rejected by `WeilLagTwoBaseWolffConfiguration` and `WeilLagCountableChain`. The former gives two-sided bounded samples with sector-positive, all-positive-power-summable weights; the latter gives either one-sided bound along any prescribed countable family. Arithmetic compatibility of these models remains unproved, so this does not retire WL.
15. **Excursion thickness supplies the missing population estimate.** Insufficient: `WeilLagExcursionBlocks` already propagates every high value across a full side of a natural-scale interval. This does not establish an unconditional supply of low-lag points or an exceptional-set budget.
16. **A variance-controlled barycentric schedule produces a sign through averaging.** Receiver only: `WeilLagBarycentricMean.barycentricLagMeanScheme_characterization` already identifies its bounded signed mean with RH. Geometry of the schedule alone does not bound that mean.

No qualifying result. The full signed tail at actual primes, or an arithmetic exclusion of off-line chains with the actual canonical weights, remains open in this pass.

## No-go closure

Route remains live. Every rejected mechanism above has an explicit already-formalized positive survivor or an exact limitation. No new dependency-closed positive survivor was exposed. Do not label the route failed; do not count these existing results as contributions.

## Verification

- Three scratch audits exited 0: curvature/Cayley (14 declarations), arithmetic source (7), spectral/sampling (12). All 33 `#check` and `#print axioms` checks passed. Every reported axiom belongs to `{propext, Classical.choice, Quot.sound}`. Conditional statements remain conditional; these checks do not prove their hypotheses.
- All 18 explicit source-import roots retained their SHA-256 hashes and clean Git status during the audits. No Lean, umbrella, or index edits. No full build or global lint claim.
- Final direct command from `formal/`: `lake --old env lean GaloisForLFunctions/RHTower/PaperLagCayleyDeterminantReconstruction.lean` exited 0 with empty output. Rechecked all 18 source hashes and Git states afterward: unchanged and clean.
- Deleted nine exact owned scratch paths (two search JSON files, three Lean audit files, three audit logs, one manifest); verified all absent. Both searches and all four Lean processes exited. No owned process remains.

Checked declarations, grouped by namespace:

```text
RHTower.IntegerLagCurvature
  corrected_second_difference
  corrected_second_difference_pos_iff
  eventually_scaledCurvature_odd_prime_power_sign
  integerLag_centered_prime_green_bound
  archCurvatureCorrection_tail_neg
  archCurvatureCorrection_cubic_tendsto
RHTower.PaperLagCayley
  summable_source_discrepancy
  relativeAngleTail_neg
  source_from_relative_determinants
  lag_from_relative_determinants
  lagFromPhases_perturbed
  greenFromPhases_affine_compensation
  tendsto_abs_lag_perturbation
  boundary_determinant_separates_constant_critical_residue
GaloisForLFunctions.RHTower
  lagBracket_succ_sub_eq
RHTower
  sqrt_mul_integerLag_eq_neg_mul_weilLagChebyshevTail_add_arch
  lagPrimeChordDefect_eq_local_chebyshevWork
  lagPrimeChordDefect_eq_centered_local_chebyshevWork
  riemannHypothesis_iff_forall_primeWindowMean
  integerLag_upper_excursion_has_height_scaled_block
  barycentricLagMeanScheme_characterization
  re_lagPoleSeries_nonneg
  integral_weilLagFunctionReal_damped_cos_nonneg
  riemannHypothesis_iff_lagPoleSeries_re_nonneg
  riemannHypothesis_iff_lagPositivePart_integral_subexponential
  exists_positive_lag_configuration_vanishing_progression
  exists_symmetric_lag_configuration_vanishing_samples
  exists_two_base_lag_configuration_vanishing
  exists_chain_configuration_countable_bddAbove
  exists_chain_configuration_countable_bddBelow
RHTower.LagPairDetection
  all_nonneg_iff
  offLine_quartet_nonneg
  radial_resolution_of_neg
```

## Log

- 2026-10-17 — Selected previously unworked WL; documented corpus search launched.
- First deep search completed with `partial=false`, no errors, and no useful proposed mechanism. Its proposed ingredient set concerned group exponents and is inapplicable. Coverage is an indexed snapshot, with pending/stale compiler data and background refresh incomplete; no compiled applicability inferred. Narrowed search to the Weil-lag modules.
- Narrowed search returned useful existing curvature, tail, and sampling declarations, but `partial=true`: `filter_and_judge` reported incomplete or malformed local-model JSON. Used the available hits; did not restart the search. Its proposed ingredient set reuses known curvature signs and a conditional prime-lag growth transfer, so does not supply the missing source theorem.
- Started three disjoint scratch audit groups: curvature/Cayley, arithmetic source, and spectral/sampling. No repository Lean edits.
