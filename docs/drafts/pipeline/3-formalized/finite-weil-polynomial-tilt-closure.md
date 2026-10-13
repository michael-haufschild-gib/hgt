# Finite Weil polynomial tilt closure

Status: FORMALIZED — all three native leaves, 17 declaration audits, and dependency checks passed.

## Objective

Prove that every finite target law, including boundary laws with zero weights, is a total-variation limit of degree-at-most-r polynomial tilts of the actual canonical base measure. Keep all final roots unconditional in r, k, and target Q. Preserve partition normalization one along the approximating sequence.

## Local Lean evidence

- `PaperFourierLLogL/Finite/Law.lean`: `Law.mixture`, `mixture_apply`, uniform positivity, and finite-law normalization.
- `PaperFourierLLogL/Finite/Comparison.lean`: TV is half the sum of absolute weight differences; `tv_le_one` and nonnegativity.
- `PaperFourierLawMeasure.lean`: finite atomic probability measures as weighted Dirac sums.
- `WeilLogShiftPolynomialTiltNormalization.lean`: every strictly positive target has a unique normalized polynomial potential with degree below support size.
- Local Mathlib Lean: finite sums and scalar measure operations; reciprocal-natural convergence; conditional supremum bounds.

Corpus search `mixture tv` in HTGeometry returned one eligible declaration (`entropy_le_of_tv`), inspected by name and source context. Exhaustive project Lean source search found no polynomial-tilt closure result and no atomic-mixture TV identity. The corpus's existing measure `tvDist` is specialized to measures on naturals; this proof will state its actual-measure conclusion explicitly as a supremum over all events.

No external sources or mathematical computations.

## Dependency-closed paper proof

Let U be uniform on the r+1 support indices, t_n=1/(n+1), and Q_n=t_n U+(1-t_n)Q.

1. Each Q_n is strictly positive since t_n>0 and U has positive weights. Its finite-law TV distance from Q is exactly t_n TV(U,Q), by factoring Q_n(i)-Q(i)=t_n(U(i)-Q(i)) under absolute values and summing. Thus TV tends to zero.
2. Atomic realization commutes with binary mixtures, by distributing finite weighted Dirac sums. For every event A, the absolute probability discrepancy is exactly t_n times the discrepancy between the U and Q atomic laws. Each probability lies in [0,1], so this discrepancy is at most t_n, uniformly over A.
3. Set p_n to the canonical interpolated log-density polynomial for Q_n. Prior verified realization gives actual base.tilted(p_n)=atomic(Q_n), degree(p_n)<r+1, and partition function one.
4. Substitute this equality into step 2. The supremum over all event discrepancies lies between zero and t_n; reciprocal-natural convergence proves that the actual tilted measures converge in total variation to atomic(Q).
5. Package the explicit sequence with all degree, normalization, and actual-measure convergence statements. This includes target laws that finite real potentials cannot attain exactly.

## Formal artifacts

- `HTGeometry/FiniteLawPositiveApproximation.lean`
- `HTGeometry/AtomicProbabilityMixture.lean`
- `RHTower/WeilLogShiftPolynomialTiltApproximation.lean`

## Verification progress

- Native API scratch passed: 21 API bindings, with exact signatures printed for scalar sums, scalar measures, finite measure values, probability bounds, conditional suprema, and reciprocal convergence.
- `FiniteLawPositiveApproximation` passed with an empty native log.
- `AtomicProbabilityMixture` passed with an empty native log. One namespace collision was corrected: inside `Law`, the measure-level bound must use `MeasureTheory.prob_le_one` explicitly.
- `WeilLogShiftPolynomialTiltApproximation` passed with an empty native log, including actual-measure convergence as a supremum over all events.
- All three new modules are wired into their theorem-area umbrellas.
- Actual-root final native audit passed: all 17 declarations (15 theorems and two definitions) depend only on `propext`, `Classical.choice`, and `Quot.sound`; no residual diagnostics. The final scratch also verifies 35 API bindings.
- Metadata audit passed: three fresh leaf objects, six fresh direct import edges, clean whitespace, and exactly one umbrella import per new leaf.
- Repository lint snapshot: 367 warnings and nine unrelated unreachable modules: `RHTower.PaperWoldPhaseColumn`, `RHTower.PaperWoldWalshDomain`, `RHTower.PaperWoldWalshEnvelope`, `RHTower.PaperWoldWalshFullOperator`, `HTGeometry.DyadicParentBase`, `HTGeometry.WalshPowerCompact`, `HTGeometry.WalshPowerEntries`, `HTGeometry.WalshPowerLevels`, and `HTGeometry.WalshPowerWeights`. No new-module lint errors.
- Final artifacts: `/tmp/hgt-polynomial-tilt-closure-final-audit.lean`, its `.log`, `/tmp/hgt-polynomial-tilt-closure-audit.py`, and `/tmp/hgt-polynomial-tilt-closure-lint.log`.

## Exact new insight

The finite-real-potential obstruction to zero target weights is an attainment boundary, not a closure obstruction. Every target law is a total-variation limit of normalized polynomial potentials of degree at most r. No degree growth, Gaussian regime, or subcritical restriction is required. The construction has exact index-law error `TV(U,Q)/(n+1)` and actual-measure event discrepancy at most `1/(n+1)`, uniformly over every event.

## Subsequent question

Does normalized potential evaluation necessarily diverge at atoms whose target mass tends to zero? For this explicit sequence, a zero target atom gives the candidate exact identity `p_n(x_i)=log(U_i/base_i)-log(n+1)`; a positive target atom should converge to `log(Q_i/base_i)`. Interpolating the zero-atom indicator suggests a unique polynomial direction governing escape to the boundary. Search the corpus and close the paper proof before formalizing these candidates; none is proved in this increment.
