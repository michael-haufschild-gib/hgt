# Quadratic tilts: relative entropy and diagonal rigidity

Status: formalized. Sources: local Lean corpus only.

## Conjecture and proof target

For actual finite Weil joint laws at depth `2*(r+1)^2+t r`, compare quadratic tilts with diagonal coefficients `s=a+2*b+d<2` and `S=A+2*B+D<2`. Their KL divergence converges to

`((2-S)/(2-s) - 1 - log ((2-S)/(2-s)))/2`.

This limit vanishes exactly when `s=S`. The sum of the two directional divergences converges to `(s-S)^2/(2*(2-s)*(2-S))`. Thus the three quadratic coefficients collapse to one asymptotic information parameter; different diagonal coefficients retain a positive information separation.

## Dependency-closed paper argument

1. Existing `llr_tilted_right`, `log_rnDeriv_tilted_left_self`, and absolute continuity identify the log likelihood ratio of two tilts as `f-g-log Zf+log Zg` almost everywhere under the first tilt.
2. Every real observable is integrable under each actual finite tilted law. Therefore both finite tilts are equivalent, KL is finite, and its real value is the integral of that exact likelihood ratio.
3. Existing second-moment limits evaluate every quadratic expectation under the first tilt as its diagonal coefficient divided by `4-2*s`.
4. Existing partition limits give `Zs -> sqrt(2/(2-s))>0`. Continuity of logarithm gives the two log-partition limits. Elementary algebra gives the displayed divergence.
5. Local `Real.log_le_sub_one_of_pos` gives nonnegativity; its strict version gives zero exactly at ratio one. Adding the reversed formula cancels logarithms and gives the displayed rational separation.

## Scope and checks

Generic reusable likelihood identities may expose analytic assumptions, but every actual finite-law root discharges them. Final limit roots use only structural subcritical parameter subtypes. No new axioms, numerical experiments, web, external papers, full builds, heartbeat changes, or subagents. Build each changed leaf natively; final scratch audit checks every new declaration and API name. Wire completed leaves into umbrellas; run formal lint and record unrelated failures.

## Working log

- Previous increment closed all mixed moments and actual covariance entries.
- Exhaustive local text search found no KL/relative-entropy theorem in the WeilLogShift family. Existing local theta-cusp likelihood proofs confirm the tilted log-likelihood API. Initial broad local index query returned 20 of 272 candidates; used only for locating dependencies, not as exhaustive novelty evidence.
- Chosen target: actual pairwise KL and exact diagonal rigidity, rather than an abstract Gaussian-only surrogate.

## Proven result

All targets above hold for actual finite tilted laws, with no residual analytic hypotheses. The finite identities and finiteness theorem hold for every natural `r,k` and every real coefficient tuple. Limit theorems use only the two structural subcritical parameter subtypes and arbitrary depth offset `t : Nat -> Nat`.

The positive invariant is the diagonal coefficient: distinct subcritical coefficients have strictly positive limiting relative entropy, while equality is equivalent to convergence of actual ENNReal KL divergence to zero. The symmetric separation is exactly the rational expression stated above. This classifies the asymptotic information retained by all three quadratic coefficients.

## Lean closure

- `HTGeometry/TiltedRelativeEntropy.lean`: six reusable theorems for absolute continuity, likelihood ratios, integrability, likelihood integrals, and real/ENNReal KL identities. The absolute-continuity helper needs no probability-measure assumption; the existing absolute-continuity chain proves this stronger form directly.
- `RHTower/WeilLogShiftQuadraticTiltInformationGeometry.lean`: one entropy definition and five theorems for nonnegativity, strict positivity, zero classification, partition algebra, and symmetric separation. This pure algebra leaf imports only local mathlib `Log.Basic`.
- `RHTower/WeilLogShiftQuadraticTiltEntropy.lean`: five unconditional actual finite-law theorems, including finite KL for every coefficient tuple.
- `RHTower/WeilLogShiftQuadraticTiltEntropyLimit.lean`: five theorems for arbitrary quadratic moments, real/ENNReal KL convergence, the zero-limit iff, and symmetric KL convergence.

All four native leaf checks exited zero with empty logs. The final native scratch audit checked all 22 declarations (21 theorems, one definition) and 28 API `have` checks. Only `propext`, `Classical.choice`, and `Quot.sound` occur; no residual diagnostics. Metadata verified all seven direct dependencies, all seven incoming imports, source/object freshness, unique declaration names, and exact umbrella wiring. Local indexing recovered 22/22 declarations with no markers or partial coverage. Scoped whitespace checks report no errors.

The global formal lint run reports 367 warnings and nine errors outside these leaves: eight unreachable modules (`CCMPolarOddPrimeJumps`, `PaperHeatSliceSource`, `XiCriticalityPortZeros`, `XiSliceOffCentreToeplitzWindow`, `CauchyTakagiApertureSimplicity`, `GaussianPolynomialScaledTails`, `PolyaClassLocalPhase`, `QKrawtchoukCompanionTriangular`) and the existing `sorry` in `CCMPolarOddPrimeJumps.lean:104`. No new leaf is flagged.

Proof-engineering lessons: type the integrable subtraction function explicitly before rewriting an integral sum; provide the Euclidean carrier explicitly in paired probability-measure coercions; factor `4-2*s` as `2*(2-s)` before clearing denominators. An external rebuild temporarily removed `DirichletMeanValueSharp.olean`; its exact live process was observed and left alone until it finished. No duplicate rebuild was started.

Artifacts: `/tmp/hgt-weil-tilt-entropy-{metadata,index-summary,audit-summary}.json`, `/tmp/hgt-weil-tilt-entropy-final-audit.lean`, `/tmp/hgt-weil-tilt-entropy-final-audit.log`, `/tmp/hgt-weil-tilt-entropy-incoming-imports.txt`, and `/tmp/hgt-weil-tilt-entropy-lint.log`. Axiom-output validation handles wrapped lists without rerunning Lean.
