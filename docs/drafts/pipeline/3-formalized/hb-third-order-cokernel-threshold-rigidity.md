# HB third-order cokernel threshold rigidity

## Status

Paper proof and Lean formalization complete, 2026-08-28. Promoted to stage 3. Frontier map is read-only and remains untouched.

## Route

HB, refining HC45's sharp quantitative burden on missing third-order `++-` Einstein--Teukolsky producer.

## Corpus basis

- HC45 proves aggregate norm budget and sharp one-third lower bound for three actual non-AIME resonant channels.
- `sameRay_iff_norm_add` in current toolchain characterizes equality in complex triangle inequality.
- `HTGeometry.norm_eq_one_of_norm_sum_eq_card` and `HTGeometry.eq_of_sameRay_of_norm_one` provide corpus precedent for equality-case norm rigidity, but no theorem treats HC45's three unequal source channels or exact target value.
- Corpus search found no one-third threshold rigidity or BM/AIME equipartition classification.

## HC46 conjecture

For complex channels `a+b+c=-t`, if all three norms are at most `‖t‖/3`, then every inequality in the nested triangle bound is equality. Strict convexity aligns all channels; equal norms then force

`a = b = c = -t/3`.

Therefore actual BM/AIME incidence has an exact sharp alternative:

- some physical non-AIME channel has resonant norm strictly greater than `‖AIME‖/3`; or
- all three physical projections equal `-AIME/3` exactly.

For nonzero absorbed seed, every channel selected by either branch is a nonzero cokernel class.

## Positive survivor

HC45's constant is rigid, not merely optimal. Failure of strict dominance forces complete phase locking and exact equal partition among charge-orthogonal stationary, second-harmonic, and direct-third-variation channels. Future third-order computation must exhibit either a strict dominant channel or this unique equipartition configuration.

## Bounded novelty audit

Search date: 2026-08-28. Primary-source search covered AIME (`arXiv:2112.11168`), conserved Kerr QNM projections (`arXiv:2210.15935`), nonlinear QNM amplitude extraction (`arXiv:2310.04489`), and parity dependence of quadratic QNMs (`arXiv:2405.10270`). These study nonlinear excitation, projection, amplitude relations, and parity dependence, but bounded search found no three-channel one-third threshold rigidity, exact equipartition alternative, or BM/AIME cokernel classification. This is a bounded no-match finding, not exhaustive literature-wide novelty claim.

## Conjecture loop

- HC46-A: abstract one-third threshold rigidity — proved in Lean scratch.
- HC46-B: strict-dominance/equipartition dichotomy — proved in Lean.
- HC46-C: actual Einstein-channel exact equipartition law — proved in Lean.
- HC46-D: quantitative nonexact strict/equipartition dichotomy — proved in Lean.

## Lean artifact

`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMThirdOrderCokernelThresholdRigidity`

All declarations are closed Lean proofs. No new axioms, `sorry`, `admit`, `opaque`, or `unsafe` declarations are introduced.

## Verification audit

- `lake env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMThirdOrderCokernelThresholdRigidity.lean`: passed.
- `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMThirdOrderCokernelThresholdRigidity`: passed, 12,750 jobs.
- `#print axioms` for all four public theorems: only `propext`, `Classical.choice`, and `Quot.sound`.
- Module wired into `GaloisForLFunctions.RHTower` umbrella; no umbrella build was run.
- Formal lint contains no HC46 error. Global lint remains red only on unrelated pre-existing or concurrently added unreachable owned modules.
