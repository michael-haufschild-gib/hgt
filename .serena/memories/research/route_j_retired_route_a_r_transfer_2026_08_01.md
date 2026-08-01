# Route J retired: concrete no-go plus Route A/R transfer

Route J (Julia compound-Poisson coherent energy) is **retired as an independent route**. RH is not proved. Closure obeys survivor ownership rule:

- Every concrete Julia coherent-energy/principal-relative implementation audited is unconditionally closed.
- The widest representation-free bounded negative-excursion capacity existential is exactly Route A's eventual lower-floor condition and hence RH. Its reverse witness is the squared negative part of the target source and is explicitly representation theatre, not source knowledge.
- The corpus's actual nontrivial completed preprojection construction is the singular Möbius--Gamma source-overlap transport into the continued Xi trace column, followed by the anchored two-point Julia cross-cell. Its nonzero Hermitian capacity is the four-unit Ward boundary Gram, and its missing positivity is exactly Route R's `ContinuedXiWardFourUnitBoundaryLiftLaw ↔ RH`.
- Therefore the abstract survivor is Route A and the explicit completed survivor is Route R. No unowned Route-J survivor remains.

Concrete no-gos:
- unrenormalized bad coherent energy has source-uniform-in-scale lower floor and is unbounded on sixth-power apertures;
- zero-scale de-attenuation restores rank-one coherence;
- post-projection subtraction fails on one node;
- positive channel-linear cancellation kills mixed coupling;
- negative-excursion dominance retains bad diagonal weight at least one;
- actual sixth-power block primes are pure-bad source cells;
- anchored Schur residual fails in source-faithful zero-scale limit;
- endpoint Hilbert--Schmidt dressing has insufficient gain;
- null diagonal in a positive symmetric kernel kills its row/column;
- diagonal-null positive-Julia offdiagonal energy is copositive but grows at least half of (m^4/576-65(\log m)^2) under every zero-scale law;
- exact calibrated Julia--Euler exterior current is antisymmetric and has zero scalar quadratic energy.

Retired cards:
- `docs/drafts/pipeline/5-failed/route-j-principal-relative-julia-current.md`
- `docs/drafts/pipeline/5-failed/route-j-julia-unrenormalized-coherent-energy-budget.md`

Formalized paper:
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/route-j-principal-relative-julia-capacity-no-go.md`

Formal modules:
- `formal/GaloisForLFunctions/HTGeometry/TwoChannelRelativeCapacityNoGo.lean`
- `formal/GaloisForLFunctions/RHTower/CCMFirstClockJuliaPrincipalRelativeNoGo.lean`

Terminal declarations:
- `CCMFirstClockPrincipalRelativeCapacityOnTail`
- `ccmFirstClockPrincipalRelativeCapacityOnTail_iff_eventuallyBoundedBelow`
- `ccmFirstClockPrincipalRelativeCapacityOnTail_iff_rh`
- `ccmFirstClockPrincipalRelativeCapacityOnTail_iff_continuedXiWardFourUnitBoundaryLiftLaw`

Verification 2026-08-01:
direct Lean passed; exact leaf builds only passed; axiom audit found only `propext`, `Classical.choice`, `Quot.sound`; formal index regenerated. Lint had no Route J errors and failed only on unrelated shared-worktree umbrella gaps `DeningerPrimeArithmeticCyclotomicComparison` and `OneDeepFibreBound`. No numerical computation or umbrella/full build used.