# CMR stage-3 promotion ledger (2026-08-11)

Goal: formalize UNCONDITIONALLY in Lean every card in
`docs/drafts/pipeline/2-fully-proven/constraint-motive-relativity`, then `git mv` it to
`3-formalized/constraint-motive-relativity/` with a `<id>-formalized.md` companion.

## Done (12/18) — all axiom-clean (propext, Classical.choice, Quot.sound only)

| card | modules under `formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/` |
|-|-|
| cofinal-inverse-capacity-vertical-fibre | `CofinalInverseCapacity`, `CofinalInverseCapacityHilbert`, `AugmentationPortCapacity` |
| cofinal-capacity-polar-horizon-moore-penrose | `CapacityPolarHorizon`, `CapacityPolarPortBridge`, `CapacityPolarCountermodels` |
| finite-lattice-direction-capacity-verticality-pontryagin | `LatticeDirectionCapacity`, `LatticePontryaginSplit`, `LatticeDirectionPortLaw`, `SymmetricSquareRoot`, `WeightedCoordinatePort`, `LatticeDirectionRealization`, `CofinalDirectionCountermodel` |
| valuation-coframe-operation-defect-rank-determinant-line | `CoframeAnomalyRank` |
| linear-hyperbolic-double-three-doctrine-nonconservativity | `HyperbolicDoubleNonconservativity` |
| puiseux-cluster-split-one-port-lorentz-exchange | `PuiseuxClusterExchange` |
| weighted-port-capacity-admission-recurrence | `WeightedPortCapacity`, `PortAdmissionCapacity`, `PortRecurrenceJets`, `PrimePortCapacityHierarchy` |
| prime-port-algebraic-continuous-separation | `PrimeAugmentationSymplectic`, `PrimeAugmentationCompletion` |
| prime-phase-port-recurrence-completion | `PrimePhasePortRecurrence` |
| ghz-coherence-graph-state-and-history-reconstruction | `GHZCoherenceGraph` |
| compact-observer-local-gauge-cofinal-horizon | `CompactObserverHorizon` |
| prime-gamma-bockstein-rees-event-germ-and-cofinal-normal-nonuniformity | `PrimeGammaReesEventGerm` |

## Remaining (6)

finite-reporter-admission-hyperbolic-reduction-composition, gauge-collapse-stratified-observation-density-reconstruction,
helson-coefficient-fredholm-crossing-response, kummer-gamma-one-sided-corona-flow-intervention-rigidity,
marked-euler-shell-mellin-gns-ht-recurrence-normalization-wall, marked-mellin-normalization-exchange-response

## Side repairs made to the shared tree (not my cards)

- `HTGeometry/UniformIteratedDerivLimit.lean` — NEW. Supplies
  `contDiff_infty_of_tendstoUniformly_iteratedDeriv` and
  `iteratedDeriv_eq_of_tendstoUniformly_iteratedDeriv`, which `HTGeometry/TestFunctionComplete.lean`
  referenced but which existed nowhere; that module was committed-but-unbuildable and broke the
  whole `GaloisForLFunctions.HTGeometry` umbrella.  Added the import line to TestFunctionComplete.
- `HTGeometry/CompactOperatorBoundedBelow.lean` — generalized `K : E →L[𝕜] E` to `K : E →L[𝕜] F₀`
  in `totallyBounded_closedBall_of_isCompactOperator_of_bounded_below` and
  `finiteDimensional_of_isCompactOperator_of_bounded_below` (only that module used them).

## Reusable machinery now in the tree

- `SourceL2 P = lp (fun _ : P => ℂ) 2`; `srcBasis`, `srcEmb`, `norm_sq_eq_tsum`, `memℓp_two_iff`.
- `wtPort`/`wtIdeal`/`portOrth`/`wtRed`/`coisotropic_reduction_wt` (weighted symplectic port).
- `lpEmb P p`, `mem_closure_image_wtIdeal`, `exists_small_spread_lp/_top`, `wtCLM` (ℓ¹ port).
- `portOrbit`/`portTrunc`/`tendstoUniformly_portTrunc`/`portOrbit_recurrent`/`contDiff_portOrbit_iff`.
- `singleCLM`, `coordCLM`; `obsFloor`, `gram`, `chartSphere` (compact-observer layer).
- `probeGraph`, `walkProd`, `walkSum`, `edgeDiff`, `componentPullback` (graph reconstruction layer).
- `sinhc`, `eventConstant`, `diagCompare` (prime Gamma–Rees layer).
- Corpus reuse: `RHTower.summable_prime_invNatLogSq`, `HTGeometry.summable_log_pow_div_nat_rpow`,
  `GaloisForLFunctions.kronecker_approx`, `GaloisForLFunctions.HTGeometry.finiteDiagonalPhaseOrbit_approx`,
  `finiteDiagonalKrylovVector_linearIndependent`, `finitePhaseLiftEnergy_unbounded`,
  `finiteDimensional_of_isCompactOperator_of_bounded_below`, `Nat.Primes.not_summable_one_div`.

## Hard-won Lean facts (this toolchain)

- `omit [Inst] in` must precede the docstring, never sit between docstring and `theorem`.
- `↥S ⧸ T` fails instance synthesis when `S : Submodule ℂ (P →₀ ℂ)`; ambient quotients are fine.
- `HasDerivAt.sum` returns a Pi-sum function; convert with `Finset.sum_apply` first.
- `HasFDerivAt.comp_hasDerivAt` needs `.restrictScalars ℝ` on a ℂ-linear CLM.
- New mathlib `tsum` lemmas carry a `SummationFilter`; elaborate the hypothesis first.
- `to_additive` fails on recursive defs over `SimpleGraph.Walk` — write both versions.
- Long `lake build` runs exceed the 600 s Bash cap; run them with `run_in_background` and poll.
- Clean up with `pkill -f "lake env lean"` if a run is killed (exit 137 = OOM from parallel leans).
