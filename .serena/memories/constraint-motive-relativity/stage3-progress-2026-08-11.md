# CMR stage-3 promotion ledger (2026-08-11)

Goal: formalize UNCONDITIONALLY in Lean every card in
`docs/drafts/pipeline/2-fully-proven/constraint-motive-relativity`, then `git mv` it to
`3-formalized/constraint-motive-relativity/` with a `<id>-formalized.md` companion.

## Done (8/18) — all axiom-clean (propext, Classical.choice, Quot.sound only)

| card | modules (all under `formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/`) |
|-|-|
| cofinal-inverse-capacity-vertical-fibre | `CofinalInverseCapacity.lean`, `CofinalInverseCapacityHilbert.lean`, `AugmentationPortCapacity.lean` |
| cofinal-capacity-polar-horizon-moore-penrose | `CapacityPolarHorizon.lean`, `CapacityPolarPortBridge.lean`, `CapacityPolarCountermodels.lean` |
| finite-lattice-direction-capacity-verticality-pontryagin | `LatticeDirectionCapacity.lean`, `LatticePontryaginSplit.lean`, `LatticeDirectionPortLaw.lean`, `SymmetricSquareRoot.lean`, `WeightedCoordinatePort.lean`, `LatticeDirectionRealization.lean`, `CofinalDirectionCountermodel.lean` |
| valuation-coframe-operation-defect-rank-determinant-line | `CoframeAnomalyRank.lean` |
| linear-hyperbolic-double-three-doctrine-nonconservativity | `HyperbolicDoubleNonconservativity.lean` |
| puiseux-cluster-split-one-port-lorentz-exchange | `PuiseuxClusterExchange.lean` |
| weighted-port-capacity-admission-recurrence | `WeightedPortCapacity.lean`, `PortAdmissionCapacity.lean`, `PortRecurrenceJets.lean`, `PrimePortCapacityHierarchy.lean` |
| prime-port-algebraic-continuous-separation | `PrimeAugmentationSymplectic.lean`, `PrimeAugmentationCompletion.lean` |

## Remaining (10)

compact-observer-local-gauge-cofinal-horizon, finite-reporter-admission-hyperbolic-reduction-composition,
gauge-collapse-stratified-observation-density-reconstruction, ghz-coherence-graph-state-and-history-reconstruction,
helson-coefficient-fredholm-crossing-response, kummer-gamma-one-sided-corona-flow-intervention-rigidity,
marked-euler-shell-mellin-gns-ht-recurrence-normalization-wall, marked-mellin-normalization-exchange-response,
prime-gamma-bockstein-rees-event-germ-and-cofinal-normal-nonuniformity, prime-phase-port-recurrence-completion

## Reusable machinery now in the tree

- `SourceL2 P = lp (fun _ : P => ℂ) 2`; `srcBasis`, `srcEmb`, `srcEmb_apply`, `norm_srcEmb_sq`,
  `norm_sq_eq_tsum`, `memℓp_two_iff` (PortAdmissionCapacity).
- `portLin`, `portKer`, `portCL`, `port_admission_iff`, `portKer_topologicalClosure_eq_top`.
- `portOrbit` / `portTrunc` / `tendstoUniformly_portTrunc` / `totallyBounded_range_portOrbit` /
  `portOrbit_recurrent` / `contDiff_portOrbit_iff` / `iteratedDeriv_portOrbit` (PortRecurrenceJets).
- `singleCLM`, `coordCLM` (CLM versions of `lp.single` / coordinate readout).
- `augment`, `augIdeal`, `dualAnnihilator_augIdeal`, `portForm`, `portOrth`, `coisotropic_reduction`.
- `lpEmb P p`, `mem_closure_image_augIdeal` (generic erasure criterion), `augCLM` (ℓ¹ augmentation).
- Corpus reuse: `RHTower.summable_prime_invNatLogSq`, `HTGeometry.summable_log_pow_div_nat_rpow`,
  `Nat.Primes.not_summable_one_div`.

## Hard-won Lean facts (this toolchain)

- `variable (h : P)` is NOT auto-included when used only in a proof body — pass it explicitly.
- `omit [Inst] in` must precede the docstring, not sit between docstring and `theorem`.
- `↥S ⧸ T` fails instance synthesis when `S : Submodule ℂ (P →₀ ℂ)`; ambient quotients are fine.
- `HasDerivAt.sum` returns a Pi-sum function; convert with `Finset.sum_apply` before `exact`.
- `HasFDerivAt.comp_hasDerivAt` needs `.restrictScalars ℝ` on a ℂ-linear CLM.
- New mathlib `tsum` lemmas carry a `SummationFilter`; fully elaborate the hypothesis first
  (`rw [tsum_eq_sum hz]`, not `refine tsum_eq_sum fun ...`).
- `tendsto_tsum_compl_atTop_zero (f)` needs no summability and indexes by `{x // x ∉ s}`.
- Deprecations seen: `push_neg`→`push Not`, `continuous_finset_sum`→`continuous_finsetSum`,
  `Finsupp.finset_sum_apply`→`Finsupp.finsetSum_apply`, `ContinuousLinearMap.smul_apply`→`smul_apply`.
- Umbrella wiring: append `import ...` to `formal/GaloisForLFunctions/HTGeometry.lean` with a
  here-doc, then `lake build <module>` (per-file `lake env lean` cannot see umbrella collisions).
