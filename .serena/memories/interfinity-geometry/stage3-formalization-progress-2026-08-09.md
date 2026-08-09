# Interfinity geometry — stage-3 formalization progress (2026-08-09)

Goal: formalize all six cards in `docs/drafts/pipeline/2-fully-proven/interfinity-geometry/`
unconditionally in Lean and move them to stage 3.

## Lean modules built (all compile, no sorry/axiom)

New area: `formal/GaloisForLFunctions/HTGeometry/InterfinityGeometry/`
(sub-umbrella `HTGeometry/InterfinityGeometry.lean`, imported from `HTGeometry.lean`).
Namespace: `GaloisForLFunctions.HTGeometry.Interfinity`.

### Card 1 `stable-primitive-exactness-topology` — DONE
- `StablePrimitiveExactness.lean`: `CochainSlice R A B`; `stableBoundary S = map dRes S`;
  `StableH S`; `OrdinaryH = StableH ⊤`; `compare`, `toOrdinary`, `dbar`, `dbar_injective`,
  `range_dbar = ker toOrdinary`, `stable_shortExact`, `mem_map_d_iff` (three-gate criterion),
  `ker_compare`, `compareKernelEquiv`, `compare_shortExact`, immortality; exact-slice section
  (`stableBoundary_top_eq_top`, `toOrdinary_eq_zero`, `dbar_surjective`, `dbarEquiv`).
- `StableDeathRegion.lean`: `profile`, `deathRegion`, `deathRegion_d`,
  `isUpperSet_deathRegion`, `exactnessTopology`, `upperSet_le_exactnessTopology`,
  `SliceEquiv` covariance + `homeomorph`.
- `StableScottRealization.lean`: `generateFrom_iUnion_eq`,
  `forall_isOpen_generateFrom_of_subbasis`, `induced_pi_sierpinski_eq`,
  `exactnessTopology_eq_induced_scott(_range)`,
  `exactnessTopology_eq_induced_sierpinski(_range)`, `jointExactnessTopology`,
  `specializes_joint_iff`, `inseparable_joint_iff`.
  Reuses corpus `HTGeometry/ExactnessFlagProvenanceTopology.lean`
  (`scott_submodule_eq_generateFrom`).

### Card 6 `arithmetic-three-chart-stable-boundary` — DONE
- `RHTower/ArithmeticMixedRateStableQuotient.lean`: `rectDiff`, `mixedBoundary`,
  `primeAtTop` (comap of coe to ℕ under atTop; NeBot proved), `mixedFilter`, `mixedRatio`,
  `radialSpace` (Submodule), `mixedRate` (LinearMap via limUnder),
  `tendsto_mixedRatio_of_base` (base-prime independence), `linearWitness`,
  `mixedRate_surjective`, `radialSlice : CochainSlice`, `subsingleton_radialSlice_ordinaryH`,
  `stableSpace = ker mixedRate`, `mixedRateQuotientEquiv : StableH ≃ₗ ℝ`.
- `RHTower/ArithmeticThreeChartStableBoundary.lean`: `primeDepthBVWold_witness_triangle`
  (= −log2/8), `routeRHolonomy`, `log_routeRHolonomy`, `soninTorsion`, `sourceChart`,
  `sourceChartClass`, `arithmetic_three_chart_identity`, reflection + vanishing iff Re s = 1/2.
  Reuses `RHTower/PrimeDepthBVWoldCurvedSourceDifferential.lean`.

### Card 5 `terminal-transgression-curvature-flux` — DONE
- `TerminalTransgression.lean`: `TerminalDatum 𝕜 M E` (π, r : ℝ≥0 → M, stableSpace),
  `coboundary`, `IsCocycle`, `curvature`, `IsRadiallyFlat`, `residue`, `bianchi`,
  `curvature_residue`, `radial_coboundary`, `tendsto_radial_primitive`,
  `stable_primitive_unique`, `tendsto_residue_curved`, `tendsto_residue_flat`,
  `residue_eq_zero_of_eventually_commutes`, `tendsto_curvature_flux`,
  `residue_mul_radial`, `residue_radial_mul`.
- `TerminalResidueModels.lean`: `AffineMonoid R E` monoid; free-source model on
  `Monoid.Coprod (Multiplicative ℝ≥0) (FreeMonoid (Fin n))` with
  `freeCochain_residue_gen : residue … (freeGen j) = h j` (universality no-go);
  parity model on `Multiplicative ℝ≥0 × Multiplicative (ZMod 2)` acting on ℂ with
  `parityCochain_residue_involution = 2`, `parityCochain_flux`,
  `parityCochain_not_isCocycle`.

## Remaining
- Card 4 `terminal-nerve-and-coherent-source-functor`
- Card 2 `spectral-terminal-horizon-model`
- Card 3 `multi-time-polyhedral-horizon`
- Then: update each card's gate 2→3, git mv to `3-formalized`, add companion cards,
  regenerate indexes via `scripts/formal_tools.py index`, run lint.

## Traps hit
- `IsOpen[t] s` notation is scoped in `Topology` — must `open Topology`.
- `congr 1` on `generateFrom A = generateFrom B` splits the TopologicalSpace structure;
  prove the set equality separately and `rw`.
- defs returning `TopologicalSpace α` need `@[reducible]`.
- `(Multiplicative.toAdd V : ℝ)` forces `V : Multiplicative ℝ`; write
  `((Multiplicative.toAdd V : ℝ≥0) : ℝ)`.
- `push_cast` rewrites `((Real.exp x : ℝ) : ℂ)` to `Complex.exp`; use `Complex.ofReal_mul`
  and `Real.exp_add` instead.
- `abs_add` → `abs_add_le`; `div_le_div_iff` → `div_le_div_iff₀`.
- `decide` fails on goals with free variables — quantify first
  (`∀ c : ZMod 2, c = 0 ∨ c = 1`).
