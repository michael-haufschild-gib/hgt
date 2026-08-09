# Interfinity geometry — stage-3 formalization progress (2026-08-09)

Goal: formalize all six cards in `docs/drafts/pipeline/2-fully-proven/interfinity-geometry/`
unconditionally in Lean and move them to stage 3.

## Lean area

`formal/GaloisForLFunctions/HTGeometry/InterfinityGeometry/` with sub-umbrella
`HTGeometry/InterfinityGeometry.lean` (imported from `HTGeometry.lean`).
Namespace `GaloisForLFunctions.HTGeometry.Interfinity`.
Card 6 lives in `RHTower/` (arithmetic) and is imported from `RHTower.lean`.

## DONE (all compile, no sorry/axiom)

### Card 1 `stable-primitive-exactness-topology`
`StablePrimitiveExactness.lean`, `StableDeathRegion.lean`, `StableScottRealization.lean`.
`CochainSlice R A B`; `stableBoundary S = map dRes S`; `StableH S`; `OrdinaryH = StableH ⊤`;
`compare`, `toOrdinary`, `dbar_injective`, `range_dbar = ker toOrdinary`, `stable_shortExact`,
`mem_map_d_iff` (three-gate), `ker_compare`, `compareKernelEquiv`, immortality;
exact-slice section (`stableBoundary_top_eq_top`, `dbar_surjective`, `dbarEquiv`);
`deathRegion`, `isUpperSet_deathRegion`, `exactnessTopology`, `upperSet_le_exactnessTopology`,
`SliceEquiv` covariance + `homeomorph`; `exactnessTopology_eq_induced_scott(_range)`,
`exactnessTopology_eq_induced_sierpinski(_range)`, `jointExactnessTopology`,
`specializes_joint_iff`, `inseparable_joint_iff`.
Reuses corpus `HTGeometry/ExactnessFlagProvenanceTopology.lean`.

### Card 6 `arithmetic-three-chart-stable-boundary`
`RHTower/ArithmeticMixedRateStableQuotient.lean`, `RHTower/ArithmeticThreeChartStableBoundary.lean`.
`primeAtTop`, `mixedFilter`, `mixedRatio`, `radialSpace`, `mixedRate`,
`tendsto_mixedRatio_of_base` (base independence), `linearWitness`, `mixedRate_surjective`,
`radialSlice : CochainSlice`, `subsingleton_radialSlice_ordinaryH`,
`mixedRateQuotientEquiv : StableH ≃ₗ ℝ`, `routeRHolonomy`, `soninTorsion`,
`arithmetic_three_chart_identity`, reflection + vanishing iff `Re s = 1/2`.
Reuses `RHTower/PrimeDepthBVWoldCurvedSourceDifferential.lean`.

### Card 5 `terminal-transgression-curvature-flux`
`TerminalTransgression.lean`, `TerminalResidueModels.lean`.
`TerminalDatum 𝕜 M E`, `bianchi`, `radial_coboundary`, `tendsto_radial_primitive`,
`stable_primitive_unique`, `tendsto_residue_curved/flat`,
`residue_eq_zero_of_eventually_commutes`, `tendsto_curvature_flux`, future-ordering laws;
`AffineMonoid`, free-source model on `Monoid.Coprod (Multiplicative ℝ≥0) (FreeMonoid (Fin n))`
with `freeCochain_residue_gen = h j` (universality no-go); parity model with
`parityCochain_residue_involution = 2`, `parityCochain_flux`, `parityCochain_not_isCocycle`.

### Card 4 `terminal-nerve-and-coherent-source-functor`
`CoherentSourceFunctor.lean` (Part I), `GramPhase.lean`, `GramNerve.lean`,
`GramStateSystem.lean`, `GramHornObstruction.lean` (Part II).
Part I: `tendstoLocallyUniformly_exp`, `tendsto_iff_tendstoLocallyUniformly_exp`,
`TendstoWeakStar`, `IsSourceCocycle`, `IsStablePrimitive`, `HasCoherentBoundary`,
`coherent_source_tfae`, `isStablePrimitive_unique`.
Part II: `gramPhase`, `cyclicPhase`, `cyclicPhase_gramGauge`, `cyclicPhase_bianchi`;
`GramNerveDatum`, `nerve : SSet`, `nerveMap` (persistence), `gramDeathRegion`,
`isUpperSet_gramDeathRegion`, `gramDeathRegion_subset_face`, `csInf_face_le_csInf`;
`stateOverlapDatum`, `realized_stateOverlapDatum_iff`; concrete ℂ³ two- and three-periodic
systems: `xRealizes_hornEdgeAB/AC`, `not_xRealizes_fullTriangle`, `yRealizes_fullTriangle`,
`mFull_det = 1/2`, `mFull_isHermitian`, `edge_realizes_iff` (same labelled one-skeleton).

## REMAINING

### Card 2 `spectral-terminal-horizon-model` — plan
* item 3 (observer line / death region arithmetic) is pure real algebra: easy first step.
* item 1: `IntegrableOn (fun s => (exp (-V s) - 1)^2 * s^(β-1)) (Ioo 0 1)` for `β > -2`;
  cocycle `b_{V+W} = b_V + T_V b_W` pointwise; Hilbert coboundary iff `β > 0`
  (η must be a.e. 1; `1 ∈ H_β` iff `β > 0`).
* item 2: finite-part functional `etaA c a h` (three branches `a>0`, `-1<a<0`, `a=0`);
  identity `etaA (e^{-V·}h) − etaA h = c ∫₀¹ (e^{-Vs}−1) h(s) s^{a-1} ds`;
  continuity as an explicit seminorm bound; stability iff `a > 0`.
* item 4: fixed subspace `= ℂ δ₀`.  Needs (i) smooth division by `(e^{-Vs}−1)/s`
  (nonvanishing on `[0,1]`), (ii) Hadamard `h s = h 0 + s·r s` with `r` smooth.
* item 4 asymptotics: needs `Γ(a) = ∫₀^∞ (e^{-t}−1) t^{a-1} dt` for `-1<a<0`
  (prove by parts from `Γ(a) = Γ(a+1)/a`), then `V^a T_V η_a → cΓ(a)δ₀`;
  `a = 0` case uses `∫₀^V (e^{-t}−1)/t dt = −(log V + γ) + o(1)`.
* item 5: complex time, sectorial `γ(a,z) → Γ(a)`, phase slope `∂_θ arg = −a`.

### Card 3 `multi-time-polyhedral-horizon`
Tensor version of card 2: product integrability, admissible/face-stable regions (4),
fixed subspaces (5) forming the Boolean face lattice, tensor finite part (6),
sectorial asymptotics (7), conormal phase (8).

### Then
Update each card's gate `2 → 3`, `git mv` to `3-formalized` with a companion card,
regenerate indexes (`scripts/formal_tools.py index`), run
`scripts/formal_tools.py lint --check-generated`.

## Traps hit
- `IsOpen[t] s` notation is scoped in `Topology` — must `open Topology`.
- `congr 1` on `generateFrom A = generateFrom B` splits the TopologicalSpace structure; prove the
  set equality separately and `rw`.
- defs returning `TopologicalSpace α` need `@[reducible]`.
- `(Multiplicative.toAdd V : ℝ)` forces `V : Multiplicative ℝ`; write
  `((Multiplicative.toAdd V : ℝ≥0) : ℝ)`.
- `push_cast` rewrites `((Real.exp x : ℝ) : ℂ)` to `Complex.exp`; use `Complex.ofReal_mul`.
- `abs_add` → `abs_add_le`; `div_le_div_iff` → `div_le_div_iff₀`;
  `norm_sq_eq_inner` → `norm_sq_eq_re_inner`; `continuous_finset_sum` → `continuous_finsetSum`.
- `decide` fails on goals with free variables — `revert x; decide`.
- `Type u` morphisms are now bundled (`TypeCat.Hom`): build functors to `Type u` with `↾f`
  and prove `map_id`/`map_comp`/`naturality` by `ext p <;> rfl`.
- `fin_cases s` yields `⟨0, ⋯⟩` which blocks `rw` with lemmas stated at `0`; use
  `revert x; decide`-style case lemmas (`x = 0 ∨ x = 1`) and `rcases … with rfl | rfl`.
