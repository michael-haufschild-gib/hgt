# CHMD: reflection symmetry and the odd-sector RH criterion (2026-10-16)

RH goal ACTIVE. Contribution 8 of this lane. STATUS row MUST-1555.
Card: docs/drafts/pipeline/3-formalized/chmd-odd-sector-criterion-2026-10-16.md.
Modules (ns RHTower.CHMDPolar): `RHTower/CHMDReflectionSymmetry`, `RHTower/CHMDOddSectorCriterion`; 62 declarations, standard axioms, wired.

## Results (unconditional)
- `measurePreserving_withDensity_of_invariant` (generic: σ preserving μ and fixing the density w preserves μ.withDensity w).
- `measurePreserving_neg_mass : MeasurePreserving (fun x => -x) massMeasure massMeasure`.
- `edgeReflect (t,x) := (t, -x-t)`; `left_edgeReflect : left (σ e) = -right e`, `right_edgeReflect`;
  `measurePreserving_edgeReflect_edge : MeasurePreserving edgeReflect edgeMeasure edgeMeasure` (skew product on archBase,
  fiberwise `x ↦ -x - log n` on each primeMeasure, `Measure.map_add`, `Measure.map_sum`).
- `reflectMass : MassSpace →ₗᵢ MassSpace` (= `Lp.compMeasurePreservingₗᵢ`), `reflectGraph : SourceGraph → SourceGraph`
  (`(f,e) ↦ (f∘neg, −e∘σ)`), `reflectGraphₗᵢ`, involutions, `inner_reflectGraph`, `reflectGraph_fst : (Jp).fst = J p.fst`.
- **`resolvent_reflectMass : resolvent (reflectMass w) = reflectMass (resolvent w)`** (via `rieszLift_unique`).
- `reflectGraph_compactLift : J (compactLift v) = compactLift (v ∘ neg)`.
- Generic dictionary for closed R-invariant `V : Submodule`: `half_bound_on_of_energy`, `energy_nonneg_on_of_half_bound`,
  `exists_eigenvector_mem_of_approx_eigen_above_half` (weak limit stays in V via `Submodule.orthogonal_orthogonal`),
  `half_bound_on_of_no_eigenvector` (numerical-range sup argument).
- `oddSector := ker (reflectMass + id)`, closed, R-invariant; `compactLift_fst_mem_oddSector`; `oddPart_compactLift`;
  `sourceEnergy_nonneg_of_rh_odd` (density via odd projection); **`riemannHypothesis_iff_no_odd_bound_state`**,
  **`not_riemannHypothesis_iff_exists_odd_bound_state`**; `oddPart_eigenvector`, `evenPart_eigenvector`;
  `exists_odd_bound_state_of_primitive_bound_state`.

## Picture
RH ⟺ no odd bound state of R above 1/2 (odd sector is pole-free). Combined with MUST-1551/1553: odd bound states finitely
degenerate, locally finite, ≤ 2·#off-line zeros.

## Next
Even-primitive criterion (corpus lacks an even Dirichlet–Poincaré statement; maybe derive from zero-side parity);
odd Birman–Schwinger with sharp constant; explicit odd trial functions from deep zeros (corpus `sinhTest`).

## Lean traps
- `Set.indicator` goals after `simp only [Set.indicator, Set.mem_preimage]` leave `if x ∈ σ⁻¹' s` vs `if σ x ∈ s`;
  use `by_cases` + `Set.indicator_of_mem`/`Set.indicator_of_notMem`.
- `WeilExcess.riemannKernelReal_neg` needs the literal `-(…)` form: rewrite `-a - b = -(a + b)` first.
- `fun_prop` does not know `continuous_riemannKernelReal`; give explicit continuity terms.
- `Measure.map_map` with `measurable_prodMk_left` (not `measurable_const.prodMk measurable_id`, which yields `(c, id a)`).
- `Continuous.const_smul` needs the scalar given explicitly `(1/2 : ℝ)` after a `show` with the lambda form.
