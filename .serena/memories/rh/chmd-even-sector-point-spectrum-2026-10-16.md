# CHMD: even primitive sector criterion and the point spectrum above 1/2 (2026-10-16)

RH goal ACTIVE. Contribution 9 of this lane. STATUS row MUST-1556.
Card: docs/drafts/pipeline/3-formalized/chmd-even-sector-point-spectrum-2026-10-16.md.
Module (ns RHTower.CHMDPolar): `RHTower/CHMDEvenSectorPointSpectrum`; 40 declarations, standard axioms, wired.

## Results (unconditional)
- `reflectMass_oneL : J 1 = 1`, `reflectMass_tanhL : J tanh = −tanh`, `inner_tanhL_eq_zero_of_even`.
- `evenSector := ker (J − id)`, `primitiveSector := (ℝ ∙ oneL)ᗮ`, `evenPrimitiveSector := evenSector ⊓ primitiveSector`;
  all closed and resolvent-invariant (`mem_*`, `isClosed_*`, `resolventInvariant_*`).
- `weilBilin_smul_left/right`; **`weilBilin_constantLift_one : weilBilin q (constantLift 1) = 0`** for every q.
- `evenPrimitivePart p := p − (2⟪Sp,1⟫) • constantLift 1`; **`weilForm_eq_sourceEnergy_evenPrimitivePart`**
  (even p ⇒ Weil form = Doob energy of the even primitive part).
- `re_W_ofReal_nonneg_of_even_energy` (even real tests, via `phiDoobInv` and `weilForm_compactLift`),
  `re_weilFullFunctional_split` (Re W(f,f) = Re W(Re f) + Re W(Im f), copied from corpus mixture identities),
  `re_weilFullFunctional_nonneg_of_even_energy` (complex even tests), `riemannHypothesis_of_evenPrimitive_energy`
  (via `WeilOneSided.riemannHypothesis_iff_positiveOnEvenNonnegCone` + `Finsupp.sum_nonneg`).
- **`riemannHypothesis_iff_no_evenPrimitive_bound_state`**, `not_riemannHypothesis_iff_exists_evenPrimitive_bound_state`,
  **`exists_odd_bound_state_iff_exists_evenPrimitive_bound_state`**.
- `inner_oneL_eq_zero_of_eigenvector (μ ≠ 1)`, `eq_smul_oneL_of_eigen_one`,
  **`riemannHypothesis_iff_point_spectrum_above_half`**: RH ⟺ (no eigenvector with 1/2 < μ ≠ 1) ∧ (R w = w ⇒ w ∈ ℝ·1);
  **`riemannHypothesis_iff_even_point_spectrum_above_half`** (same inside the even sector).

## Picture
Hyperplane-free spectral RH: σ_pp(R) ∩ (1/2, 1] = {1} simple with eigenvector 1 ⟺ RH. Odd and even-primitive sectors
each detect RH; bound states of both parities coexist.

## Next
Lower Birman–Schwinger (off-line zero ⇒ explicit bound state); odd sharp count; even bound states ↔ zero pairs.

## Lean traps
- Do NOT ascribe types to `ae_eq_comp` results or `MemLp.coeFn_toLp _` on `Lp` vectors defined by `toLp`: whnf timeout.
  Use `unfold oneL; exact MemLp.coeFn_toLp _` and `have h3 := ….ae_eq_comp h2` + `simp only [Function.comp_apply] at hx3`.
- Graph inner products: `real_inner_smul_left` does not fire on `⟪a • p, q⟫` for `p q : SourceGraph`; use `inner_smul_graph`.
- `zetaZeroConfig.W`, `EF.weilTest` need `open Zeta23`.
- Submodule names: `Submodule.coe_inf`, `Submodule.mem_inf`, `Submodule.mem_orthogonal_singleton_iff_inner_left`,
  `Submodule.isClosed_orthogonal`; `innerSL_apply` does not exist in this toolchain.
