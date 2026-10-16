# CHMD: bound-state inertia / lower Birman–Schwinger bound (2026-10-16)

RH goal ACTIVE. Contribution 10 of this lane. STATUS row MUST-1557.
Card: docs/drafts/pipeline/3-formalized/chmd-bound-state-inertia-2026-10-16.md.
Module (ns RHTower.CHMDPolar): `RHTower/CHMDBoundStateInertia`; 37 declarations, standard axioms, wired, lint passed.

## Results (unconditional)
- `boundStateSpace := (span {w | ∃ μ > 1/2, R w = μ w}).topologicalClosure`; closed, R-invariant; `1 ∈ P`;
  `half_bound_on_orthogonal_boundStateSpace : R ≤ 1/2 on Pᗮ`; **`riemannHypothesis_iff_boundStateSpace_eq_span_oneL`**.
- `sourceEnergy_nonneg_of_inner_resolvent_le`, `half_lt_inner_resolvent_of_energy_neg`, `fst_notMem_orthogonal_of_energy_neg`.
- `inner_compactLift_tanhL : ⟪S(compactLift v), tanhL⟫ = phiDoobSinhMass v`;
  `weilForm_compactLift_eq_sourceEnergy_of_polar` (cosh and sinh masses 0 ⇒ weilForm = E);
  `coshHalfMoment_eq_zero_and_sinhHalfMoment_eq_zero` (ĝ(±i/2) = 0 ⟺ C(g) = S(g) = 0);
  **`sourceEnergy_phiDoobInv_eq_re_W`** (polar-constrained real g: E(lift(g/K)) = Re W(g,g)).
- `paperFT_rePart_imPart_of_exp_real` (+ `_I_div_two`, `_neg_I_div_two`): transforms of Re f, Im f at ±i/2.
- `testSource g` (dif-defined source of lift(g/K)), `testSource_add/smul` (ae proofs), `doubledSource V hV : V →ₗ[ℝ] M × M`.
- **`finrank_le_finrank_boundStateSpace_of_negative_subspace`**: complex polar-constrained V with Re W negative
  definite ⇒ finrank ℂ V ≤ finrank ℝ P (via Ψ : V → P × P and `LinearMap.ker_ne_bot_of_finrank_lt`);
  cardinal version `finrank_le_rank_boundStateSpace_of_negative_subspace`.
- **`weilNegIndex_le_finrank_boundStateSpace`** (ε ≥ 0, any a); **`card_le_finrank_boundStateSpace_add_two`**
  (corpus `zeta_weil_inertia_law` lower half: visible separated deep zero sets T ⇒ |T| ≤ dim P + 2).

## Picture
Bound states above 1/2 are counted from both sides by off-line zeros: weilNegIndex ≤ dim P ≤ (MUST-1553) 2·#offline.

## Next
P finite-dim when off-line set finite (orthogonal eigen-decomposition); sharp multiplicity = zero pairs in window
(corpus upper inertia law); top eigenvalue vs depth δ via sinhTest Rayleigh quotient.

## Lean traps
- `Submodule.orthogonalProjection` is deprecated → `Submodule.orthogonalProjectionOnto`, `..._eq_zero_iff`.
- `HasCompactSupport.smul_left` takes the scalar implicitly (`hgc.smul_left`, no explicit arg).
- `Submodule.ne_bot_iff` takes the submodule explicitly: `(Submodule.ne_bot_iff _).mp`.
- `zeta_W_eq_weilFullFunctional` rewrites need `have hf : ContDiff ℝ 2 (fun x => (g x : ℂ))` with the lambda stated
  explicitly (not `ofRealCLM.contDiff.comp hg` inline: the pattern becomes `⇑ofRealCLM ∘ g`).
- Dimension count over ℝ for a ℂ-subspace V: `Module.finrank_mul_finrank ℝ ℂ V`, `Complex.finrank_real_complex`,
  `Module.Finite.trans ℂ V`, `Module.finrank_prod`; `IsClosed.completeSpace_coe` needs `haveI : IsClosed (↑P)`.
- `field_simp` may close the goal (no trailing `ring`).
