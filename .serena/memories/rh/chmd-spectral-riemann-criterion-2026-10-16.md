# CHMD: spectral Riemann criterion (2026-10-16) — RH ⟺ no primitive bound state above 1/2

RH goal ACTIVE. Contribution 6 of this lane. STATUS row MUST-1552.
Card: docs/drafts/pipeline/3-formalized/chmd-spectral-riemann-criterion-2026-10-16.md.
Module `RHTower/CHMDSpectralRiemannCriterion` (ns RHTower.CHMDPolar), 21 declarations, standard axioms, wired.

## Theorems (unconditional)
- `PrimitiveGraph p := ⟪p.val.fst, oneL⟫ = 0`; `primitiveGraph_compactLift_iff : ↔ phiDoobCoshMass v = 0`.
- `sourceEnergy_nonneg_of_rh : RH → ∀ p primitive, 0 ≤ sourceEnergy p` (density via the correction map
  `q ↦ q − (ℓ q / ℓ q₀) q₀`, `mem_closure_image` + `closure_minimal`); `riemannHypothesis_of_primitive_energy` (converse,
  from corpus `riemannHypothesis_iff_forall_phiDoobCoshMass_zero_dirichlet_poincare`).
- `ResolventHalfBound := ∀ w, ⟪w,oneL⟫ = 0 → ⟪Rw,w⟫ ≤ ½‖w‖²`; `riemannHypothesis_iff_resolventHalfBound`.
- `inner_resolvent_sq_le` (Cauchy–Schwarz for ⟪R·,·⟫ via `discrim_le_zero`);
  `resolventHalfBound_of_no_primitive_bound_state` (sup of numerical range on primitive unit sphere → approximate
  eigenvectors via `‖Rw‖² ≤ M⟪Rw,w⟫` → weak-limit primitive eigenvector `exists_primitive_eigenvector_of_approx_eigen_above_half`).
- **`riemannHypothesis_iff_no_primitive_bound_state : RH ↔ ∀ μ w, 1/2 < μ → ⟪w,oneL⟫ = 0 → R w = μ • w → w = 0`**;
  **`not_riemannHypothesis_iff_exists_primitive_bound_state`**.

## Spectral picture (complete, all Lean): σ(R) ⊆ [0,1]; σ_ess ⊆ [0,1/2], 1/2 ∈ σ_ess (MUST-1544/1546/1548);
σ(R) ∩ (1/2,1] pure point, finitely degenerate, finitely many above 1/2+ε (MUST-1551); RH ⟺ none of it in 1^⊥ (MUST-1552).

## Next
Birman–Schwinger count of primitive bound states vs nonreal Xi orbits (corpus has `CHMDFullSpectralNullspace`,
`fourierKernel_memLp` zero modes in L²(μ) — candidates for explicit eigenvectors? not yet checked); min–max stability.

## Lean traps
- `Set.Nonempty (f '' s)` needs the double anonymous constructor `⟨_, ⟨w, hw, rfl⟩⟩`.
- `lt_inv_mul_iff₀` (not `inv_mul_lt_iff₀'`) for `a < c⁻¹ * b`.
- `simp only [not_forall, not_le] at h` replaces deprecated `push_neg`.
- `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)` for positivity of a bump integral.
