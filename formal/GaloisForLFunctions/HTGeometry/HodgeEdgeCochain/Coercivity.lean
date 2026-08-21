import GaloisForLFunctions.HTGeometry.TernaryFormationDualityHodge
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Hodge coercivity on the divergence-free edge-cochain space

This file formalises §2 of Boudourides, *Hodge Coercivity and Global Dynamics in Two-Field
Edge-Cochain Systems with MHD-Type Cancellation* (arXiv:2608.19360).

Let `C⁰ → C¹ → C²` be a finite two-step cochain complex of real inner-product spaces with
coboundaries `d₀`, `d₁` and `d₁ ∘ d₀ = 0`.  The divergence-free edge space is `V = ker d₀*`, the
degree-one Hodge Laplacian is `Δ₁ = d₀ d₀* + d₁* d₁`, and the harmonic space is
`H¹ = ker Δ₁ = ker d₁ ∩ ker d₀*`.

## Main results

* `inner_hodgeLaplacian_self_of_mem_divFree` — equation (1): `⟨Δ₁ v, v⟩ = ‖d₁ v‖²` on `V`.
* `hodgeLaplacian_mem_divFree`, `starProjection_divFree_hodgeLaplacian` — Lemma 1: `V` is
  `Δ₁`-invariant and `P Δ₁ = Δ₁ P`.
* `hodge_coercive_iff_harmonic_eq_bot` — **Theorem 1**, the Hodge coercivity criterion: the
  Poincaré-type estimate `⟨Δ₁ v, v⟩ ≥ λ ‖v‖²` holds on all of `V` for some `λ > 0` if and only
  if the harmonic space is trivial.
* `exists_pos_coercive_on_divFreeComplement` — the unconditional companion: the estimate always
  holds on `V₀ = V ∩ (H¹)ᗮ`, with the sharp constant `λ₊` attained
  (`exists_attained_coercive_on_divFreeComplement`).

The compactness input is isolated as `exists_pos_forall_mem_smul_norm_sq_le`, a reusable statement
about continuous `2`-homogeneous functions that are positive off the origin of a subspace.
-/

open Set Metric
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry.HodgeEdgeCochain

/-! ## A reusable compactness lemma -/

section Homogeneous

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A continuous `2`-homogeneous function vanishes at the origin. -/
theorem eq_zero_of_homogeneous {q : E → ℝ}
    (hhom : ∀ (c : ℝ) (v : E), q (c • v) = c ^ 2 * q v) : q 0 = 0 := by
  have h := hhom 0 0
  simpa using h

/-- The unit sphere of a subspace of a finite-dimensional space is compact. -/
theorem isCompact_sphere_inter_submodule (W : Submodule ℝ E) :
    IsCompact {v : E | v ∈ W ∧ ‖v‖ = 1} := by
  have hset : {v : E | v ∈ W ∧ ‖v‖ = 1} = (W : Set E) ∩ Metric.sphere (0 : E) 1 := by
    ext v
    simp
  rw [hset]
  exact (isCompact_sphere (0 : E) 1).inter_left W.closed_of_finiteDimensional

/-- **Uniform positivity from pointwise positivity.**  A continuous `2`-homogeneous function that
is strictly positive on the nonzero vectors of a subspace `W` of a finite-dimensional space
dominates a positive multiple of `‖·‖²` on all of `W`.  This is the compactness step behind the
Hodge coercivity criterion. -/
theorem exists_pos_forall_mem_smul_norm_sq_le (W : Submodule ℝ E) {q : E → ℝ}
    (hq : Continuous q) (hhom : ∀ (c : ℝ) (v : E), q (c • v) = c ^ 2 * q v)
    (hpos : ∀ v ∈ W, v ≠ 0 → 0 < q v) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ v ∈ W, lam * ‖v‖ ^ 2 ≤ q v := by
  classical
  have hq0 : q 0 = 0 := eq_zero_of_homogeneous hhom
  set S : Set E := {v : E | v ∈ W ∧ ‖v‖ = 1} with hS
  have hSc : IsCompact S := isCompact_sphere_inter_submodule W
  -- Normalising a nonzero vector of `W` lands in `S`.
  have hnorm : ∀ v ∈ W, v ≠ 0 → ‖v‖⁻¹ • v ∈ S := by
    intro v hv hne
    refine ⟨W.smul_mem _ hv, ?_⟩
    rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)
  rcases S.eq_empty_or_nonempty with hE | hNe
  · refine ⟨1, one_pos, fun v hv => ?_⟩
    have hv0 : v = 0 := by
      by_contra hne
      have := hnorm v hv hne
      rw [hE] at this
      exact this
    simp [hv0, hq0]
  · obtain ⟨v₀, hv₀S, hmin⟩ := hSc.exists_isMinOn hNe hq.continuousOn
    have hv₀ne : v₀ ≠ 0 := by
      intro h
      have : ‖v₀‖ = 1 := hv₀S.2
      rw [h] at this
      simp at this
    refine ⟨q v₀, hpos v₀ hv₀S.1 hv₀ne, fun v hv => ?_⟩
    rcases eq_or_ne v 0 with rfl | hne
    · simp [hq0]
    · have hnv : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hne
      have hmem := hnorm v hv hne
      have hle : q v₀ ≤ q (‖v‖⁻¹ • v) := hmin hmem
      rw [hhom ‖v‖⁻¹ v] at hle
      have hsq : (‖v‖⁻¹) ^ 2 = (‖v‖ ^ 2)⁻¹ := by
        rw [inv_pow]
      rw [hsq] at hle
      have h2 : (0 : ℝ) < ‖v‖ ^ 2 := by positivity
      calc q v₀ * ‖v‖ ^ 2 ≤ ((‖v‖ ^ 2)⁻¹ * q v) * ‖v‖ ^ 2 := by
            exact mul_le_mul_of_nonneg_right hle (le_of_lt h2)
        _ = q v := by field_simp

/-- The sharp form of `exists_pos_forall_mem_smul_norm_sq_le`: on a nontrivial subspace the optimal
constant is attained on the unit sphere.  This is the variational characterisation
`λ₊ = min_{0 ≠ v ∈ W} ⟨Δ₁ v, v⟩ / ‖v‖²` of the paper. -/
theorem exists_attained_forall_mem_smul_norm_sq_le (W : Submodule ℝ E) {q : E → ℝ}
    (hq : Continuous q) (hhom : ∀ (c : ℝ) (v : E), q (c • v) = c ^ 2 * q v)
    (hpos : ∀ v ∈ W, v ≠ 0 → 0 < q v) (hW : W ≠ ⊥) :
    ∃ lam : ℝ, 0 < lam ∧ (∀ v ∈ W, lam * ‖v‖ ^ 2 ≤ q v) ∧
      ∃ v ∈ W, ‖v‖ = 1 ∧ q v = lam := by
  classical
  have hq0 : q 0 = 0 := eq_zero_of_homogeneous hhom
  set S : Set E := {v : E | v ∈ W ∧ ‖v‖ = 1} with hS
  have hSc : IsCompact S := isCompact_sphere_inter_submodule W
  have hnorm : ∀ v ∈ W, v ≠ 0 → ‖v‖⁻¹ • v ∈ S := by
    intro v hv hne
    refine ⟨W.smul_mem _ hv, ?_⟩
    rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)
  have hNe : S.Nonempty := by
    obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp hW
    exact ⟨‖w‖⁻¹ • w, hnorm w hwW hw0⟩
  obtain ⟨v₀, hv₀S, hmin⟩ := hSc.exists_isMinOn hNe hq.continuousOn
  have hv₀ne : v₀ ≠ 0 := by
    intro h
    have : ‖v₀‖ = 1 := hv₀S.2
    rw [h] at this
    simp at this
  refine ⟨q v₀, hpos v₀ hv₀S.1 hv₀ne, fun v hv => ?_, v₀, hv₀S.1, hv₀S.2, rfl⟩
  rcases eq_or_ne v 0 with rfl | hne
  · simp [hq0]
  · have hnv : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hne
    have hmem := hnorm v hv hne
    have hle : q v₀ ≤ q (‖v‖⁻¹ • v) := hmin hmem
    rw [hhom ‖v‖⁻¹ v, inv_pow] at hle
    have h2 : (0 : ℝ) < ‖v‖ ^ 2 := by positivity
    calc q v₀ * ‖v‖ ^ 2 ≤ ((‖v‖ ^ 2)⁻¹ * q v) * ‖v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hle (le_of_lt h2)
      _ = q v := by field_simp

end Homogeneous

/-! ## The edge-cochain phase space -/

section Complex

variable {C0 C1 C2 : Type*}
  [NormedAddCommGroup C0] [InnerProductSpace ℝ C0] [FiniteDimensional ℝ C0]
  [NormedAddCommGroup C1] [InnerProductSpace ℝ C1] [FiniteDimensional ℝ C1]
  [NormedAddCommGroup C2] [InnerProductSpace ℝ C2] [FiniteDimensional ℝ C2]

/-- The divergence-free edge-cochain space `V = ker d₀*`. -/
noncomputable def divFree (d0 : C0 →ₗ[ℝ] C1) : Submodule ℝ C1 := LinearMap.ker (LinearMap.adjoint d0)

theorem mem_divFree_iff (d0 : C0 →ₗ[ℝ] C1) (v : C1) :
    v ∈ divFree d0 ↔ LinearMap.adjoint d0 v = 0 := Iff.rfl

/-- `V` is the orthogonal complement of the range of `d₀`: the Hodge splitting removes exactly the
gradient component. -/
theorem divFree_eq_orthogonal_range (d0 : C0 →ₗ[ℝ] C1) :
    divFree d0 = (LinearMap.range d0)ᗮ := (LinearMap.orthogonal_range d0).symm

/-- The harmonic 1-cochains `H¹ = ker Δ₁`. -/
noncomputable def harmonic (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) : Submodule ℝ C1 :=
  LinearMap.ker (hodgeLaplacian d0 d1)

/-- Equation (2): `H¹ = ker d₁ ∩ ker d₀*`. -/
theorem harmonic_eq_inf (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) :
    harmonic d0 d1 = LinearMap.ker d1 ⊓ divFree d0 := by
  rw [harmonic, ker_hodgeLaplacian d0 d1, divFree_eq_orthogonal_range]

theorem harmonic_le_divFree (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) :
    harmonic d0 d1 ≤ divFree d0 := by
  rw [harmonic_eq_inf]
  exact inf_le_right

/-- The complementary divergence-free space `V₀ = V ∩ (H¹)ᗮ` of equation (2). -/
noncomputable def divFreeComplement (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) : Submodule ℝ C1 :=
  divFree d0 ⊓ (harmonic d0 d1)ᗮ

theorem divFreeComplement_le_divFree (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) :
    divFreeComplement d0 d1 ≤ divFree d0 := inf_le_left

/-! ### The Laplacian form on `V` -/

/-- The real Laplacian quadratic form is a sum of two squares. -/
theorem inner_hodgeLaplacian_self (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (v : C1) :
    ⟪hodgeLaplacian d0 d1 v, v⟫_ℝ = ‖LinearMap.adjoint d0 v‖ ^ 2 + ‖d1 v‖ ^ 2 := by
  have h := re_inner_hodgeLaplacian_self (𝕜 := ℝ) d0 d1 v
  simpa using h

/-- **Equation (1).**  On the divergence-free space the Laplacian form is `‖d₁ v‖²`. -/
theorem inner_hodgeLaplacian_self_of_mem_divFree (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2)
    {v : C1} (hv : v ∈ divFree d0) :
    ⟪hodgeLaplacian d0 d1 v, v⟫_ℝ = ‖d1 v‖ ^ 2 := by
  rw [inner_hodgeLaplacian_self, (mem_divFree_iff d0 v).mp hv]
  simp

theorem inner_hodgeLaplacian_self_nonneg (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2) (v : C1) :
    0 ≤ ⟪hodgeLaplacian d0 d1 v, v⟫_ℝ := by
  rw [inner_hodgeLaplacian_self]
  positivity

/-- A divergence-free cochain with vanishing Laplacian form is harmonic. -/
theorem mem_harmonic_of_inner_eq_zero (d0 : C0 →ₗ[ℝ] C1) (d1 : C1 →ₗ[ℝ] C2)
    {v : C1} (hv : v ∈ divFree d0) (h : ⟪hodgeLaplacian d0 d1 v, v⟫_ℝ = 0) :
    v ∈ harmonic d0 d1 := by
  rw [inner_hodgeLaplacian_self_of_mem_divFree d0 d1 hv] at h
  have hd1 : d1 v = 0 := by
    have : ‖d1 v‖ = 0 := by nlinarith [norm_nonneg (d1 v)]
    exact norm_eq_zero.mp this
  rw [harmonic_eq_inf]
  exact ⟨hd1, hv⟩

end Complex

end GaloisForLFunctions.HTGeometry.HodgeEdgeCochain
