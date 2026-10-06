import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Real.Basic

/-!
# No coordinate-free residual promoter

Let `V` be a real vector space of dimension at least two, with `GL(V)` acting on covectors by
`α ↦ α ∘ g⁻¹`.  **Theorem 2.1** of the residual-transduction law: a map
`τ : V* ∖ {0} → V` with `τ(α ∘ g⁻¹) = g τ(α)` for every `g ∈ GL(V)` vanishes identically, with no
regularity assumed on `τ`.

For `α ≠ 0` choose `u` with `α(u) = 1` and a nonzero `c ∈ ker α`.  The shear
`x ↦ x + α(x) c` and the map `x ↦ 2x - α(x) u` (identity on `ℝu`, doubling on `ker α`) preserve `α`,
so both fix `τ(α)`; the shear forces `α(τ(α)) = 0` and the doubling then forces `τ(α) = 0`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ResidualTransduction

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The shear `x ↦ x + α(x) c` for `c ∈ ker α`, an automorphism preserving `α`. -/
def shear (α : Module.Dual ℝ V) (c : V) (hc : α c = 0) : V ≃ₗ[ℝ] V where
  toFun x := x + α x • c
  invFun x := x - α x • c
  map_add' x y := by
    rw [map_add, add_smul]
    abel
  map_smul' a x := by
    rw [map_smul, smul_eq_mul, RingHom.id_apply, smul_add, mul_smul]
  left_inv x := by
    simp only [map_add, map_smul, hc, smul_eq_mul, mul_zero, add_zero, add_sub_cancel_right]
  right_inv x := by
    simp only [map_sub, map_smul, hc, smul_eq_mul, mul_zero, sub_zero, sub_add_cancel]

/-- The map `x ↦ 2x - α(x) u` for `α(u) = 1`: the identity on `ℝu`, doubling on `ker α`. -/
def doubling (α : Module.Dual ℝ V) (u : V) (hu : α u = 1) : V ≃ₗ[ℝ] V where
  toFun x := (2 : ℝ) • x - α x • u
  invFun x := (2 : ℝ)⁻¹ • (x + α x • u)
  map_add' x y := by
    rw [map_add, add_smul, smul_add]
    abel
  map_smul' a x := by
    rw [map_smul, smul_eq_mul, RingHom.id_apply, smul_sub, smul_comm a (2 : ℝ), mul_smul]
  left_inv x := by
    simp only [map_sub, map_smul, hu, smul_eq_mul, mul_one]
    rw [show (2 : ℝ) * α x - α x = α x by ring, sub_add_cancel, smul_smul,
      inv_mul_cancel₀ (two_ne_zero), one_smul]
  right_inv x := by
    simp only [map_smul, map_add, hu, smul_eq_mul, mul_one, smul_add, smul_smul]
    rw [show (2 : ℝ) * 2⁻¹ = 1 by norm_num, one_smul, show (2 : ℝ) * (2⁻¹ * α x) = α x by ring,
      show (2 : ℝ)⁻¹ * α x + 2⁻¹ * α x = α x by ring, add_sub_cancel_right]

theorem dual_comp_shear (α : Module.Dual ℝ V) (c : V) (hc : α c = 0) :
    α ∘ₗ ((shear α c hc).symm : V →ₗ[ℝ] V) = α := by
  ext x
  change α (x - α x • c) = α x
  rw [map_sub, map_smul, hc, smul_zero, sub_zero]

theorem dual_comp_doubling (α : Module.Dual ℝ V) (u : V) (hu : α u = 1) :
    α ∘ₗ ((doubling α u hu).symm : V →ₗ[ℝ] V) = α := by
  ext x
  change α ((2 : ℝ)⁻¹ • (x + α x • u)) = α x
  rw [map_smul, map_add, map_smul, hu, smul_eq_mul, smul_eq_mul, mul_one]
  ring

/-- **Theorem 2.1, `(LRT.3)`–`(LRT.7)`**: in dimension at least two, a residual promoter that is
natural under all of `GL(V)` vanishes on every nonzero covector. -/
theorem promoter_eq_zero [FiniteDimensional ℝ V] (hV : 2 ≤ Module.finrank ℝ V)
    (τ : Module.Dual ℝ V → V)
    (hτ : ∀ (g : V ≃ₗ[ℝ] V) (α : Module.Dual ℝ V), α ≠ 0 →
      τ (α ∘ₗ (g.symm : V →ₗ[ℝ] V)) = g (τ α))
    (α : Module.Dual ℝ V) (hα : α ≠ 0) : τ α = 0 := by
  -- a vector `u` with `α u = 1`
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, α u₀ ≠ 0 := by
    by_contra! h
    exact hα (LinearMap.ext h)
  set u : V := (α u₀)⁻¹ • u₀
  have hu : α u = 1 := by
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hu₀]
  -- a nonzero vector `c ∈ ker α`
  obtain ⟨c, hc, hc0⟩ : ∃ c, α c = 0 ∧ c ≠ 0 := by
    have hker : 1 ≤ Module.finrank ℝ (LinearMap.ker α) := by
      have h := LinearMap.finrank_range_add_finrank_ker α
      have hr : Module.finrank ℝ (LinearMap.range α) ≤ 1 := by
        calc Module.finrank ℝ (LinearMap.range α) ≤ Module.finrank ℝ ℝ :=
              Submodule.finrank_le _
          _ = 1 := Module.finrank_self ℝ
      omega
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := LinearMap.ker α) (by
      intro h
      rw [h, finrank_bot] at hker
      omega)
    exact ⟨c, hc, hc0⟩
  -- the shear fixes `τ α`, so `α (τ α) = 0`
  have h1 := hτ (shear α c hc) α hα
  rw [dual_comp_shear] at h1
  have hατ : α (τ α) = 0 := by
    have : α (τ α) • c = 0 := by
      have h1' : τ α = τ α + α (τ α) • c := h1
      have := congrArg (fun x => x - τ α) h1'
      simpa using this.symm
    exact (smul_eq_zero.1 this).resolve_right hc0
  -- the doubling fixes `τ α`, so `τ α = 0`
  have h2 := hτ (doubling α u hu) α hα
  rw [dual_comp_doubling] at h2
  have h2' : τ α = (2 : ℝ) • τ α - α (τ α) • u := h2
  rw [hατ, zero_smul, sub_zero, two_smul] at h2'
  calc τ α = τ α + τ α - τ α := by abel
    _ = τ α - τ α := by rw [← h2']
    _ = 0 := sub_self _

/-- **Corollary 2.2**: a natural promoter is the zero rule on all nonzero covectors; no
regularity hypothesis on `τ` is used. -/
theorem natural_promoter_trivial [FiniteDimensional ℝ V] (hV : 2 ≤ Module.finrank ℝ V)
    (τ : Module.Dual ℝ V → V)
    (hτ : ∀ (g : V ≃ₗ[ℝ] V) (α : Module.Dual ℝ V), α ≠ 0 →
      τ (α ∘ₗ (g.symm : V →ₗ[ℝ] V)) = g (τ α)) :
    ∀ α : Module.Dual ℝ V, α ≠ 0 → τ α = 0 :=
  fun α hα => promoter_eq_zero hV τ hτ α hα

end GaloisForLFunctions.HTGeometry.ResidualTransduction
