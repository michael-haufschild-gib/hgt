import GaloisForLFunctions.HTGeometry.PsdHankelJetVanishing
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The radical of a nonnegative symmetric bilinear form

A nonnegative symmetric bilinear form satisfies the Cauchy–Schwarz inequality, so its zero-energy
vectors form a submodule: the radical.  If a linear operator represents the form, that submodule is
contained in the operator kernel, and every linearly independent family of zero-energy vectors is
therefore a lower bound for the rank of the kernel.

This is the step that turns a Gram computation — "these explicit vectors have zero energy and are
independent" — into a spectral statement about the operator of the form.
-/

open Module

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- Cauchy–Schwarz for a nonnegative symmetric bilinear form. -/
theorem bilinForm_sq_le (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (x y : W) : (B x y) ^ 2 ≤ B x x * B y y := by
  refine symmBilin_sq_le (S := fun u v => B u v) (comb := fun t u v => u + t • v) ?_ hnn x y
  intro t u v
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hsymm v u]
  ring

/-- A zero-energy vector of a nonnegative symmetric form annihilates the whole form. -/
theorem form_pairing_eq_zero_of_diag (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) {x : W} (hx : B x x = 0) (y : W) : B x y = 0 := by
  have h := bilinForm_sq_le B hsymm hnn x y
  rw [hx, zero_mul] at h
  nlinarith [sq_nonneg (B x y)]

/-- The radical of a nonnegative symmetric bilinear form: its zero-energy vectors. -/
def formRadical (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) : Submodule ℝ W where
  carrier := {x | B x x = 0}
  add_mem' := by
    intro x y hx hy
    have hxy : B x y = 0 := form_pairing_eq_zero_of_diag B hsymm hnn hx y
    have hyx : B y x = 0 := by rw [hsymm]; exact hxy
    have hx' : B x x = 0 := hx
    have hy' : B y y = 0 := hy
    show B (x + y) (x + y) = 0
    simp only [map_add, LinearMap.add_apply]
    rw [hx', hy', hxy, hyx]
    ring
  zero_mem' := by
    show B 0 0 = 0
    simp
  smul_mem' := by
    intro c x hx
    have hx' : B x x = 0 := hx
    show B (c • x) (c • x) = 0
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hx']
    ring

theorem mem_formRadical_iff (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (x : W) : x ∈ formRadical B hsymm hnn ↔ B x x = 0 := Iff.rfl

/-- **A zero-energy vector lies in the kernel of any operator representing the form.** -/
theorem eq_zero_of_form_diag_eq_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (B : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x)
    (A : H →ₗ[ℝ] H) (hrep : ∀ x y, B x y = inner ℝ (A x) y) {x : H} (hx : B x x = 0) :
    A x = 0 := by
  have h := form_pairing_eq_zero_of_diag B hsymm hnn hx (A x)
  rw [hrep] at h
  exact inner_self_eq_zero.1 h

/-- **An independent family of zero-energy vectors bounds the rank of the operator kernel.** -/
theorem card_le_rank_ker_of_zero_energy {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (B : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (A : H →ₗ[ℝ] H) (hrep : ∀ x y, B x y = inner ℝ (A x) y)
    {ι : Type*} [Fintype ι] {v : ι → H} (hv : LinearIndependent ℝ v)
    (hzero : ∀ i, B (v i) (v i) = 0) :
    (Fintype.card ι : Cardinal) ≤ Module.rank ℝ (LinearMap.ker A) := by
  have hmem : Submodule.span ℝ (Set.range v) ≤ LinearMap.ker A := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact LinearMap.mem_ker.2 (eq_zero_of_form_diag_eq_zero B hsymm hnn A hrep (hzero i))
  have hfin : Module.Finite ℝ (Submodule.span ℝ (Set.range v)) :=
    Module.Finite.span_of_finite ℝ (Set.finite_range v)
  calc (Fintype.card ι : Cardinal)
      = (Module.finrank ℝ (Submodule.span ℝ (Set.range v)) : Cardinal) := by
        rw [finrank_span_eq_card hv]
    _ = Module.rank ℝ (Submodule.span ℝ (Set.range v)) := Module.finrank_eq_rank _ _
    _ ≤ Module.rank ℝ (LinearMap.ker A) := Submodule.rank_mono hmem

/-! ## Capacity of a unit-source constraint -/

/-- **The capacity law.**  If `ζ` has unit source and represents the form on the source functional,
`B ζ ψ = ρ · v ψ`, then its energy is `ρ` and no vector of unit source has smaller energy. -/
theorem form_capacity (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (v : W →ₗ[ℝ] ℝ) (ζ : W) (ρ : ℝ)
    (hunit : v ζ = 1) (hrep : ∀ ψ, B ζ ψ = ρ * v ψ) :
    B ζ ζ = ρ ∧ ∀ ψ : W, v ψ = 1 → ρ ≤ B ψ ψ := by
  have hζ : B ζ ζ = ρ := by rw [hrep ζ, hunit, mul_one]
  refine ⟨hζ, fun ψ hψ => ?_⟩
  have hd : v (ψ - ζ) = 0 := by
    rw [map_sub, hψ, hunit, sub_self]
  have hcross : B ζ (ψ - ζ) = 0 := by rw [hrep, hd, mul_zero]
  have hexp : B ψ ψ = B ζ ζ + 2 * B ζ (ψ - ζ) + B (ψ - ζ) (ψ - ζ) := by
    have hsplit : ψ = ζ + (ψ - ζ) := by abel
    nth_rewrite 1 [hsplit]
    nth_rewrite 2 [hsplit]
    simp only [map_add, LinearMap.add_apply]
    rw [hsymm (ψ - ζ) ζ]
    ring
  rw [hexp, hζ, hcross]
  have := hnn (ψ - ζ)
  linarith

/-- **The source is orthogonal to the radical when the capacity is nonzero.** -/
theorem source_eq_zero_on_radical (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (v : W →ₗ[ℝ] ℝ) (ζ : W) (ρ : ℝ) (hρ : ρ ≠ 0)
    (hrep : ∀ ψ, B ζ ψ = ρ * v ψ) {k : W} (hk : B k k = 0) : v k = 0 := by
  have h1 : B ζ k = 0 := by
    rw [hsymm]
    exact form_pairing_eq_zero_of_diag B hsymm hnn hk ζ
  rw [hrep k] at h1
  exact (mul_eq_zero.1 h1).resolve_left hρ

/-- **Vanishing capacity puts the normalized source vector in the radical.** -/
theorem mem_formRadical_of_capacity_eq_zero (B : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y, B x y = B y x) (hnn : ∀ x, 0 ≤ B x x) (v : W →ₗ[ℝ] ℝ) (ζ : W)
    (hunit : v ζ = 1) (hrep : ∀ ψ, B ζ ψ = (0 : ℝ) * v ψ) :
    ζ ∈ formRadical B hsymm hnn ∧ v ζ = 1 :=
  ⟨(form_capacity B hsymm hnn v ζ 0 hunit hrep).1, hunit⟩

end

end GaloisForLFunctions.HTGeometry
