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

end

end GaloisForLFunctions.HTGeometry
