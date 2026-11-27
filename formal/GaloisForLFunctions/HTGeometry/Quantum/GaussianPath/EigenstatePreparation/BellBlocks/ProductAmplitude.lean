import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! # Product-state amplitudes in a basis of maximally entangled pairs -/
open Finset
namespace GaloisForLFunctions.HTGeometry.EigenstatePreparation.BellBlocks
noncomputable section
variable {I : Type*} [Fintype I] [Nonempty I]

/-- In dimension d on either side, a Bell vector pairs each left index
with one right index, with equal amplitudes and arbitrary phases. -/
def productAmplitude (e : I ≃ I) (phase u v : I → ℂ) :=
  (∑ i, phase i*u i*v (e i))/((Real.sqrt (Fintype.card I):ℝ):ℂ)

/-- The squared overlap with any product vector is at most its squared
norm divided by the dimension. The vectors on the two sides may each
be entangled across all of their own spins. -/
theorem product_weight (e : I ≃ I) (phase u v : I → ℂ) (hp : ∀ i, ‖phase i‖=1) :
    (Fintype.card I:ℝ)*‖productAmplitude e phase u v‖^2 ≤
      (∑ i, ‖u i‖^2)*∑ i, ‖v i‖^2 := by
  let z := ∑ i, phase i*u i*v (e i)
  have h : ‖z‖ ≤ ∑ i, ‖u i‖*‖v (e i)‖ := by
    apply (norm_sum_le _ _).trans
    simp only [norm_mul,hp,one_mul,le_refl]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ (fun i => ‖u i‖) (fun i => ‖v (e i)‖)
  rw [Equiv.sum_comp e (fun i => ‖v i‖^2)] at hcs
  have hD : (0:ℝ)<Fintype.card I := by exact_mod_cast Fintype.card_pos (α:=I)
  calc _ = ‖z‖^2 := by
         rw [productAmplitude,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
           div_pow,Real.sq_sqrt hD.le]
         change (Fintype.card I:ℝ)*(‖z‖^2/(Fintype.card I:ℝ))=_
         field_simp
       _ ≤ _ := (pow_le_pow_left₀ (norm_nonneg z) h 2).trans hcs

#print axioms product_weight
end
end GaloisForLFunctions.HTGeometry.EigenstatePreparation.BellBlocks
