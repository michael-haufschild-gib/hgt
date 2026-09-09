import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

open Matrix
open scoped Matrix
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section


/-- Landau–Lifshitz motion driven by an energy gradient with nonnegative damping. -/
def spinField (m g : Fin 3 → ℝ) (a : ℝ) : Fin 3 → ℝ :=
  m ⨯₃ g + a ^ 2 • (m ⨯₃ (m ⨯₃ g))

/-- Precession and damping are tangent to every centered sphere, without normalization. -/
theorem spinField_tangent (m g : Fin 3 → ℝ) (a : ℝ) :
    m ⬝ᵥ spinField m g a = 0 := by
  simp [spinField, dotProduct_add, dotProduct_smul, dot_self_cross]

/-- The damping power is minus the squared torque. -/
theorem doubleCross_power (m g : Fin 3 → ℝ) :
    g ⬝ᵥ (m ⨯₃ (m ⨯₃ g)) = -((m ⨯₃ g) ⬝ᵥ (m ⨯₃ g)) := by
  rw [cross_cross_eq_smul_sub_smul', dotProduct_sub, dotProduct_smul, dotProduct_smul,
    cross_dot_cross, dotProduct_comm g m]
  ring

/-- Proposition 1's pointwise energy balance, strengthened to arbitrary spin length. -/
theorem spinField_power (m g : Fin 3 → ℝ) (a : ℝ) :
    g ⬝ᵥ spinField m g a = -a ^ 2 * ((m ⨯₃ g) ⬝ᵥ (m ⨯₃ g)) := by
  rw [spinField, dotProduct_add, dotProduct_smul, dot_cross_self, doubleCross_power]
  ring

theorem spinField_power_nonpos (m g : Fin 3 → ℝ) (a : ℝ) :
    g ⬝ᵥ spinField m g a ≤ 0 := by
  rw [spinField_power]
  apply mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg a))
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg ((m ⨯₃ g) i))

/-- Positive regularized damping detects exactly Brown's zero-torque equilibrium. -/
theorem spinField_regularized_lossless_iff (m g : Fin 3 → ℝ) (a : ℝ) :
    g ⬝ᵥ (m ⨯₃ g + (1 + a ^ 2) • (m ⨯₃ (m ⨯₃ g))) = 0 ↔ m ⨯₃ g = 0 := by
  rw [dotProduct_add, dotProduct_smul, dot_cross_self, doubleCross_power, zero_add,
    smul_eq_mul, mul_eq_zero]
  have ha : (1 + a ^ 2 : ℝ) ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg a])
  simp only [ha, false_or, neg_eq_zero, dotProduct_self_eq_zero]

/-- Finite spatial sums retain the exact torque-square dissipation law. -/
theorem spinField_total_power {ι : Type*} [Fintype ι]
    (m g : ι → Fin 3 → ℝ) (a : ι → ℝ) :
    (∑ i, g i ⬝ᵥ spinField (m i) (g i) (a i)) =
      -∑ i, a i ^ 2 * ((m i ⨯₃ g i) ⬝ᵥ (m i ⨯₃ g i)) := by
  simp only [spinField_power, neg_mul, Finset.sum_neg_distrib]

theorem spinField_total_power_nonpos {ι : Type*} [Fintype ι]
    (m g : ι → Fin 3 → ℝ) (a : ι → ℝ) :
    (∑ i, g i ⬝ᵥ spinField (m i) (g i) (a i)) ≤ 0 :=
  Finset.sum_nonpos (fun i _ => spinField_power_nonpos (m i) (g i) (a i))

end
end GaloisForLFunctions.HTGeometry.SchafferExl
