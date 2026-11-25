import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.MonomialWeights

/-! # Real and integer characters away from two closing levels -/

open Finset
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Extend weights on the free levels to a balanced action by subtracting
their sum at the reference level j. The other closing level i has weight zero. -/
def anchoredWeight (i j : I) (m : Outside i j→ℝ) (k : I) : ℝ :=
  ∑ l : Outside i j, m l*((if k=l.val then 1 else 0)-(if k=j then 1 else 0))

theorem anchored_balance (i j : I) (m : Outside i j→ℝ) : ∑ l, anchoredWeight i j m l=0 := by
  unfold anchoredWeight
  rw [sum_comm]
  simp only [←mul_sum,sum_sub_distrib,sum_ite_eq',mem_univ,if_true,sub_self,mul_zero,sum_const_zero]

theorem anchored_outside (i j : I) (m : Outside i j→ℝ) (l : Outside i j) :
    anchoredWeight i j m l.val=m l := by
  simp [anchoredWeight,l.property.2,Subtype.val_inj,mul_ite]

theorem anchored_action (i j : I) (m : Outside i j→ℝ) (E : I→ℝ) :
    normalizedAction (anchoredWeight i j m) E i j=∑ l : Outside i j, m l*((E l.val-E j)/(E i-E j)) := by
  unfold normalizedAction
  have he : ∑ k, anchoredWeight i j m k*E k=∑ l : Outside i j, m l*(E l.val-E j) := by
    simp only [anchoredWeight,sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro l _
    simp only [mul_assoc,←mul_sum,sub_mul,ite_mul,one_mul,zero_mul,sum_sub_distrib,sum_ite_eq',mem_univ,if_true]
  rw [he,sum_div]
  exact sum_congr rfl fun _ _ => mul_div_assoc ..

#print axioms anchored_action
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics
