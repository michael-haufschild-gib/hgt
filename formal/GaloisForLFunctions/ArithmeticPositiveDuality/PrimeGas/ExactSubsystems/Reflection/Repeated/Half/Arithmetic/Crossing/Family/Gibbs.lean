import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Alphabet

/-! # Calibration of a single finite Gibbs probability distribution -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family

open Finset Real
open _root_.HTGeometry (finiteGibbsPartition finiteGibbsStateWeight)

variable {I L : Type*} [Fintype I]

theorem centered_affine (E : I → ℝ) (a b : ℝ) :
    centered (fun i => a*E i+b) = fun i => a*centered E i := by
  funext i
  letI : Nonempty I := ⟨i⟩
  have hn : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [centered,meanEnergy,sum_add_distrib,← mul_sum,sum_const,card_univ,nsmul_eq_mul]
  field_simp
  ring

theorem agrees_affine (E : I → ℝ) (a b u : ℝ) :
    agrees (fun i => a*E i+b) u ↔ agrees E (u*a) := by
  simp only [agrees,centered_affine,finiteGibbsPartition,neg_neg,neg_mul,mul_assoc]

/-- The comparison uses only centered negative logarithms of the entries of one law. -/
def lawOrder (P : I → ℝ) (u : ℝ) := agrees (Observation.information P) u

theorem gibbs_order (E : I → ℝ) (d u : ℝ) :
    lawOrder (finiteGibbsStateWeight d E) u ↔ agrees E (u*d) := by
  have info := funext (Observation.gibbs_information E d)
  rw [lawOrder,info,agrees_affine]

/-- A good alphabet calibration separates zero damping from every asymmetric
finite Gibbs spectrum, regardless of its degeneracies. -/
theorem gibbs_pair (h : L → ℝ) (a : I → L) {r : ℝ} (hr : 0 < r) (good : r ∉ exceptional h) (d : ℝ) :
    let P := finiteGibbsStateWeight d (h ∘ a)
    lawOrder P 1 ∧ lawOrder P r ↔ d=0 ∨ Reflects (h ∘ a) := by
  dsimp only
  rw [gibbs_order,gibbs_order,one_mul]
  exact calibrated h a hr good d

#print axioms gibbs_order
#print axioms gibbs_pair

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family
