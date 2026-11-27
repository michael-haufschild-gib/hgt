import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Coefficients
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Powers

/-! # Testing energy reflection at half the number of integer temperatures -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half

open Finset Real
open _root_.HTGeometry (finiteGibbsPartition)

variable {I : Type*} [Fintype I]

def meanEnergy (E : I → ℝ) := (∑ i, E i)/(Fintype.card I : ℝ)
def centered (E : I → ℝ) (i : I) := E i-meanEnergy E
def weight (E : I → ℝ) (i : I) := exp (-E i)

def HeatTests (E : I → ℝ) (k : ℕ) := ∀ j : ℕ, 1 ≤ j → j ≤ k →
  finiteGibbsPartition (j : ℝ) E = finiteGibbsPartition (-(j : ℝ)) E

theorem sum_centered (E : I → ℝ) : ∑ i, centered E i = 0 := by
  rcases isEmpty_or_nonempty I with he | hn
  · letI := he
    simp only [univ_eq_empty,sum_empty]
  · letI := hn
    have hp : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [centered,meanEnergy,sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul]
    field_simp
    ring

theorem centered_eq_of_sum_zero {E : I → ℝ} (h : ∑ i, E i=0) : centered E=E := by
  funext i
  simp only [centered,meanEnergy,h,zero_div,sub_zero]

theorem reflects_iff_centered_pair (E : I → ℝ) : Reflects E ↔ PairsAt (centered E) 0 := by
  constructor
  · rintro ⟨d,R,he⟩
    refine ⟨R,fun i => ?_⟩
    letI : Nonempty I := ⟨i⟩
    have hn : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have total := sum_congr (s₁ := univ) rfl (fun j _ => he j)
    rw [sum_add_distrib,Equiv.sum_comp R E,sum_const,card_univ,nsmul_eq_mul] at total
    have avg : meanEnergy E+meanEnergy E=d := by
      rw [meanEnergy,← add_div,div_eq_iff hn,mul_comm]
      exact total
    unfold centered
    linarith only [he i,avg]
  · rintro ⟨R,he⟩
    refine ⟨meanEnergy E+meanEnergy E,R,fun x => ?_⟩
    have hh := he x
    unfold centered at hh
    linarith only [hh]

theorem weight_product {E : I → ℝ} (h : ∑ i, E i=0) : ∏ i, weight E i = 1 := by
  simp only [weight,← Real.exp_sum,sum_neg_distrib,h,neg_zero,exp_zero]

theorem partition_negative (E : I → ℝ) (t : ℝ) :
    finiteGibbsPartition (-t) E = finiteGibbsPartition t (fun i => -E i) := by
  simp only [finiteGibbsPartition,neg_neg,mul_neg,neg_mul]

theorem heat_iff_weights (E : I → ℝ) (k : ℕ) :
    HeatTests E k ↔ Agrees (weight E) (fun i => (weight E i)⁻¹) k := by
  have weights : weight E = fun i => (exp (E i))⁻¹ := funext fun i => exp_neg (E i)
  simp only [HeatTests,Agrees,weights,partition_negative E,partition_moment,neg_neg,exp_neg,inv_inv]

omit [Fintype I] in
theorem pair_iff_weights (E : I → ℝ) :
    PairsAt E 0 ↔ Matches (weight E) (fun i => (weight E i)⁻¹) := by
  constructor <;> rintro ⟨R,h⟩ <;> refine ⟨R,fun i => ?_⟩
  · have e : -E i=E (R i) := by linarith only [h i]
    change exp (-E i)=(exp (-E (R i)))⁻¹
    rw [exp_neg (E (R i)),inv_inv,e]
  · have hh := h i
    change exp (-E i)=(exp (-E (R i)))⁻¹ at hh
    rw [exp_neg (E (R i)),inv_inv] at hh
    linarith only [Real.exp_injective hh]

/-- Agreement through the half cutoff already forces a permutation pairing every centered
energy with its negative. The mean is the only possible reflection center for a nonempty list. -/
theorem centered_heat_iff_reflects (E : I → ℝ) :
    HeatTests (centered E) (cutoff (Fintype.card I)) ↔ Reflects E := by
  rw [reflects_iff_centered_pair,pair_iff_weights,reciprocal_matches_iff _ (weight_product (sum_centered E)),heat_iff_weights]

#print axioms reflects_iff_centered_pair
#print axioms heat_iff_weights
#print axioms centered_heat_iff_reflects

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half
