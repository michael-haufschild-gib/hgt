import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Heat
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Mixed.Balance

/-! # Centered log probabilities of a particle–hole tensor product -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Observation

open Finset Real _root_.HTGeometry

variable {I J : Type*} [Fintype I] [Fintype J]

def information {X : Type*} (P : X → ℝ) (x : X) := -log (P x)

theorem centered_matches {E : I → ℝ} {F : J → ℝ} (h : Matches E F) :
    Matches (centered E) (centered F) := by
  obtain ⟨e,he⟩ := h
  have mass := Fintype.sum_equiv e E F he
  exact ⟨e,fun x => by rw [centered,centered,he,meanEnergy,meanEnergy,mass,Fintype.card_congr e]⟩

theorem gibbs_information (E : I → ℝ) (t : ℝ) (x : I) :
    information (finiteGibbsStateWeight t E) x = t*E x+log (finiteGibbsPartition t E) := by
  letI : Nonempty I := ⟨x⟩
  rw [information,finiteGibbsStateWeight,log_div (exp_pos _).ne' (finiteGibbsPartition_pos _ _).ne',log_exp]
  ring

theorem information_matches {E : I → ℝ} {F : J → ℝ} (h : Matches E F) (t : ℝ) :
    Matches (centered (information (finiteGibbsStateWeight t E))) (centered (information (finiteGibbsStateWeight t F))) := by
  apply centered_matches
  obtain ⟨e,he⟩ := h
  exact ⟨e,fun x => by rw [gibbs_information,gibbs_information,he x,partition_congr (show Matches E F from ⟨e,he⟩)]⟩

private theorem remove_shift {E : I → ℝ} (h : ∑ i, E i=0) (b : ℝ) :
    centered (fun i => E i+b) = E := by
  funext i
  letI : Nonempty I := ⟨i⟩
  have hn : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [centered,meanEnergy,sum_add_distrib,h,zero_add,sum_const,card_univ,nsmul_eq_mul]
  field_simp
  ring

/-- A zero-sum single-coordinate reading has zero sum on tuples, also when no states exist. -/
private theorem copy_sum_zero {E : I → ℝ} (h : ∑ i, E i=0) (k : ℕ) :
    ∑ x, copyEnergy E k x=0 := by
  unfold copyEnergy
  rw [sum_comm]
  apply sum_eq_zero
  intro i _
  let f (j : Fin k) (x : I) := if i=j then E x else 1
  have eq := Fintype.prod_sum f
  have z : (∏ j, ∑ x, f j x)=0 := prod_eq_zero (mem_univ i) (by simpa only [f,if_pos rfl] using h)
  rw [z] at eq
  simpa only [f,prod_ite_eq,mem_univ,if_true] using eq.symm

theorem sum_mixed_zero {E : I → ℝ} (h : ∑ i, E i=0) (k l : ℕ) :
    ∑ z, Mixed.mixedEnergy E 0 k l z=0 := by
  have neg : (∑ i, (0-E i))=0 := by simp only [zero_sub,sum_neg_distrib,h,neg_zero]
  simp only [Mixed.mixedEnergy,finiteTensorEnergy,Fintype.sum_prod_type,sum_add_distrib,sum_const,
    card_univ,nsmul_eq_mul,copy_sum_zero neg,add_zero,← mul_sum,copy_sum_zero h,mul_zero]

omit [Fintype I] in
private theorem copy_affine (E : I → ℝ) (a b : ℝ) (k : ℕ) (x : Fin k → I) :
    copyEnergy (fun i => a*E i+b) k x=a*copyEnergy E k x+(k : ℝ)*b := by
  simp only [copyEnergy,sum_add_distrib,← mul_sum,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]

/-- Suppressing the partition constant in the measured log probabilities leaves copies
of the centered single-copy energy and its negative with their full multiplicities. -/
theorem centered_joint_information (E : I → ℝ) (C : ℝ) (k l : ℕ) (t : ℝ) :
    centered (information (finiteGibbsStateWeight t (Mixed.mixedEnergy E C k l))) =
      Mixed.mixedEnergy (fun i => t*centered E i) 0 k l := by
  let A := fun i => t*centered E i
  let M := Mixed.mixedEnergy E C k l
  let D := Mixed.mixedEnergy A 0 k l
  let a := t*meanEnergy E
  let b := t*(C-meanEnergy E)
  have ha : A = fun i => t*E i+(-a) := by funext i; unfold A centered a; ring
  have hb : (fun i => 0-A i) = fun i => t*(C-E i)+(-b) := by funext i; unfold A centered b; ring
  have id : information (finiteGibbsStateWeight t M) =
      fun x => D x+((k : ℝ)*a+(l : ℝ)*b+log (finiteGibbsPartition t M)) := by
    funext x
    rw [gibbs_information]
    change t*(copyEnergy E k x.1+copyEnergy (fun i => C-E i) l x.2)+_ =
      (copyEnergy A k x.1+copyEnergy (fun i => 0-A i) l x.2)+_
    rw [hb,ha,copy_affine,copy_affine]
    ring
  have hA : ∑ i, A i=0 := by simp only [A,← mul_sum,sum_centered,mul_zero]
  change centered (information (finiteGibbsStateWeight t M))=D
  rw [id]
  exact remove_shift (sum_mixed_zero hA k l) _

#print axioms sum_mixed_zero
#print axioms centered_joint_information

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Observation
