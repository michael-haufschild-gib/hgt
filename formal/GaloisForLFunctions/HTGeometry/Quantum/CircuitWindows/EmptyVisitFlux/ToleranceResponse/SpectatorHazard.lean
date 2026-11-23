import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-! # First-order spectator loss at the closing endpoints of a scalar arc -/
open Finset
namespace GaloisForLFunctions.HTGeometry.EmptyVisitFlux
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Total interval lost to the two moving endpoints per unit elapsed time. -/
def spectatorLoss (a b z : ℝ) := max 0 (a-z)+max 0 (z-b)

private theorem twice_positive (x : ℝ) : 2*max 0 x=x+|x| := by
  rcases le_total 0 x with h|h
  · rw [max_eq_right h,abs_of_nonneg h]; ring
  · rw [max_eq_left h,abs_of_nonpos h]; ring

private theorem loss_identity (a b z : ℝ) :
    2*spectatorLoss a b z=(a-b)+|a-z|+|b-z| := by
  rw [spectatorLoss,mul_add,twice_positive,twice_positive,abs_sub_comm z b]
  ring

/-- Summing endpoint contributions over each unordered pair counts every
line once for every possible partner. -/
private theorem endpoint_sum (v R : I→ℝ) (h : Function.Injective v) :
    (∑ i, ∑ j, if v j<v i then R i+R j else 0) =
      ((Fintype.card I:ℝ)-1)*(∑ i,R i) := by
  let f (i j : I) := if v j<v i then R i else 0
  let g (i j : I) := if v j<v i then R j else 0
  have he (i j : I) : (if v j<v i then R i+R j else 0)=f i j+g i j := by
    by_cases hc : v j<v i <;> simp only [f,g,hc,ite_true,ite_false,add_zero]
  have hswap : (∑ i, ∑ j, g i j)=∑ i, ∑ j, g j i := sum_comm
  have hpair (i j : I) : f i j+g j i=R i-(if i=j then R i else 0) := by
    rcases eq_or_ne i j with rfl|hne
    · simp [f,g]
    rcases lt_or_gt_of_ne (h.ne hne) with h₁|h₁
    · simp [f,g,hne,h₁,h₁.asymm]
    · simp [f,g,hne,h₁,h₁.asymm]
  simp only [he,sum_add_distrib]
  rw [hswap,←sum_add_distrib]
  simp only [←sum_add_distrib,hpair,sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,
    sum_ite_eq,mem_univ,if_true,←mul_sum]
  ring

private theorem absolute_pair_sum (v : I→ℝ) :
    (∑ i, ∑ j, |v i-v j|)=2*∑ i, ∑ j,max 0 (v i-v j) := by
  have he (a b : ℝ) : |a-b|=max 0 (a-b)+max 0 (b-a) := by
    rcases le_total a b with h|h
    · rw [abs_of_nonpos (sub_nonpos.mpr h),max_eq_left (sub_nonpos.mpr h),max_eq_right (sub_nonneg.mpr h)]; ring
    · rw [abs_of_nonneg (sub_nonneg.mpr h),max_eq_right (sub_nonneg.mpr h),max_eq_left (sub_nonpos.mpr h),add_zero]
  simp only [he,sum_add_distrib]
  rw [sum_comm (f:=fun i j => max 0 (v j-v i))]
  ring

/-- The flux-weighted initial rate of losing a closing pair is exactly
three halves per spectator for every simple real spectrum. -/
theorem total_spectator_loss (v : I→ℝ) (h : Function.Injective v) :
    2*(∑ i, ∑ j, if v j<v i then
      ∑ k ∈ (univ.erase i).erase j, spectatorLoss (v i) (v j) (v k) else 0) =
      3*((Fintype.card I:ℝ)-2)*(∑ i, ∑ j,max 0 (v i-v j)) := by
  let D := (Fintype.card I:ℝ)
  let R (i : I) := ∑ k, |v i-v k|
  let G (i j : I) := max 0 (v i-v j)
  have hp (i j : I) : 2*(if v j<v i then
        ∑ k ∈ (univ.erase i).erase j, spectatorLoss (v i) (v j) (v k) else 0) =
      (D-4)*G i j+(if v j<v i then R i+R j else 0) := by
    by_cases hg : v j<v i
    · have hne : j≠i := fun he => hg.ne (congrArg v he)
      let A (k : I) := spectatorLoss (v i) (v j) (v k)
      have ht := sum_erase_add _ A (mem_erase.mpr ⟨hne,mem_univ j⟩ : j∈univ.erase i)
      have hi := sum_erase_add univ A (mem_univ i)
      have hu : 2*(∑ k,A k)=D*(v i-v j)+R i+R j := by
        rw [mul_sum]
        simp only [A,loss_identity,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,D,R]
      have hai : A i=v i-v j := by simp only [A,spectatorLoss,sub_self,max_self,zero_add,max_eq_right (sub_nonneg.mpr hg.le)]
      have haj : A j=v i-v j := by simp only [A,spectatorLoss,sub_self,max_self,add_zero,max_eq_right (sub_nonneg.mpr hg.le)]
      change 2*(if v j<v i then ∑ k ∈ (univ.erase i).erase j,A k else 0)=_
      rw [if_pos hg,if_pos hg,show G i j=v i-v j from max_eq_right (sub_nonneg.mpr hg.le)]
      rw [hai] at hi
      rw [haj] at ht
      linarith only [ht,hi,hu]
    · simp only [hg,ite_false,mul_zero,add_zero,G,max_eq_left (sub_nonpos.mpr (le_of_not_gt hg))]
  have hh := congrArg (fun f : I→I→ℝ => ∑ i, ∑ j,f i j) (funext fun i => funext (hp i))
  simp only [sum_add_distrib,←mul_sum] at hh
  rw [endpoint_sum v R h,show (∑ i,R i)=2*(∑ i,∑ j,G i j) from absolute_pair_sum v] at hh
  change 2*_ = 3*(D-2)*(∑ i,∑ j,G i j)
  dsimp only [D] at *
  linarith only [hh]

#print axioms total_spectator_loss
end
end GaloisForLFunctions.HTGeometry.EmptyVisitFlux
