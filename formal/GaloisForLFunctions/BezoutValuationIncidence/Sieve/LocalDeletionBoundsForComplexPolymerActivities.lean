import GaloisForLFunctions.BezoutValuationIncidence.Sieve.SharpZeroFreeRegionOfAPolymerGas
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Dobrushin bounds for complex activities and arbitrary deletions

The local hypothesis of Proposition 3.1 in arXiv:2611.14167 yields a lower
bound for every negative partition ratio. The exact corner comparison then
bounds the relative change under deletion throughout a complex polydisc.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.BezoutValuationIncidence.Sieve.PolymerGas

variable {ι : Type*} [DecidableEq ι] (G : SimpleGraph ι) [DecidableRel G.Adj]

/-- Total deletion cost and cost of all neighbors present in P. -/
def cost (c : ι → NNReal) (S : Finset ι) : ℝ := ∑ j ∈ S, (c j : ℝ)

def neighborCost (c : ι → NNReal) (P : Finset ι) (i : ι) :=
  cost c (P.filter (G.Adj i))

/-- Dobrushin's local test in terms of an activity radius and vertex costs. -/
def LocalTest (p c : ι → NNReal) (P : Finset ι) : Prop :=
  ∀ i ∈ P, (p i : ℝ)*Real.exp (neighborCost G c P i) ≤ 1-Real.exp (-(c i : ℝ))

private theorem exp_cost_pos (c : ι → NNReal) (S : Finset ι) : 0 < Real.exp (-cost c S) :=
  Real.exp_pos _

/-- Removing any vertex set from the negative partition can cost at most
the exponential of the sum of its assigned costs. -/
theorem negative_deletion (p c : ι → NNReal) (P : Finset ι) (hc : LocalTest G p c P)
    (S T : Finset ι) (hS : S ⊆ P) (hT : T ⊆ S) :
    Real.exp (-cost c (S \ T))*negative G p T ≤ negative G p S := by
  induction S using Finset.strongInductionOn generalizing T with
  | _ S ih =>
    by_cases he : S ⊆ T
    · rw [Subset.antisymm hT he,sdiff_self]
      simp [cost]
    obtain ⟨i,hi,hit⟩ := not_subset.mp he
    let Q := S.erase i
    let C := compatible G i Q
    have hQ : Q ⊂ S := erase_ssubset hi
    have hC : C ⊆ Q := filter_subset _ _
    have hQP := hQ.subset.trans hS
    have hCQ := ih Q hQ C hQP hC
    have hCP := hC.trans hQP
    have posC : 0 < negative G p C := by
      have hh := ih C (hC.trans_ssubset hQ) ∅ hCP (empty_subset _)
      have hlo : Real.exp (-cost c C) ≤ negative G p C := by
        simpa only [sdiff_empty,negative,partition_empty,mul_one] using hh
      exact (exp_cost_pos c C).trans_le hlo
    have hsub : Q \ C ⊆ P.filter (G.Adj i) := by
      intro j hj
      obtain ⟨hjQ,hjC⟩ := mem_sdiff.mp hj
      exact mem_filter.mpr ⟨hQP hjQ,not_not.mp (fun h => hjC (mem_filter.mpr ⟨hjQ,h⟩))⟩
    have hsum : cost c (Q \ C) ≤ neighborCost G c P i :=
      sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => (c j).property
    have he₁ : 0 ≤ 1-Real.exp (-(c i : ℝ)) :=
      sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (c i).property))
    have hlocal : (p i : ℝ) ≤ (1-Real.exp (-(c i : ℝ)))*Real.exp (-cost c (Q \ C)) := by
      calc
        _ ≤ (1-Real.exp (-(c i : ℝ)))/Real.exp (neighborCost G c P i) :=
          (le_div_iff₀ (Real.exp_pos _)).2 (hc i (hS hi))
        _ = (1-Real.exp (-(c i : ℝ)))*Real.exp (-neighborCost G c P i) := by
          rw [Real.exp_neg,div_eq_mul_inv]
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hsum)) he₁
    have hdec := partition_insert G i Q (notMem_erase _ _) (fun j => -(p j : ℝ))
    rw [show insert i Q=S from insert_erase hi] at hdec
    change negative G p S=negative G p Q+(-(p i : ℝ))*negative G p C at hdec
    have step : Real.exp (-(c i : ℝ))*negative G p Q ≤ negative G p S := by
      have h₁ := mul_le_mul_of_nonneg_right hlocal posC.le
      have h₂ := mul_le_mul_of_nonneg_left hCQ he₁
      linarith only [h₁,h₂,hdec]
    have ratio := ih Q hQ T hQP (subset_erase.mpr ⟨hT,hit⟩)
    have hsplit : S \ T = insert i (Q \ T) := by
      ext j
      by_cases h : j=i <;> simp [h,Q,hi,hit,mem_sdiff,mem_erase]
    rw [hsplit,cost,sum_insert (fun hh => (notMem_erase i S) (mem_sdiff.mp hh).1),
      neg_add,Real.exp_add,mul_assoc]
    exact (mul_le_mul_of_nonneg_left ratio (Real.exp_pos _).le).trans step

/-- Uniform distance from zero, valid under independent complex perturbations. -/
theorem complex_lower (p c : ι → NNReal) (P : Finset ι) (hc : LocalTest G p c P)
    (w : ι → ℂ) (hw : ∀ i ∈ P, ‖w i‖ ≤ (p i : ℝ)) :
    Real.exp (-cost c P) ≤ ‖partition G P w‖ := by
  have low (S : Finset ι) (hs : S ⊆ P) : Real.exp (-cost c S) ≤ negative G p S := by
    simpa [negative] using negative_deletion G p c P hc S ∅ hs (empty_subset _)
  exact (low P Subset.rfl).trans (corner_minimum G p P
    (fun S hs => (Real.exp_pos _).trans_le (low S hs)) w hw)

/-- Deleting arbitrary vertices from a complex gas inflates its modulus
by at most the exponential of their total cost. -/
theorem complex_deletion (p c : ι → NNReal) (P : Finset ι) (hc : LocalTest G p c P)
    (w : ι → ℂ) (hw : ∀ i ∈ P, ‖w i‖ ≤ (p i : ℝ)) (S T : Finset ι)
    (hS : S ⊆ P) (hT : T ⊆ S) :
    ‖partition G T w‖ ≤ Real.exp (cost c (S \ T))*‖partition G S w‖ := by
  have hpos (U : Finset ι) (hu : U ⊆ P) : 0 < negative G p U := by
    have h := negative_deletion G p c P hc U ∅ hu (empty_subset _)
    exact (exp_cost_pos c U).trans_le (by simpa [negative] using h)
  have hm := normalized_mono G p P hpos w hw S T hS hT
  rw [div_le_div_iff₀ (hpos T (hT.trans hS)) (hpos S hS)] at hm
  have hh := negative_deletion G p c P hc S T hS hT
  rw [Real.exp_neg,inv_mul_eq_div,div_le_iff₀ (Real.exp_pos _)] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (norm_nonneg (partition G S w))
  apply le_of_mul_le_mul_right (a := negative G p S) _ (hpos S hS)
  exact (hm.trans hmul).trans_eq (by ring)

end GaloisForLFunctions.BezoutValuationIncidence.Sieve.PolymerGas

#print axioms GaloisForLFunctions.BezoutValuationIncidence.Sieve.PolymerGas.negative_deletion
#print axioms GaloisForLFunctions.BezoutValuationIncidence.Sieve.PolymerGas.complex_lower
#print axioms GaloisForLFunctions.BezoutValuationIncidence.Sieve.PolymerGas.complex_deletion
