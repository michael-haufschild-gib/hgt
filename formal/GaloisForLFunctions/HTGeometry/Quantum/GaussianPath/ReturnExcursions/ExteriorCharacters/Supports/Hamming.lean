import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # Counting small supports in a family of energy subsets -/

open Finset
open scoped symmDiff
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A translate of a Hamming ball contains at most the exponential moment
of its radius, including when the candidate subsets have fixed cardinality. -/
theorem small_support_count (F : Finset (Finset I)) (S : Finset I) (r : ℕ) :
    ((F.filter fun T => (S ∆ T).card≤r).card:ℝ)≤2^r*(3/2)^Fintype.card I := by
  let g (T : Finset I) := (1/2:ℝ)^(S ∆ T).card
  let B := F.filter fun T => (S ∆ T).card≤r
  have hmass : (∑ T, g T)=(3/2:ℝ)^Fintype.card I := by
    let e := (symmDiff_right_involutive S).toPerm _
    have hh := Equiv.sum_comp e (fun T : Finset I => (1/2:ℝ)^T.card)
    calc
      _ = ∑ T : Finset I, (1/2:ℝ)^T.card := hh
      _ = _ := by
        simpa only [powerset_univ,one_pow,mul_one,card_univ,show (1/2:ℝ)+1=3/2 by norm_num] using
          sum_pow_mul_eq_add_pow (1/2:ℝ) 1 (univ : Finset I)
  have hterm (T) (hT : T∈B) : (1:ℝ)≤2^r*g T := by
    dsimp only [g]
    rw [one_div,inv_pow,←div_eq_mul_inv,le_div_iff₀ (by positivity),one_mul]
    exact pow_le_pow_right₀ (by norm_num) (mem_filter.mp hT).2
  change (B.card:ℝ)≤_
  calc
    _ = ∑ T ∈ B, (1:ℝ) := by simp
    _ ≤ ∑ T ∈ B, 2^r*g T := sum_le_sum hterm
    _ ≤ ∑ T, 2^r*g T := sum_le_sum_of_subset_of_nonneg (subset_univ B)
      (fun _ _ _ => mul_nonneg (by positivity) (pow_nonneg (by norm_num : (0:ℝ)≤1/2) _))
    _ = _ := by rw [←mul_sum,hmass]

#print axioms small_support_count
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters
