import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # Binary dilation patterns consistent with few forced wire tests -/

open Finset
namespace GaloisForLFunctions.HTGeometry.BlockDilations

/-- If each regular block has a designated costly bit, the number of
patterns paying for at most k such bits has an exponential bound.
A mismatching bit has weight two and a matching bit has weight one. -/
theorem few_matching_patterns {I : Type*} [Fintype I] [DecidableEq I]
    (G : Finset I) (tag : I→Bool) (k : ℕ) :
    let E := (univ : Finset (I→Bool)).filter fun x => (G.filter fun i => x i=tag i).card≤k
    E.card*2^(Fintype.card I-k) ≤ 3^G.card*4^(Fintype.card I-G.card) := by
  classical
  intro E
  let W (i : I) (v : Bool) : ℕ := if ¬(i∈G ∧ v=tag i) then 2 else 1
  have hw (x : I→Bool) : (∏ i, W i (x i))=2^(Fintype.card I-(G.filter fun i => x i=tag i).card) := by
    have he : univ.filter (fun i => ¬(i∈G ∧ x i=tag i))=(G.filter fun i => x i=tag i)ᶜ := by ext; simp
    dsimp only [W]
    rw [←prod_filter,he,prod_const,card_compl]
  have hsum (i : I) : (∑ v : Bool, W i v)=if i∈G then 3 else 4 := by
    by_cases hi : i∈G <;> cases ht : tag i <;> simp [W,Fintype.sum_bool,hi,ht]
  have hprod : (∏ i : I, if i∈G then 3 else (4:ℕ))=3^G.card*4^(Fintype.card I-G.card) := by
    rw [Finset.prod_ite]
    have h₁ : univ.filter (fun i => i∈G)=G := by ext; simp
    have h₂ : univ.filter (fun i => i∉G)=Gᶜ := by ext; simp
    rw [h₁,h₂,prod_const,prod_const,card_compl]
  calc
    _ = ∑ _x ∈ E, 2^(Fintype.card I-k) := by simp
    _ ≤ ∑ x ∈ E, ∏ i, W i (x i) := sum_le_sum fun x hx => by
      have h := (mem_filter.mp hx).2
      rw [hw]
      exact Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
    _ ≤ ∑ x : I→Bool, ∏ i, W i (x i) := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ = _ := by rw [←Fintype.prod_sum]; simp_rw [hsum]; exact hprod

#print axioms few_matching_patterns
end GaloisForLFunctions.HTGeometry.BlockDilations
