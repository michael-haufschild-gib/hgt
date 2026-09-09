import GaloisForLFunctions.HTGeometry.FiniteRegularGeneratorCost
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Counting forces growth of the all-word generator comparison cost

Padding by the identity embeds every cost-k sublevel set into words of exact
length k on at most five letters. Counting this set gives a lower bound for
the full squared-cost sum. A bound on the constructed Reynolds comparison
constant therefore forces an explicit bound on the finite group cardinality.
This concerns the all-word comparison recipe, not an optimal spectral gap.
-/

open scoped BigOperators Pointwise
namespace GaloisForLFunctions.HTGeometry.FiniteRegularGeneratorCost
noncomputable section
variable {G : Type*} [Group G]
local instance : DecidableEq G := Classical.decEq G

/-- Identity plus the two generators and their inverses; padding permits exact-length balls. -/
def alphabet (s t : G) : Finset G := by
  classical
  exact {1,s,t,s⁻¹,t⁻¹}

theorem alphabet_inv (s t : G) : (alphabet s t)⁻¹=alphabet s t := by
  classical
  ext g
  simp only [Finset.mem_inv',alphabet,Finset.mem_insert,Finset.mem_singleton]
  simp only [inv_eq_iff_eq_inv,inv_inv,inv_one]
  tauto

theorem generated_mem_power (s t : G) {g : G} {n : ℕ} (h : GeneratedCost s t g n) :
    g ∈ (alphabet s t)^n := by
  classical
  induction h with
  | one => simp
  | left => simp [alphabet]
  | right => simp [alphabet]
  | mul ha hb iha ihb =>
    rw [pow_add]
    exact Finset.mul_mem_mul iha ihb
  | inv ha ih =>
    have h := Finset.inv_mem_inv ih
    simpa only [← inv_pow,alphabet_inv] using h

theorem card_alphabet_le (s t : G) : (alphabet s t).card ≤ 5 := by
  classical
  have h1 := Finset.card_insert_le (1:G) ({s,t,s⁻¹,t⁻¹}:Finset G)
  have h2 := Finset.card_insert_le s ({t,s⁻¹,t⁻¹}:Finset G)
  have h3 := Finset.card_insert_le t ({s⁻¹,t⁻¹}:Finset G)
  have h4 := Finset.card_insert_le s⁻¹ ({t⁻¹}:Finset G)
  have h5 : ({t⁻¹}:Finset G).card=1 := Finset.card_singleton _
  change ({1,s,t,s⁻¹,t⁻¹}:Finset G).card ≤ 5
  omega

variable [Fintype G]
variable (s t : G) (hgen : Subgroup.closure ({s,t}:Set G)=⊤)

/-- The exact sublevel set of the least certified generator cost. -/
def costBall (k : ℕ) : Finset G := by
  classical
  exact Finset.univ.filter (fun g => cost s t hgen g ≤ k)

theorem costBall_subset_power (k : ℕ) : costBall s t hgen k ⊆ (alphabet s t)^k := by
  classical
  intro g hg
  have hle : cost s t hgen g ≤ k := (Finset.mem_filter.mp hg).2
  exact Finset.pow_subset_pow_right (by simp [alphabet] : (1:G) ∈ alphabet s t) hle
    (generated_mem_power s t (cost_spec s t hgen g))

/-- Two generators supply at most five-to-the-k elements at certified cost at most k. -/
theorem card_costBall_le (k : ℕ) : (costBall s t hgen k).card ≤ 5^k := by
  calc
    _ ≤ ((alphabet s t)^k).card := Finset.card_le_card (costBall_subset_power s t hgen k)
    _ ≤ (alphabet s t).card^k := Finset.card_pow_le
    _ ≤ _ := Nat.pow_le_pow_left (card_alphabet_le s t) k

/-- Exact counting lower bound for the average squared generator cost. -/
theorem counting_cost_lower (k : ℕ) :
    (k:ℝ)^2*((Fintype.card G:ℝ)-(5:ℝ)^k) ≤
      ∑ g : G, (cost s t hgen g:ℝ)^2 := by
  classical
  let B := costBall s t hgen k
  let R := Finset.univ \ B
  have hr (g : G) (hg : g ∈ R) : k < cost s t hgen g := by
    have hnot := (Finset.mem_sdiff.mp hg).2
    change g ∉ Finset.univ.filter (fun g => cost s t hgen g ≤ k) at hnot
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,not_le] using hnot
  have hsum : (R.card:ℝ)*(k:ℝ)^2 ≤ ∑ g : G, (cost s t hgen g:ℝ)^2 := by
    calc
      _ = ∑ g ∈ R, (k:ℝ)^2 := by simp
      _ ≤ ∑ g ∈ R, (cost s t hgen g:ℝ)^2 := by
        apply Finset.sum_le_sum
        intro g hg
        have hh : (k:ℝ) ≤ (cost s t hgen g:ℝ) := by exact_mod_cast (hr g hg).le
        nlinarith [show (0:ℝ) ≤ (k:ℝ) by positivity]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => sq_nonneg _)
  have hc : (R.card:ℝ)+(B.card:ℝ)=(Fintype.card G:ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
  have hb : (B.card:ℝ) ≤ (5:ℝ)^k := by exact_mod_cast card_costBall_le s t hgen k
  nlinarith [mul_nonneg (sq_nonneg (k:ℝ)) (sub_nonneg.mpr hb)]

/-- A bounded all-word comparison cost forces an explicit bound on group size. -/
theorem card_le_of_comparisonConstant_le (k : ℕ) (hk : 0 < k)
    (hC : comparisonConstant s t hgen ≤ (k:ℝ)^2/2) :
    Fintype.card G ≤ 2*5^k := by
  have hc : 0 < (Fintype.card G:ℝ) := by exact_mod_cast Fintype.card_pos
  have hkR : 0 < (k:ℝ) := by exact_mod_cast hk
  have hs := counting_cost_lower s t hgen k
  have hsum : (∑ g : G, (cost s t hgen g:ℝ)^2)=
      (Fintype.card G:ℝ)*(comparisonConstant s t hgen-1) := by
    unfold comparisonConstant
    rw [add_sub_cancel_left,← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul]
  rw [hsum] at hs
  have hh : (Fintype.card G:ℝ) ≤ 2*(5:ℝ)^k := by
    by_contra h
    have hgt := lt_of_not_ge h
    have hp := mul_pos (sq_pos_of_pos hkR) (sub_pos.mpr hgt)
    nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hC)]
  exact_mod_cast hh

end
end GaloisForLFunctions.HTGeometry.FiniteRegularGeneratorCost
