import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Recovery from fixed-size subset sums

The incidence Gram matrix of all equally sized subsets has one diagonal
and one off-diagonal coefficient. Its positive diagonal remainder gives
an exact energy decomposition and reconstructs every input coordinate.
-/

open Finset
open scoped BigOperators
namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
variable {k l : ℕ}

/-- All `(k+2)`-subsets of a set of size `k+l+3`. -/
def fixedSubsetRows (k l : ℕ) : Finset (Finset (Fin (k+l+3))) :=
  univ.powersetCard (k+2)

def fixedSubsetSum (v : Fin (k+l+3) → ℝ) (S : Finset (Fin (k+l+3))) : ℝ := ∑ i ∈ S, v i

lemma fixedSubsetRows_single_count (i : Fin (k+l+3)) :
    ((fixedSubsetRows k l).filter (fun S => i ∈ S)).card = (k+l+2).choose (k+1) := by
  have h := card_filter_powersetCard_subset ({i} : Finset (Fin (k+l+3))) univ
    (k+2) (subset_univ _) (by simp)
  simpa [fixedSubsetRows, singleton_subset_iff, Nat.add_assoc] using h

lemma fixedSubsetRows_pair_count (i j : Fin (k+l+3)) (hij : i ≠ j) :
    ((fixedSubsetRows k l).filter (fun S => i ∈ S ∧ j ∈ S)).card = (k+l+1).choose k := by
  have h := card_filter_powersetCard_subset ({i,j} : Finset (Fin (k+l+3))) univ
    (k+2) (subset_univ _) (by simp [hij])
  simpa [fixedSubsetRows, insert_subset_iff, singleton_subset_iff, hij, Nat.add_assoc,
    show k+(l+3)-2 = k+(l+1) by omega] using h

/-- Single-coordinate incidence mass. -/
lemma fixedSubsetRows_sum_indicator (i : Fin (k+l+3)) :
    (∑ S ∈ fixedSubsetRows k l, if i ∈ S then (1 : ℝ) else 0) =
      ((k+l+2).choose (k+1) : ℝ) := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, fixedSubsetRows_single_count]

lemma fixedSubsetRows_sum_pair_indicator (i j : Fin (k+l+3)) (hij : i ≠ j) :
    (∑ S ∈ fixedSubsetRows k l, if i ∈ S ∧ j ∈ S then (1 : ℝ) else 0) =
      ((k+l+1).choose k : ℝ) := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, fixedSubsetRows_pair_count i j hij]

/-- The exact incidence Gram entries, with Pascal's identity separating the identity part. -/
theorem fixedSubsetRows_gram (i j : Fin (k+l+3)) :
    (∑ S ∈ fixedSubsetRows k l,
      (if i ∈ S then (1 : ℝ) else 0) * (if j ∈ S then (1 : ℝ) else 0)) =
      (if i = j then ((k+l+1).choose (k+1) : ℝ) else 0) + ((k+l+1).choose k : ℝ) := by
  have hp : ∀ S : Finset (Fin (k+l+3)),
      (if i ∈ S then (1 : ℝ) else 0) * (if j ∈ S then (1 : ℝ) else 0) =
        if i ∈ S ∧ j ∈ S then 1 else 0 := by
    intro S; split_ifs <;> simp_all
  simp_rw [hp]
  by_cases hij : i = j
  · subst j
    simp only [and_self, ↓reduceIte, fixedSubsetRows_sum_indicator]
    have h := Nat.choose_succ_succ (k+l+1) k
    have hc := congrArg (fun n : ℕ => (n : ℝ)) h
    push_cast at hc
    rw [show (k+l+1).succ = k+l+2 by omega, Nat.succ_eq_add_one] at hc
    exact hc.trans (add_comm _ _)
  · rw [fixedSubsetRows_sum_pair_indicator i j hij, if_neg hij, zero_add]

lemma fixedSubsetSum_eq_indicator (v : Fin (k+l+3) → ℝ) (S : Finset (Fin (k+l+3))) :
    fixedSubsetSum v S = ∑ i, (if i ∈ S then (1 : ℝ) else 0) * v i := by
  simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
  simp [fixedSubsetSum]

/-- Transpose incidence applied to the observed subset sums. -/
def fixedSubsetBackprojection (v : Fin (k+l+3) → ℝ) (i : Fin (k+l+3)) : ℝ :=
  ∑ S ∈ fixedSubsetRows k l, (if i ∈ S then (1 : ℝ) else 0) * fixedSubsetSum v S

/-- Exact normal equation, separating the constant and zero-sum components. -/
theorem fixedSubsetBackprojection_eq (v : Fin (k+l+3) → ℝ) (i : Fin (k+l+3)) :
    fixedSubsetBackprojection v i =
      ((k+l+1).choose (k+1) : ℝ) * v i + ((k+l+1).choose k : ℝ) * ∑ j, v j := by
  unfold fixedSubsetBackprojection
  simp_rw [fixedSubsetSum_eq_indicator, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, fixedSubsetRows_gram, add_mul]
  rw [Finset.sum_add_distrib]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.mul_sum]

/-- Exact observation energy: an isotropic part plus the constant-mode correction. -/
theorem fixedSubsetSum_energy (v : Fin (k+l+3) → ℝ) :
    ∑ S ∈ fixedSubsetRows k l, fixedSubsetSum v S ^ 2 =
      ((k+l+1).choose (k+1) : ℝ) * ∑ i, v i ^ 2 +
        ((k+l+1).choose k : ℝ) * (∑ i, v i)^2 := by
  have he (S : Finset (Fin (k+l+3))) : fixedSubsetSum v S ^ 2 =
      ∑ i, v i * ((if i ∈ S then (1 : ℝ) else 0) * fixedSubsetSum v S) := by
    rw [pow_two, fixedSubsetSum_eq_indicator v S, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  change (∑ i, v i * fixedSubsetBackprojection v i) = _
  simp_rw [fixedSubsetBackprojection_eq, mul_add, Finset.sum_add_distrib]
  have h₁ : (∑ i, v i * (((k+l+1).choose (k+1) : ℝ) * v i)) =
      ((k+l+1).choose (k+1) : ℝ) * ∑ i, v i^2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [h₁, ← Finset.sum_mul]
  ring

lemma fixedSubsetContrast_pos (k l : ℕ) : 0 < ((k+l+1).choose (k+1) : ℝ) := by
  exact_mod_cast Nat.choose_pos (by omega : k+1 ≤ k+l+1)

/-- A uniform lower bound proves stable identification from all fixed-size rows. -/
theorem fixedSubsetSum_energy_lower (v : Fin (k+l+3) → ℝ) :
    ((k+l+1).choose (k+1) : ℝ) * ∑ i, v i^2 ≤
      ∑ S ∈ fixedSubsetRows k l, fixedSubsetSum v S ^ 2 := by
  rw [fixedSubsetSum_energy]
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

/-- The backprojected data recover every coordinate without a zero-sum assumption. -/
theorem fixedSubsetSum_reconstruction (v : Fin (k+l+3) → ℝ) (i : Fin (k+l+3)) :
    v i = (fixedSubsetBackprojection v i -
      ((k+l+1).choose k : ℝ) / ((k+l+1).choose (k+1) + (k+l+3) * (k+l+1).choose k : ℝ) *
        ∑ j, fixedSubsetBackprojection v j) / ((k+l+1).choose (k+1) : ℝ) := by
  have hc := fixedSubsetContrast_pos k l
  have hb : 0 ≤ ((k+l+1).choose k : ℝ) := Nat.cast_nonneg _
  have hd : ((k+l+1).choose (k+1) : ℝ) + (k+l+3) * (k+l+1).choose k ≠ 0 := by
    positivity
  simp_rw [fixedSubsetBackprojection_eq]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp [hc.ne', hd]
  ring

#print axioms fixedSubsetRows_gram
#print axioms fixedSubsetSum_energy
#print axioms fixedSubsetSum_energy_lower
#print axioms fixedSubsetSum_reconstruction
/-- The actual observation map on the fixed-size subset family. -/
def fixedSubsetObservation (k l : ℕ) (v : Fin (k+l+3) → ℝ) :
    {S // S ∈ fixedSubsetRows k l} → ℝ := fun S => fixedSubsetSum v S.1

/-- Fixed-size subset observations determine the complete vector. -/
theorem fixedSubsetObservation_injective (k l : ℕ) :
    Function.Injective (fixedSubsetObservation k l) := by
  intro v w h
  have hb : fixedSubsetBackprojection v = fixedSubsetBackprojection w := by
    funext i
    unfold fixedSubsetBackprojection
    apply Finset.sum_congr rfl
    intro S hS
    have he := congrFun h ⟨S,hS⟩
    change fixedSubsetSum v S = fixedSubsetSum w S at he
    rw [he]
  funext i
  rw [fixedSubsetSum_reconstruction v i, fixedSubsetSum_reconstruction w i, hb]

#print axioms fixedSubsetObservation_injective

end
end GaloisForLFunctions.BezoutValuationIncidence
