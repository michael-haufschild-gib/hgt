import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Tactic

/-!
# Integral zero-sum energy

The sum of squares of an integral zero-sum vector is even. Its norm-two
vectors are exactly the differences of distinct coordinate vectors. Thus
excluding these roots forces every nonzero vector to have energy at least four.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.IntegralZeroSum

variable {ι : Type*} [Fintype ι]

/-- The squared Euclidean norm of an integral coordinate vector. -/
def energy (x : ι → ℤ) : ℤ := ∑ i, (x i)^2

/-- The integral coordinate pairing. -/
def pairing (x y : ι → ℤ) : ℤ := ∑ i, x i * y i

/-- The difference of two coordinate vectors. -/
noncomputable def root (a b : ι) : ι → ℤ := by
  classical
  exact Pi.single a 1 - Pi.single b 1

theorem pairing_comm (x y : ι → ℤ) : pairing x y = pairing y x := by
  unfold pairing
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem pairing_root_left (a b : ι) (x : ι → ℤ) : pairing (root a b) x = x a - x b := by
  classical
  simp [pairing, root, Pi.single_apply, sub_mul, ite_mul, Finset.sum_sub_distrib]

theorem pairing_root_right (x : ι → ℤ) (a b : ι) : pairing x (root a b) = x a - x b := by
  rw [pairing_comm, pairing_root_left]

/-- Roots sharing a base coordinate have Gram matrix identity plus all-ones. -/
theorem pairing_roots_common_base [DecidableEq ι] (a b e : ι) (ha : a ≠ e) (hb : b ≠ e) :
    pairing (root a e) (root b e) = (if a = b then 1 else 0) + 1 := by
  classical
  rw [pairing_root_left]
  by_cases hab : a = b
  · subst b
    simp [root, ha, Ne.symm ha]
  · simp [root, ha, Ne.symm hb, hab]

theorem energy_sub (x y : ι → ℤ) :
    energy (x - y) = energy x + energy y - 2 * pairing x y := by
  calc
    energy (x - y) = ∑ i, ((x i)^2 + (y i)^2 - 2 * (x i * y i)) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.sub_apply]
      ring
    _ = energy x + energy y - 2 * pairing x y := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, energy, pairing]

theorem energy_nonneg (x : ι → ℤ) : 0 ≤ energy x :=
  Finset.sum_nonneg fun i _ => sq_nonneg (x i)

theorem energy_eq_zero_iff (x : ι → ℤ) : energy x = 0 ↔ x = 0 := by
  rw [energy, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))]
  simp only [Finset.mem_univ, forall_const, sq_eq_zero_iff, funext_iff, Pi.zero_apply]

theorem energy_pos {x : ι → ℤ} (hx : x ≠ 0) : 0 < energy x := by
  have hn := energy_nonneg x
  have hz : energy x ≠ 0 := fun h => hx ((energy_eq_zero_iff x).mp h)
  omega

/-- Zero coordinate sum forces even squared norm. -/
theorem energy_even {x : ι → ℤ} (hx : ∑ i, x i = 0) : Even (energy x) := by
  have he (i : ι) : Even ((x i)^2 - x i) := by
    convert Int.even_mul_pred_self (x i) using 1; ring
  choose k hk using he
  refine ⟨∑ i, k i, ?_⟩
  calc
    energy x = ∑ i, ((x i)^2 - x i) := by
      rw [Finset.sum_sub_distrib, hx, sub_zero]
      rfl
    _ = ∑ i, (k i + k i) := Finset.sum_congr rfl fun i _ => hk i
    _ = (∑ i, k i) + ∑ i, k i := Finset.sum_add_distrib

theorem energy_root [DecidableEq ι] (a b : ι) : energy (root a b) = if a = b then 0 else 2 := by
  classical
  by_cases hab : a = b
  · subst b
    simp [root, energy]
  · rw [if_neg hab]
    have he (i : ι) : (root a b i)^2 =
        (if i = a then (1 : ℤ) else 0) + (if i = b then 1 else 0) := by
      by_cases hia : i = a
      · subst i
        simp [root, hab]
      · by_cases hib : i = b
        · subst i
          simp [root, Ne.symm hab]
        · simp [root, hia, hib]
    rw [energy, Finset.sum_congr rfl (fun i _ => he i), Finset.sum_add_distrib]
    simp

/-- Every integral zero-sum vector of squared norm two is a root. -/
theorem exists_root_of_energy_two {x : ι → ℤ} (hsum : ∑ i, x i = 0)
    (he : energy x = 2) : ∃ a b, a ≠ b ∧ x = root a b := by
  classical
  have hbound (i : ι) : -1 ≤ x i ∧ x i ≤ 1 := by
    have hsq : (x i)^2 ≤ 2 :=
      (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)).trans_eq he
    constructor
    · by_contra hn
      have h : x i ≤ -2 := by omega
      nlinarith only [h, hsq]
    · by_contra hn
      have h : 2 ≤ x i := by omega
      nlinarith only [h, hsq]
  have hpos : ∃ a, 0 < x a := by
    by_contra! h
    have hz := (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => h i)).mp hsum
    have hx : x = 0 := funext fun i => hz i (Finset.mem_univ i)
    rw [(energy_eq_zero_iff x).mpr hx] at he
    omega
  have hneg : ∃ b, x b < 0 := by
    by_contra! h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h i)).mp hsum
    have hx : x = 0 := funext fun i => hz i (Finset.mem_univ i)
    rw [(energy_eq_zero_iff x).mpr hx] at he
    omega
  obtain ⟨a, ha⟩ := hpos
  obtain ⟨b, hb⟩ := hneg
  have ha1 : x a = 1 := by have := hbound a; omega
  have hb1 : x b = -1 := by have := hbound b; omega
  have hab : a ≠ b := by intro h; subst b; omega
  refine ⟨a, b, hab, funext fun i => ?_⟩
  by_cases hia : i = a
  · subst i
    simp [root, ha1, hab]
  · by_cases hib : i = b
    · subst i
      simp [root, hb1, Ne.symm hab]
    · have htri : (x a)^2 + (x b)^2 + (x i)^2 ≤ energy x := by
        have hs := Finset.sum_le_sum_of_subset_of_nonneg
          (show ({a, b, i} : Finset ι) ⊆ Finset.univ from Finset.subset_univ _)
          (fun j _ _ => sq_nonneg (x j))
        simpa only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
          hab, Ne.symm hia, Ne.symm hib, not_false_eq_true, or_self, Finset.sum_singleton,
          energy, add_assoc]
          using hs
      have hxi : x i = 0 := by
        rw [ha1, hb1, he] at htri
        nlinarith only [htri, sq_nonneg (x i)]
      simp [root, hia, hib, hxi]

/-- A nonzero zero-sum vector which is not a root has squared norm at least four. -/
theorem four_le_energy_of_no_root {x : ι → ℤ} (hsum : ∑ i, x i = 0)
    (hx : x ≠ 0) (hroot : ∀ a b, a ≠ b → x ≠ root a b) : 4 ≤ energy x := by
  obtain ⟨k, hk⟩ := energy_even hsum
  have hp := energy_pos hx
  have htwo : energy x ≠ 2 := by
    intro h
    obtain ⟨a, b, hab, hx⟩ := exists_root_of_energy_two hsum h
    exact hroot a b hab hx
  omega

#print axioms exists_root_of_energy_two
#print axioms four_le_energy_of_no_root

end GaloisForLFunctions.HTGeometry.IntegralZeroSum
