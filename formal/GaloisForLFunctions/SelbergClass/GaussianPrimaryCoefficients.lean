import GaloisForLFunctions.SelbergClass.GaussianAngularCoefficients
import GaloisForLFunctions.FamilyContinuationTheory.Quartic.GaussianPrimary

/-!
# Primary representatives of Gaussian angular coefficients

At every odd norm, one of the four unit rotations is primary. In weights
divisible by four all rotations have the same harmonic weight. Restriction to
primary representatives therefore divides the full norm coefficient by four.
-/

noncomputable section

open scoped Classical
open Complex Finset RHTower.GaussianTwoSquares
open GaloisForLFunctions.FamilyContinuationTheory.Quartic

namespace GaloisForLFunctions.SelbergClass.GaussianAngular

/-- Harmonic coefficients summed over the canonical primary representatives. -/
def primaryCoefficient (k n : ℕ) : ℂ :=
  ∑ z : ↥(normSet n), if IsPrimary z.val then (z.val : ℂ) ^ k else 0

/-- Number of primary representatives on a Gaussian norm fiber. -/
def primaryCount (n : ℕ) : ℕ :=
  ∑ z : ↥(normSet n), if IsPrimary z.val then 1 else 0

/-- The weight-zero primary coefficient is an ordinary nonnegative count. -/
theorem primaryCoefficient_zero (n : ℕ) : primaryCoefficient 0 n = (primaryCount n : ℂ) := by
  classical
  simp [primaryCoefficient, primaryCount]

private theorem rotate_gaussian (n : ℕ) (z : ↥(normSet n)) :
    (rotate n z).val = gaussianI * z.val := by
  apply Zsqrtd.ext <;>
    simp [rotate, gaussianI, Zsqrtd.re_mul, Zsqrtd.im_mul]

private theorem rotate_pow_gaussian (n j : ℕ) (z : ↥(normSet n)) :
    (((rotate n : Equiv.Perm ↥(normSet n)) ^ j) z).val = gaussianI ^ j * z.val := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, rotate_gaussian, ih, ← mul_assoc, ← pow_succ']

private theorem rotate_weight (m n : ℕ) (z : ↥(normSet n)) :
    ((rotate n z).val : ℂ) ^ (4 * m) = (z.val : ℂ) ^ (4 * m) := by
  rw [rotate_complex, mul_pow]
  have hI : I ^ (4 * m) = 1 := by
    rw [pow_mul, show I ^ 4 = 1 by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, I_sq]; norm_num, one_pow]
  rw [hI, one_mul]

private theorem rotate_pow_weight (m n j : ℕ) (z : ↥(normSet n)) :
    ((((rotate n : Equiv.Perm ↥(normSet n)) ^ j) z).val : ℂ) ^ (4 * m) =
      (z.val : ℂ) ^ (4 * m) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ', Equiv.Perm.mul_apply, rotate_weight, ih]

private theorem odd_of_odd_norm (n : {n : ℕ // n % 2 = 1}) (z : ↥(normSet n.val)) :
    ¬onePlusI ∣ z.val := by
  rintro ⟨w, hw⟩
  have hn := mem_normSet.mp z.property
  rw [hw, Zsqrtd.norm_mul, norm_onePlusI] at hn
  have hnodd := n.property
  omega

/-- At odd norm, restriction to primary generators divides every weight-four coefficient by four. -/
theorem coefficient_eq_four_primary (m : ℕ) (n : {n : ℕ // n % 2 = 1}) :
    coefficient (4 * m) n.val = 4 * primaryCoefficient (4 * m) n.val := by
  classical
  let f : ↥(normSet n.val) → ℂ :=
    fun z => if IsPrimary z.val then (z.val : ℂ) ^ (4 * m) else 0
  have horbit (z : ↥(normSet n.val)) :
      (∑ j : Fin 4, f (((rotate n.val : Equiv.Perm ↥(normSet n.val)) ^ j.val) z)) =
        (z.val : ℂ) ^ (4 * m) := by
    obtain ⟨j, hj, huniq⟩ :=
      (odd_iff_unique_primary_rotation z.val).mp (odd_of_odd_norm n z)
    have heq (k : Fin 4) :
        f (((rotate n.val : Equiv.Perm ↥(normSet n.val)) ^ k.val) z) =
          if IsPrimary (gaussianI ^ k.val * z.val) then (z.val : ℂ) ^ (4 * m) else 0 := by
      dsimp only [f]
      rw [rotate_pow_weight, rotate_pow_gaussian]
    simp_rw [heq]
    rw [Finset.sum_eq_single j]
    · rw [if_pos hj]
    · intro k _ hkj
      exact if_neg (fun hk => hkj (huniq k hk))
    · simp
  calc
    coefficient (4 * m) n.val = ∑ z : ↥(normSet n.val), ∑ j : Fin 4,
        f (((rotate n.val : Equiv.Perm ↥(normSet n.val)) ^ j.val) z) := by
      simp only [horbit, coefficient]
    _ = ∑ j : Fin 4, ∑ z : ↥(normSet n.val),
        f (((rotate n.val : Equiv.Perm ↥(normSet n.val)) ^ j.val) z) := Finset.sum_comm
    _ = ∑ _j : Fin 4, primaryCoefficient (4 * m) n.val := by
      apply Finset.sum_congr rfl
      intro j _
      exact ((rotate n.val : Equiv.Perm ↥(normSet n.val)) ^ j.val).sum_comp f
    _ = 4 * primaryCoefficient (4 * m) n.val := by simp

/-- The number of primary representatives is exactly one quarter of the two-square count. -/
theorem norm_count_eq_four_primary (n : {n : ℕ // n % 2 = 1}) :
    ((normSet n.val).card : ℂ) = 4 * primaryCoefficient 0 n.val := by
  simpa [coefficient] using coefficient_eq_four_primary 0 n

/-- Primary representatives account for exactly a quarter of every odd norm fiber. -/
theorem card_normSet_eq_four_primaryCount (n : {n : ℕ // n % 2 = 1}) :
    (normSet n.val).card = 4 * primaryCount n.val := by
  have h := norm_count_eq_four_primary n
  rw [primaryCoefficient_zero] at h
  exact_mod_cast h

/-- Jacobi's divisor sum counts primary Gaussian representatives at every odd norm. -/
theorem primaryCount_eq_divisorChar (n : {n : ℕ // n % 2 = 1}) :
    (primaryCount n.val : ℤ) = divisorChar n.val := by
  have hn : 0 < n.val := by have h := n.property; omega
  have hc := card_normSet hn
  rw [card_normSet_eq_four_primaryCount n] at hc
  push_cast at hc
  linarith only [hc]

end GaloisForLFunctions.SelbergClass.GaussianAngular
