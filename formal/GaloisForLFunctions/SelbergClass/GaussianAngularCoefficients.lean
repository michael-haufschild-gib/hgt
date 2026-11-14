import GaloisForLFunctions.RHTower.GaussianTwoSquaresCount
import Mathlib.Analysis.Complex.Basic

/-!
# Angular coefficients on Gaussian norm fibers

Quarter turns preserve each Gaussian norm fiber. Its harmonic coefficient of
weight `k` is therefore an `i^k` eigenvector, so only weights divisible by four
survive. Those coefficients are real by conjugation and satisfy a bound by the
ordinary two-square representation count.
-/

noncomputable section

open Complex Finset RHTower.GaussianTwoSquares

namespace GaloisForLFunctions.SelbergClass.GaussianAngular

/-- Rotation through a quarter turn on a fixed norm fiber. -/
def rotate (n : ℕ) : ↥(normSet n) ≃ ↥(normSet n) where
  toFun z := ⟨⟨-z.1.im, z.1.re⟩, by
    rw [mem_normSet, norm_eq]
    have h := mem_normSet.mp z.2
    rw [norm_eq] at h
    change (-z.1.im) ^ 2 + z.1.re ^ 2 = _
    nlinarith only [h]⟩
  invFun z := ⟨⟨z.1.im, -z.1.re⟩, by
    rw [mem_normSet, norm_eq]
    have h := mem_normSet.mp z.2
    rw [norm_eq] at h
    change z.1.im ^ 2 + (-z.1.re) ^ 2 = _
    nlinarith only [h]⟩
  left_inv z := by apply Subtype.ext; ext <;> simp
  right_inv z := by apply Subtype.ext; ext <;> simp

/-- The complex embedding intertwines the integral rotation with multiplication by `i`. -/
theorem rotate_complex (n : ℕ) (z : ↥(normSet n)) :
    ((rotate n z).1 : ℂ) = I * (z.1 : ℂ) := by
  change ((⟨-z.1.im, z.1.re⟩ : GaussianInt) : ℂ) = _
  simp only [GaussianInt.toComplex_def, Int.cast_neg]
  calc
    -(z.1.im : ℂ) + (z.1.re : ℂ) * I =
        I * (z.1.re : ℂ) + (z.1.im : ℂ) * I ^ 2 := by rw [I_sq]; ring
    _ = _ := by ring

/-- Harmonic coefficient of a Gaussian norm fiber. -/
def coefficient (k n : ℕ) : ℂ := ∑ z : ↥(normSet n), (z.1 : ℂ) ^ k

/-- Quarter-turn symmetry imposes an exact algebraic constraint on every coefficient. -/
theorem coefficient_constraint (k n : ℕ) : (I ^ k - 1) * coefficient k n = 0 := by
  have h := (rotate n).sum_comp (fun z : ↥(normSet n) => (z.1 : ℂ) ^ k)
  simp_rw [rotate_complex, mul_pow] at h
  rw [← Finset.mul_sum] at h
  change I ^ k * coefficient k n = coefficient k n at h
  linear_combination h

private theorem I_four_mul (m : ℕ) : I ^ (4 * m) = 1 := by
  rw [pow_mul, show I ^ 4 = 1 by norm_num [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, I_sq], one_pow]

/-- Weights congruent to one modulo four have zero coefficients at every norm. -/
theorem coefficient_one_mod_four (m n : ℕ) : coefficient (4 * m + 1) n = 0 := by
  have h := coefficient_constraint (4 * m + 1) n
  rw [pow_add, I_four_mul, pow_one, one_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (by
    intro hI
    have := congrArg Complex.im hI
    norm_num at this)

/-- Weights congruent to two modulo four have zero coefficients at every norm. -/
theorem coefficient_two_mod_four (m n : ℕ) : coefficient (4 * m + 2) n = 0 := by
  have h := coefficient_constraint (4 * m + 2) n
  rw [pow_add, I_four_mul, I_sq, one_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num)

/-- Cubic angular coefficients vanish on every Gaussian norm fiber. -/
theorem coefficient_three_mod_four (m n : ℕ) : coefficient (4 * m + 3) n = 0 := by
  have h := coefficient_constraint (4 * m + 3) n
  rw [pow_add, I_four_mul, one_mul, show I ^ 3 = -I by
    rw [pow_succ, I_sq, neg_one_mul]] at h
  exact (mul_eq_zero.mp h).resolve_left (by
    intro hI
    have := congrArg Complex.im hI
    norm_num at this)

/-- Conjugation permutes the same norm fiber. -/
def conjugate (n : ℕ) : ↥(normSet n) ≃ ↥(normSet n) where
  toFun z := ⟨star z.1, by
    rw [mem_normSet, Zsqrtd.norm_conj]
    exact mem_normSet.mp z.2⟩
  invFun z := ⟨star z.1, by
    rw [mem_normSet, Zsqrtd.norm_conj]
    exact mem_normSet.mp z.2⟩
  left_inv z := by apply Subtype.ext; exact star_star z.1
  right_inv z := by apply Subtype.ext; exact star_star z.1

/-- All harmonic norm coefficients are real. -/
theorem coefficient_conj (k n : ℕ) : star (coefficient k n) = coefficient k n := by
  have h := (conjugate n).sum_comp (fun z : ↥(normSet n) => (z.1 : ℂ) ^ k)
  change (∑ z : ↥(normSet n), ((star z.1 : GaussianInt) : ℂ) ^ k) = coefficient k n at h
  simpa only [coefficient, star_sum, star_pow, Complex.star_def, GaussianInt.toComplex_star] using h

/-- The surviving weight-four sectors are bounded by the ordinary representation count. -/
theorem coefficient_four_mul_bound (m n : ℕ) :
    ‖coefficient (4 * m) n‖ ≤ ((normSet n).card : ℝ) * (n : ℝ) ^ (2 * m) := by
  have hnorm (z : ↥(normSet n)) : ‖(z.1 : ℂ)‖ ^ 2 = (n : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq, ← GaussianInt.intCast_real_norm, mem_normSet.mp z.2]
    norm_cast
  calc
    ‖coefficient (4 * m) n‖ ≤ ∑ z : ↥(normSet n), ‖(z.1 : ℂ) ^ (4 * m)‖ :=
      norm_sum_le _ _
    _ = ∑ _z : ↥(normSet n), (n : ℝ) ^ (2 * m) := by
      apply sum_congr rfl
      intro z _
      rw [norm_pow, show 4 * m = 2 * (2 * m) by omega, pow_mul, hnorm]
    _ = _ := by simp

private theorem norm_one_fourth (z : ↥(normSet 1)) : (z.1 : ℂ) ^ 4 = 1 := by
  have hn := mem_normSet.mp z.2
  rw [norm_eq] at hn
  norm_num only [Nat.cast_one] at hn
  have hab : z.1.re * z.1.im = 0 := by
    by_cases ha : z.1.re = 0
    · rw [ha, zero_mul]
    · have ha2 : 1 ≤ z.1.re ^ 2 := by
        have hp : 0 < z.1.re ^ 2 := sq_pos_of_ne_zero ha
        omega
      have hb2 : z.1.im ^ 2 = 0 := by nlinarith only [hn, ha2, sq_nonneg z.1.im]
      have hb : z.1.im = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hb2
      rw [hb, mul_zero]
  have hnC : (z.1.re : ℂ) ^ 2 + (z.1.im : ℂ) ^ 2 = 1 := by exact_mod_cast hn
  have habC : (z.1.re : ℂ) * (z.1.im : ℂ) = 0 := by exact_mod_cast hab
  have hz2 : (z.1 : ℂ) ^ 2 = (z.1.re : ℂ) ^ 2 - (z.1.im : ℂ) ^ 2 := by
    rw [GaussianInt.toComplex_def]
    linear_combination (z.1.im : ℂ) ^ 2 * I_sq + (2 * I) * habC
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hz2]
  linear_combination ((z.1.re : ℂ) ^ 2 + (z.1.im : ℂ) ^ 2 + 1) * hnC -
    (4 * (z.1.re : ℂ) * (z.1.im : ℂ)) * habC

/-- Every surviving weight has a nonzero first coefficient: the four units all contribute one. -/
theorem coefficient_four_mul_one (m : ℕ) : coefficient (4 * m) 1 = 4 := by
  unfold coefficient
  simp_rw [pow_mul, norm_one_fourth, one_pow]
  simp only [sum_const, card_univ, Fintype.card_coe, card_normSet_one, nsmul_eq_mul,
    Nat.cast_ofNat, mul_one]

/-- A complete angular sector vanishes exactly when its weight is not divisible by four. -/
theorem coefficient_all_zero_iff (k : ℕ) :
    (∀ n : ℕ, coefficient k n = 0) ↔ ¬4 ∣ k := by
  constructor
  · intro h ⟨m, hm⟩
    have h1 := h 1
    rw [hm, coefficient_four_mul_one] at h1
    norm_num at h1
  · intro h
    have hrange := Nat.mod_lt k (show 0 < 4 by norm_num)
    have hmod : k % 4 ≠ 0 := fun hz => h (Nat.dvd_of_mod_eq_zero hz)
    have hr : k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    rcases hr with hr | hr | hr
    · have hk : k = 4 * (k / 4) + 1 := by omega
      intro n
      rw [hk]
      exact coefficient_one_mod_four _ _
    · have hk : k = 4 * (k / 4) + 2 := by omega
      intro n
      rw [hk]
      exact coefficient_two_mod_four _ _
    · have hk : k = 4 * (k / 4) + 3 := by omega
      intro n
      rw [hk]
      exact coefficient_three_mod_four _ _

end GaloisForLFunctions.SelbergClass.GaussianAngular
