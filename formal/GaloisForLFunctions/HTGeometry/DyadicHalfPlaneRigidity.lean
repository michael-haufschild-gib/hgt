import Mathlib

/-!
# Dyadic half-plane phase rigidity

A complex number whose every dyadic power has nonnegative real part must itself lie on the
nonnegative real ray.  The proof uses the doubling recurrence on the real parts of the normalized
unit-phase powers; no argument branch or trigonometric classification is needed.
-/

open Complex

namespace GaloisForLFunctions

/-- Every dyadic power of `z` lies in the closed right half-plane. -/
def ComplexDyadicHalfPlane (z : ℂ) : Prop :=
  ∀ k : ℕ, 0 ≤ (z ^ (2 ^ k)).re

/-- **Dyadic half-plane phase rigidity.**  A complex number has every dyadic power in the closed
right half-plane exactly when it is a nonnegative real number. -/
theorem complexDyadicHalfPlane_iff_nonnegativeReal (z : ℂ) :
    ComplexDyadicHalfPlane z ↔ z.im = 0 ∧ 0 ≤ z.re := by
  constructor
  · intro h
    by_cases hz : z = 0
    · subst z
      simp
    let r : ℝ := ‖z‖
    have hr : 0 < r := by simpa only [r] using norm_pos_iff.mpr hz
    let u : ℂ := z / (r : ℂ)
    have hunorm : ‖u‖ = 1 := by
      simp [u, r, hr.ne']
    have hzu : z = (r : ℂ) * u := by
      dsimp only [u]
      field_simp [hr.ne']
    let x : ℕ → ℝ := fun k => (u ^ (2 ^ k)).re
    have hx0 : ∀ k : ℕ, 0 ≤ x k := by
      intro k
      have hk := h k
      have hscale :
          (z ^ (2 ^ k)).re = r ^ (2 ^ k) * x k := by
        rw [hzu, mul_pow]
        have hcastRe : ((r : ℂ) ^ (2 ^ k)).re = r ^ (2 ^ k) := by
          exact congrArg Complex.re (Complex.ofReal_pow r (2 ^ k)).symm
        have hcastIm : ((r : ℂ) ^ (2 ^ k)).im = 0 := by
          exact congrArg Complex.im (Complex.ofReal_pow r (2 ^ k)).symm
        rw [Complex.mul_re, hcastRe, hcastIm]
        simp [x]
      have hp : 0 < r ^ (2 ^ k) := pow_pos hr _
      rw [hscale] at hk
      nlinarith
    have hx1 : ∀ k : ℕ, x k ≤ 1 := by
      intro k
      have hnorm : ‖u ^ (2 ^ k)‖ = 1 := by simp [norm_pow, hunorm]
      exact (Complex.re_le_norm _).trans_eq hnorm
    have hrec : ∀ k : ℕ, x (k + 1) = 2 * (x k) ^ 2 - 1 := by
      intro k
      let v : ℂ := u ^ (2 ^ k)
      have hvnorm : ‖v‖ = 1 := by simp [v, norm_pow, hunorm]
      have hvnormsq : v.re ^ 2 + v.im ^ 2 = 1 := by
        have hs := Complex.sq_norm v
        rw [hvnorm] at hs
        simpa [Complex.normSq_apply, pow_two] using hs.symm
      change (u ^ (2 ^ (k + 1))).re = 2 * (u ^ (2 ^ k)).re ^ 2 - 1
      rw [pow_succ, pow_mul]
      change (v ^ 2).re = 2 * v.re ^ 2 - 1
      rw [pow_two, Complex.mul_re]
      nlinarith
    let d : ℕ → ℝ := fun k => 1 - x k
    have hd0 : ∀ k : ℕ, 0 ≤ d k := fun k => by
      dsimp only [d]
      linarith [hx1 k]
    have hdle : ∀ k : ℕ, d k ≤ 1 := fun k => by
      dsimp only [d]
      linarith [hx0 k]
    have hdrec : ∀ k : ℕ, 2 * d k ≤ d (k + 1) := by
      intro k
      have hrk := hrec k
      have hxk := hx0 k
      have hxk1 := hx1 k
      dsimp only [d]
      nlinarith
    have hdlin : ∀ k : ℕ, ((k + 1 : ℕ) : ℝ) * d 0 ≤ d k := by
      intro k
      induction k with
      | zero => norm_num
      | succ k ih =>
          have hstep := hdrec k
          have hdmono : d 0 ≤ d k := by
            have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by norm_num
            have := hd0 0
            nlinarith
          norm_num [Nat.cast_add, Nat.cast_one] at ih ⊢
          nlinarith
    have hd_zero : d 0 = 0 := by
      by_contra hne
      have hdpos : 0 < d 0 := lt_of_le_of_ne (hd0 0) (Ne.symm hne)
      obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (1 / d 0)
      have hnprod : 1 < (n : ℝ) * d 0 := by
        rw [div_lt_iff₀ hdpos] at hn
        simpa [one_mul] using hn
      have hbound := hdlin n
      have hbad : 1 < d n := by
        have hnnonneg : 0 ≤ d 0 := hd0 0
        norm_num [Nat.cast_add, Nat.cast_one] at hbound
        nlinarith
      linarith [hdle n]
    have hure : u.re = 1 := by
      dsimp only [d, x] at hd_zero
      norm_num at hd_zero
      linarith
    have huim : u.im = 0 := by
      have hs := Complex.sq_norm u
      rw [hunorm] at hs
      simp only [one_pow, Complex.normSq_apply] at hs
      nlinarith [sq_nonneg u.im]
    have hu : u = 1 := by
      apply Complex.ext
      · simpa using hure
      · simpa using huim
    rw [hzu, hu]
    constructor
    · simp
    · simpa using hr.le
  · rintro ⟨him, hre⟩ k
    have hzreal : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    rw [hzreal]
    have hcastRe : (((z.re : ℝ) : ℂ) ^ (2 ^ k)).re = z.re ^ (2 ^ k) := by
      exact congrArg Complex.re (Complex.ofReal_pow z.re (2 ^ k)).symm
    rw [hcastRe]
    exact pow_nonneg hre (2 ^ k)

end GaloisForLFunctions
