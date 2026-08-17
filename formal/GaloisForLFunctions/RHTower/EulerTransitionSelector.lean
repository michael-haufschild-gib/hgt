import Mathlib
import GaloisForLFunctions.RHTower.TwoDilationDivisorMetric

/-!
# The two-base real Euler-transition selector

For a base `x > 1` the centered reflected-Euler transition is `q_x(s) = x + 1 - x^s - x^(1-s)`.
Its imaginary part factors as `-(x^β - x^(1-β)) sin(γ log x)` for `s = β + iγ`, so away from the
critical line `β = 1/2` reality of `q_x(s)` forces `γ log x ∈ π ℤ`.  Two bases whose logarithms
have irrational ratio therefore cannot both give a real transition unless `γ = 0` or `β = 1/2`.
The bases `2` and `3` qualify unconditionally, since `2^m = 3^n` is impossible for positive
exponents.

Conversely `β = 1/2` makes the transition real at every base, with the closed form
`q_x(s) = x + 1 - 2 √x cos(γ log x)`.
-/

namespace GaloisForLFunctions.EulerTransitionSelector

/-- The centered reflected-Euler transition at base `x`. -/
noncomputable def eulerTransition (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) + 1 - (x : ℂ) ^ s - (x : ℂ) ^ (1 - s)

theorem im_cpow_ofReal {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ((x : ℂ) ^ s).im = x ^ s.re * Real.sin (s.im * Real.log x) := by
  have hx0 : (x : ℂ) ≠ 0 := by
    simpa using ne_of_gt hx
  rw [Complex.cpow_def_of_ne_zero hx0, Complex.exp_im, ← Complex.ofReal_log (le_of_lt hx)]
  have hre : ((Real.log x : ℂ) * s).re = Real.log x * s.re := by
    simp [Complex.mul_re]
  have him : ((Real.log x : ℂ) * s).im = Real.log x * s.im := by
    simp [Complex.mul_im]
  rw [hre, him, Real.rpow_def_of_pos hx, mul_comm (Real.log x) s.im]

theorem im_eulerTransition {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (eulerTransition x s).im
      = -((x ^ s.re - x ^ (1 - s.re)) * Real.sin (s.im * Real.log x)) := by
  have h1 := im_cpow_ofReal hx s
  have h2 := im_cpow_ofReal hx (1 - s)
  have hre : (1 - s).re = 1 - s.re := by simp
  have him : (1 - s).im = -s.im := by simp
  rw [hre, him] at h2
  rw [eulerTransition]
  simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.one_im, h1, h2]
  rw [neg_mul, Real.sin_neg]
  ring

theorem im_eulerTransition_eq_zero_iff {x : ℝ} (hx : 1 < x) (s : ℂ) :
    (eulerTransition x s).im = 0 ↔ s.re = 1 / 2 ∨ Real.sin (s.im * Real.log x) = 0 := by
  have hx0 : 0 < x := lt_trans one_pos hx
  rw [im_eulerTransition hx0, neg_eq_zero, mul_eq_zero, sub_eq_zero]
  constructor
  · rintro (h | h)
    · left
      rcases lt_trichotomy s.re (1 - s.re) with hlt | heq | hgt
      · exact absurd h (ne_of_lt ((Real.rpow_lt_rpow_left_iff hx).mpr hlt))
      · linarith
      · exact absurd h.symm (ne_of_lt ((Real.rpow_lt_rpow_left_iff hx).mpr hgt))
    · exact Or.inr h
  · rintro (h | h)
    · left
      rw [h]
      norm_num
    · exact Or.inr h

/-- **The two-base real-transition selector.**  If the transition is real at two bases with
irrational logarithmic ratio, the coordinate has critical real part. -/
theorem re_eq_half_of_im_eulerTransition_eq_zero {p q : ℝ} (hp : 1 < p) (hq : 1 < q)
    (hirr : Irrational (Real.log p / Real.log q)) {s : ℂ} (hγ : s.im ≠ 0)
    (h1 : (eulerTransition p s).im = 0) (h2 : (eulerTransition q s).im = 0) :
    s.re = 1 / 2 := by
  rcases (im_eulerTransition_eq_zero_iff hp s).mp h1 with hre | hsin1
  · exact hre
  rcases (im_eulerTransition_eq_zero_iff hq s).mp h2 with hre | hsin2
  · exact hre
  exfalso
  have hlp : 0 < Real.log p := Real.log_pos hp
  have hlq : 0 < Real.log q := Real.log_pos hq
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hsin1
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin2
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at hm
    simp only [Int.cast_zero, zero_mul] at hm
    exact (mul_ne_zero hγ (ne_of_gt hlp)) hm.symm
  have hn0 : n ≠ 0 := by
    intro h
    rw [h] at hn
    simp only [Int.cast_zero, zero_mul] at hn
    exact (mul_ne_zero hγ (ne_of_gt hlq)) hn.symm
  have hcross : Real.log p * (n : ℝ) = (m : ℝ) * Real.log q := by
    have h3 : (n : ℝ) * (s.im * Real.log p) = (m : ℝ) * (s.im * Real.log q) := by
      rw [← hm, ← hn]; ring
    have h4 : s.im * ((n : ℝ) * Real.log p - (m : ℝ) * Real.log q) = 0 := by nlinarith [h3]
    rcases mul_eq_zero.mp h4 with h | h
    · exact absurd h hγ
    · linarith
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  have hratio : Real.log p / Real.log q = (m : ℝ) / (n : ℝ) :=
    (div_eq_div_iff (ne_of_gt hlq) hnR).mpr hcross
  refine hirr ⟨(m : ℚ) / (n : ℚ), ?_⟩
  rw [hratio]
  push_cast
  ring

/-- The converse: on the critical line every transition is real. -/
theorem im_eulerTransition_eq_zero_of_re_eq_half {x : ℝ} (hx : 0 < x) {s : ℂ}
    (h : s.re = 1 / 2) : (eulerTransition x s).im = 0 := by
  rw [im_eulerTransition hx, h]
  norm_num

/-- On the critical line the transition has the explicit real closed form. -/
theorem eulerTransition_re_eq_half {x : ℝ} (hx : 0 < x) {s : ℂ} (h : s.re = 1 / 2) :
    (eulerTransition x s).re
      = x + 1 - 2 * Real.sqrt x * Real.cos (s.im * Real.log x) := by
  have hx0 : (x : ℂ) ≠ 0 := by simpa using ne_of_gt hx
  have hre : ∀ t : ℂ, ((x : ℂ) ^ t).re = x ^ t.re * Real.cos (t.im * Real.log x) := by
    intro t
    rw [Complex.cpow_def_of_ne_zero hx0, Complex.exp_re, ← Complex.ofReal_log (le_of_lt hx)]
    have h1 : ((Real.log x : ℂ) * t).re = Real.log x * t.re := by simp [Complex.mul_re]
    have h2 : ((Real.log x : ℂ) * t).im = Real.log x * t.im := by simp [Complex.mul_im]
    rw [h1, h2, Real.rpow_def_of_pos hx, mul_comm (Real.log x) t.im]
  have h1 := hre s
  have h2 := hre (1 - s)
  have hre1 : (1 - s).re = 1 - s.re := by simp
  have him1 : (1 - s).im = -s.im := by simp
  rw [hre1, him1, h, neg_mul, Real.cos_neg] at h2
  rw [h] at h1
  rw [eulerTransition]
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.one_re, h1, h2]
  have hsqrt : x ^ (1 / 2 : ℝ) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
  norm_num [hsqrt]
  ring

/-- **Unconditional specialization to the bases `2` and `3`.** -/
theorem re_eq_half_of_two_three {s : ℂ} (hγ : s.im ≠ 0)
    (h2 : (eulerTransition 2 s).im = 0) (h3 : (eulerTransition 3 s).im = 0) :
    s.re = 1 / 2 := by
  have hirr : Irrational (Real.log 2 / Real.log 3) := by
    have := RHTower.irrational_log_div_log (r := 2) (s := 3) le_rfl (by norm_num) ?_
    · simpa using this
    · intro m n hm hn hcon
      have h2d : (2 : ℕ) ∣ 2 ^ m := dvd_pow_self 2 hm.ne'
      rw [hcon] at h2d
      have h23 : (2 : ℕ) ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2d
      norm_num at h23
  exact re_eq_half_of_im_eulerTransition_eq_zero (by norm_num) (by norm_num) hirr hγ h2 h3

end GaloisForLFunctions.EulerTransitionSelector
