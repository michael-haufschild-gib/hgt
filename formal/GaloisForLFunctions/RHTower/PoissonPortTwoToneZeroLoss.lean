import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Poisson port loses real zeros of two-tone sources at an exact threshold

The PTR Poisson port `sech(cD)` acts on `cos(ωt)` by the positive symbol `sech(cω)`.

**Theorem** (`twoTone_zeros_real_iff`). For `A ≠ 0`, `A cos 2z + B cos z` has only real zeros iff
`|B| ≤ |A|`.

**Theorem** (`portTwoTone_zeros_real_iff`). The port of `α cos 2t + β cos t` keeps only real zeros
iff `|β| cosh 2c ≤ |α| cosh c`.

**Corollary** (`poissonPort_loses_real_zeros`). For `cosh c/cosh 2c < r ≤ 1` the source
`cos 2t + r cos t` has only real zeros, while its port has a non-real zero. The window is nonempty
for every `c ≠ 0` (`cosh_lt_cosh_two_mul`).

So a positive port amplifies the lower tone by `cosh(2c)/cosh(c)`. Zero-count preservation is
lost as soon as the amplified subdominant tone overtakes the dominant one. For `cos(½D)`
mapping the horizon producer to `Ξ`, the same amplification turns the prime weights `p^{−1}` on
`σ = 1` into `p^{−½}` on the critical line.

**Proof.** With `w = cos z`, `A cos 2z + B cos z = 2Aw² + Bw − A`. Its roots are real with product
`−½`, and they lie in `[−1, 1]` iff `|B| ≤ |A|`. A real `w ∈ [−1, 1]` has only real preimages under
`cos`. A root with `|w| > 1` is `cos(iy)` or `cos(π + iy)` with `cosh y = |w|`.
-/

open Complex

noncomputable section

namespace RHTower.TwoTonePort

/-- The two-tone function `A cos 2z + B cos z`. -/
def twoTone (A B : ℝ) (z : ℂ) : ℂ := A * Complex.cos (2 * z) + B * Complex.cos z

theorem twoTone_eq (A B : ℝ) (z : ℂ) :
    twoTone A B z = 2 * A * Complex.cos z ^ 2 + B * Complex.cos z - A := by
  rw [twoTone, Complex.cos_two_mul]; ring

/-- `cos z` real and in `[−1, 1]` forces `z` real. -/
theorem im_eq_zero_of_cos_eq {z : ℂ} {c : ℝ} (hc : |c| ≤ 1) (hz : Complex.cos z = c) :
    z.im = 0 := by
  by_contra hy
  have hz' : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
  rw [hz', Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sin, ← Complex.ofReal_sinh] at hz
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, zero_mul, mul_one, Complex.sub_im, Complex.mul_im,
    add_zero, zero_sub] at hre him
  have hsh : Real.sinh z.im ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]; exact hy
  have hsin : Real.sin z.re = 0 := by
    have : Real.sin z.re * Real.sinh z.im = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hsh
  have hcos2 : Real.cos z.re ^ 2 = 1 := by nlinarith [Real.sin_sq_add_cos_sq z.re]
  have hch : 1 < Real.cosh z.im := Real.one_lt_cosh.mpr hy
  have : c ^ 2 = Real.cosh z.im ^ 2 := by rw [← hre]; ring_nf; rw [hcos2]; ring
  have habs : |c| ^ 2 ≤ 1 := by nlinarith [abs_nonneg c]
  rw [sq_abs] at habs
  nlinarith

/-- **Two-tone real-rootedness.** For `A ≠ 0`, `A cos 2z + B cos z` has only real zeros iff
`|B| ≤ |A|`. -/
theorem twoTone_zeros_real_iff {A B : ℝ} (hA : A ≠ 0) :
    (∀ z : ℂ, twoTone A B z = 0 → z.im = 0) ↔ |B| ≤ |A| := by
  set D := Real.sqrt (B ^ 2 + 8 * A ^ 2) with hD
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hDsq : D ^ 2 = B ^ 2 + 8 * A ^ 2 := Real.sq_sqrt (by positivity)
  have hAabs : 0 < |A| := abs_pos.mpr hA
  constructor
  · intro h
    by_contra hBA
    push Not at hBA
    -- the root of largest modulus, `r = −ε(|B| + D)/(4A)` with `ε = sign B`
    set ε : ℝ := if 0 ≤ B then 1 else -1 with hε
    have hε2 : ε ^ 2 = 1 := by rw [hε]; split_ifs <;> norm_num
    have hεB : ε * B = |B| := by
      rw [hε]; split_ifs with hB
      · rw [abs_of_nonneg hB]; ring
      · rw [abs_of_neg (not_le.mp hB)]; ring
    set r : ℝ := -ε * (|B| + D) / (4 * A) with hr
    have hroot : 2 * A * r ^ 2 + B * r - A = 0 := by
      have h8 : 8 * A * (2 * A * r ^ 2 + B * r - A) =
          ε ^ 2 * (|B| + D) ^ 2 - 2 * (ε * B) * (|B| + D) - 8 * A ^ 2 := by
        rw [hr]; field_simp; ring
      rw [hε2, hεB] at h8
      have hB2 : |B| ^ 2 = B ^ 2 := sq_abs B
      have h0 : 8 * A * (2 * A * r ^ 2 + B * r - A) = 0 := by rw [h8]; nlinarith [hDsq, hB2]
      exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (by norm_num) hA)
    have hDgt : 3 * |A| < D := by
      rw [hD]
      have : (3 * |A|) ^ 2 < B ^ 2 + 8 * A ^ 2 := by
        have : |A| ^ 2 < |B| ^ 2 := by nlinarith [abs_nonneg A]
        rw [sq_abs, sq_abs] at this
        nlinarith [sq_abs A]
      exact Real.lt_sqrt_of_sq_lt this
    have hrabs : 1 < |r| := by
      rw [hr, abs_div, abs_mul, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |B| + D)]
      have hεabs : |ε| = 1 := by rw [hε]; split_ifs <;> simp
      rw [hεabs, one_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), lt_div_iff₀ (by positivity)]
      linarith
    -- a non-real zero: `cos z = r` with `|r| > 1`
    obtain ⟨y, hy, hcy⟩ : ∃ y : ℝ, 0 < y ∧ Real.cosh y = |r| := by
      have hcont : ContinuousOn Real.cosh (Set.Icc 0 |r|) := Real.continuous_cosh.continuousOn
      have hle : |r| ≤ Real.cosh |r| := by
        rw [Real.cosh_eq]
        have := Real.quadratic_le_exp_of_nonneg (abs_nonneg r)
        have := Real.exp_pos (-|r|)
        nlinarith [sq_nonneg (|r| - 1)]
      obtain ⟨y, hy, hcy⟩ := intermediate_value_Icc (abs_nonneg r) hcont
        ⟨by rw [Real.cosh_zero]; linarith, hle⟩
      refine ⟨y, lt_of_le_of_ne hy.1 ?_, hcy⟩
      rintro rfl; rw [Real.cosh_zero] at hcy; linarith
    set z : ℂ := (if 0 ≤ r then 0 else (Real.pi : ℂ)) + (y : ℂ) * I with hz
    have hcosz : Complex.cos z = r := by
      rw [hz]
      split_ifs with hr0
      · rw [zero_add, Complex.cos_mul_I, ← Complex.ofReal_cosh, hcy, abs_of_nonneg hr0]
      · rw [Complex.cos_add, Complex.cos_mul_I, Complex.sin_mul_I, ← Complex.ofReal_cos,
          ← Complex.ofReal_sin, Real.cos_pi, Real.sin_pi, ← Complex.ofReal_cosh, hcy,
          abs_of_neg (not_le.mp hr0)]
        push_cast; ring
    have hzero : twoTone A B z = 0 := by
      rw [twoTone_eq, hcosz]
      exact_mod_cast hroot
    have him := h z hzero
    rw [hz] at him
    split_ifs at him <;> simp at him <;> linarith
  · intro hBA z hz
    rw [twoTone_eq] at hz
    set w := Complex.cos z with hw
    -- the roots of `2A w² + B w − A`
    set r₁ : ℝ := (-B + D) / (4 * A)
    set r₂ : ℝ := (-B - D) / (4 * A)
    have hsum : 2 * A * (r₁ + r₂) = -B := by
      simp only [r₁, r₂]; field_simp; ring
    have hprod : 2 * A * (r₁ * r₂) = -A := by
      simp only [r₁, r₂]; field_simp; nlinarith [hDsq]
    have hsumC : 2 * (A : ℂ) * ((r₁ : ℂ) + r₂) = -B := by exact_mod_cast hsum
    have hprodC : 2 * (A : ℂ) * ((r₁ : ℂ) * r₂) = -A := by exact_mod_cast hprod
    have hfac : 2 * A * w ^ 2 + B * w - A = 2 * A * (w - r₁) * (w - r₂) := by
      linear_combination w * hsumC - hprodC
    rw [hfac] at hz
    have hA2 : (2 * (A : ℂ)) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero hA
    have hDle : D ≤ 3 * |A| := by
      rw [hD]
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity, ?_⟩
      have : B ^ 2 ≤ A ^ 2 := by
        have := mul_self_le_mul_self (abs_nonneg B) hBA
        rw [← sq, ← sq, sq_abs, sq_abs] at this; exact this
      nlinarith [sq_abs A]
    have hbound : ∀ r : ℝ, (r = r₁ ∨ r = r₂) → |r| ≤ 1 := by
      rintro r (rfl | rfl)
      · simp only [r₁]
        rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), div_le_one (by positivity)]
        calc |-B + D| ≤ |B| + D := by
              calc |-B + D| ≤ |-B| + |D| := abs_add_le _ _
                _ = |B| + D := by rw [abs_neg, abs_of_nonneg hD0]
          _ ≤ 4 * |A| := by linarith
      · simp only [r₂]
        rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), div_le_one (by positivity)]
        calc |-B - D| ≤ |B| + D := by
              calc |-B - D| = |-B + -D| := by rw [sub_eq_add_neg]
                _ ≤ |-B| + |-D| := abs_add_le _ _
                _ = |B| + D := by rw [abs_neg, abs_neg, abs_of_nonneg hD0]
          _ ≤ 4 * |A| := by linarith
    rcases mul_eq_zero.mp hz with h1 | h2
    · rcases mul_eq_zero.mp h1 with h0 | h1
      · exact absurd h0 hA2
      · exact im_eq_zero_of_cos_eq (hbound r₁ (Or.inl rfl)) (sub_eq_zero.mp h1)
    · exact im_eq_zero_of_cos_eq (hbound r₂ (Or.inr rfl)) (sub_eq_zero.mp h2)

/-- The Poisson port `sech(cD)` acts on `cos(ωt)` by the symbol `sech(cω)`; on the two-tone source
`α cos 2t + β cos t` it gives `α sech(2c) cos 2t + β sech(c) cos t`. -/
def portTwoTone (c α β : ℝ) (z : ℂ) : ℂ := twoTone (α / Real.cosh (2 * c)) (β / Real.cosh c) z

/-- **Exact zero-loss threshold of the Poisson port on two tones.** For `α ≠ 0`, the ported
two-tone function has only real zeros iff `|β| cosh(2c) ≤ |α| cosh c`. -/
theorem portTwoTone_zeros_real_iff {c α β : ℝ} (hα : α ≠ 0) :
    (∀ z : ℂ, portTwoTone c α β z = 0 → z.im = 0) ↔
      |β| * Real.cosh (2 * c) ≤ |α| * Real.cosh c := by
  have h2 : 0 < Real.cosh (2 * c) := Real.cosh_pos _
  have h1 : 0 < Real.cosh c := Real.cosh_pos _
  show (∀ z : ℂ, twoTone (α / Real.cosh (2 * c)) (β / Real.cosh c) z = 0 → z.im = 0) ↔ _
  rw [twoTone_zeros_real_iff (div_ne_zero hα h2.ne'), abs_div, abs_div,
    abs_of_pos h1, abs_of_pos h2, div_le_div_iff₀ h1 h2]

/-- **The Poisson port destroys real-rootedness of real-rooted sources.** For every `c` and
`cosh c / cosh 2c < r ≤ 1`, the source `cos 2t + r cos t` has only real zeros, but its image under
`sech(cD)` has a non-real zero. The window is nonempty exactly when `c ≠ 0`
(`cosh_lt_cosh_two_mul`). The port amplifies the low tone relative to the high tone by
`cosh(2c)/cosh(c) > 1`. -/
theorem poissonPort_loses_real_zeros {c r : ℝ}
    (hr : Real.cosh c / Real.cosh (2 * c) < r) (hr1 : r ≤ 1) :
    (∀ z : ℂ, twoTone 1 r z = 0 → z.im = 0) ∧
      ∃ z : ℂ, z.im ≠ 0 ∧ portTwoTone c 1 r z = 0 := by
  have h2 : 0 < Real.cosh (2 * c) := Real.cosh_pos _
  have hr0 : 0 < r := lt_trans (div_pos (Real.cosh_pos _) h2) hr
  have hsrc : |r| ≤ |(1 : ℝ)| := by rw [abs_one, abs_of_pos hr0]; exact hr1
  refine ⟨(twoTone_zeros_real_iff one_ne_zero).mpr hsrc, ?_⟩
  by_contra hcon
  push Not at hcon
  have hreal : ∀ z : ℂ, portTwoTone c 1 r z = 0 → z.im = 0 := fun z hz => by
    by_contra him; exact hcon z him hz
  have := (portTwoTone_zeros_real_iff one_ne_zero).mp hreal
  rw [abs_one, one_mul, abs_of_pos hr0] at this
  rw [div_lt_iff₀ h2] at hr
  linarith

/-- The threshold window is nonempty: `cosh c < cosh 2c` for `c ≠ 0`. -/
theorem cosh_lt_cosh_two_mul {c : ℝ} (hc : c ≠ 0) : Real.cosh c < Real.cosh (2 * c) := by
  rw [Real.cosh_lt_cosh, abs_mul, abs_two]
  have : 0 < |c| := abs_pos.mpr hc
  linarith

end RHTower.TwoTonePort
