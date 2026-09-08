import GaloisForLFunctions.RHTower.SelbergScatteringPolynomialReality
import GaloisForLFunctions.HTGeometry.EvenEntireSquareFactor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# An entire transform of the native modular scattering Casimir

Even-entire square descent constructs `F` with `F (1/4 + w²) = cosh (8πw)`.
On the critical scattering parabola this is `cosh (4πz)`. The transform is entire
and is not any polynomial. Its real-native values lie in `[-1, ∞)` and exceed
one exactly above the quarter. Both the quarter and `3/16` map to one.

Inside the open centered Xi strip, away from zero real coordinate, membership
of the transformed scattering parameter in the real half-line `[-1, ∞)`
characterizes the critical line. This constructs a transform and classifier;
it does not construct spectral occurrence or an operator domain.
-/

open Complex
open GaloisForLFunctions.HTGeometry
open RHTower.SelbergScatteringPolynomialReality

namespace RHTower.SelbergScatteringEntireTransform
noncomputable section

/-- Entire square descent in the native Casimir coordinate, with no global square-root choice. -/
def casimirTransform (lam : ℂ) : ℂ :=
  evenEntireSquareFactor (fun w : ℂ => Complex.cosh (8 * Real.pi * w)) (lam - 1 / 4)

private theorem entire_cosh_scaled :
    Differentiable ℂ (fun w : ℂ => Complex.cosh (8 * Real.pi * w)) :=
  Complex.differentiable_cosh.comp ((differentiable_const _).mul differentiable_id)

private theorem even_cosh_scaled :
    Function.Even (fun w : ℂ => Complex.cosh (8 * Real.pi * w)) := by
  intro w
  simp only [mul_neg, Complex.cosh_neg]

/-- The native Casimir transform is entire. -/
theorem differentiable_casimirTransform : Differentiable ℂ casimirTransform :=
  (differentiable_evenEntireSquareFactor entire_cosh_scaled).comp
    (differentiable_id.sub_const _)

/-- Exact descent identity on the quadratic cover centered at the quarter. -/
theorem casimirTransform_sq (w : ℂ) :
    casimirTransform (1 / 4 + w ^ 2) = Complex.cosh (8 * Real.pi * w) := by
  simp only [casimirTransform, add_sub_cancel_left]
  exact evenEntireSquareFactor_sq entire_cosh_scaled even_cosh_scaled w

/-- The original scattering Casimir maps to a periodic hyperbolic cosine. -/
theorem casimirTransform_criticalCasimir (z : ℂ) :
    casimirTransform (criticalCasimir z) = Complex.cosh (4 * Real.pi * z) := by
  have hk : criticalCasimir z = 1 / 4 + ((z + I / 2) / 2) ^ 2 := by
    dsimp [criticalCasimir]
    ring_nf
    simp only [I_sq]
    ring
  rw [hk, casimirTransform_sq]
  convert Complex.cosh_periodic (4 * Real.pi * z) using 1
  congr 1
  ring

/-- Above the quarter, the native transform is a real hyperbolic cosine. -/
theorem casimirTransform_of_ge_quarter (lam : ℝ) (hlam : 1 / 4 ≤ lam) :
    casimirTransform lam = (Real.cosh (8 * Real.pi * Real.sqrt (lam - 1 / 4)) : ℂ) := by
  have hs : (Real.sqrt (lam - 1 / 4) : ℂ) ^ 2 = (lam : ℂ) - 1 / 4 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (sub_nonneg.mpr hlam)]
    push_cast
    rfl
  have h := casimirTransform_sq (Real.sqrt (lam - 1 / 4))
  rw [hs] at h
  have ha : (1 / 4 : ℂ) + (lam - 1 / 4) = lam := by ring
  rw [ha] at h
  simpa only [← Complex.ofReal_mul, ← Complex.ofReal_ofNat, ← Complex.ofReal_cosh] using h

/-- Below the quarter, the native transform is a real cosine. -/
theorem casimirTransform_of_le_quarter (lam : ℝ) (hlam : lam ≤ 1 / 4) :
    casimirTransform lam = (Real.cos (8 * Real.pi * Real.sqrt (1 / 4 - lam)) : ℂ) := by
  have hs : (Real.sqrt (1 / 4 - lam) : ℂ) ^ 2 = 1 / 4 - (lam : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (sub_nonneg.mpr hlam)]
    push_cast
    rfl
  have h := casimirTransform_sq ((Real.sqrt (1 / 4 - lam) : ℂ) * I)
  rw [mul_pow, hs, I_sq] at h
  have ha : (1 / 4 : ℂ) + (1 / 4 - lam) * -1 = lam := by ring
  rw [ha, ← mul_assoc, Complex.cosh_mul_I] at h
  simpa only [← Complex.ofReal_mul, ← Complex.ofReal_ofNat, ← Complex.ofReal_cos] using h

/-- Every real native parameter has a real transform bounded below by minus one. -/
theorem casimirTransform_real_range (lam : ℝ) :
    (casimirTransform lam).im = 0 ∧ -1 ≤ (casimirTransform lam).re := by
  rcases le_total (1 / 4 : ℝ) lam with hlam | hlam
  · rw [casimirTransform_of_ge_quarter lam hlam]
    simpa only [Complex.ofReal_im, Complex.ofReal_re, true_and] using
      (show -1 ≤ Real.cosh (8 * Real.pi * Real.sqrt (lam - 1 / 4)) from
        le_trans (by norm_num) (Real.one_le_cosh _))
  · rw [casimirTransform_of_le_quarter lam hlam]
    simpa only [Complex.ofReal_im, Complex.ofReal_re, true_and] using
      Real.neg_one_le_cos (8 * Real.pi * Real.sqrt (1 / 4 - lam))

/-- The strict transformed threshold detects exactly the open native quarter range. -/
theorem one_lt_casimirTransform_iff (lam : ℝ) :
    1 < (casimirTransform lam).re ↔ 1 / 4 < lam := by
  constructor
  · intro h
    by_contra hn
    rw [casimirTransform_of_le_quarter lam (le_of_not_gt hn), Complex.ofReal_re] at h
    exact (not_lt_of_ge (Real.cos_le_one _)) h
  · intro h
    rw [casimirTransform_of_ge_quarter lam h.le, Complex.ofReal_re,
      Real.one_lt_cosh]
    exact ne_of_gt (mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (Real.sqrt_pos.mpr (sub_pos.mpr h)))

/-- The native spectral threshold maps to one. -/
theorem casimirTransform_quarter : casimirTransform (1 / 4) = 1 := by
  simpa using casimirTransform_sq 0

/-- The non-strict threshold has an exact complementary-parameter alias at `3/16`. -/
theorem casimirTransform_alias : casimirTransform (3 / 16) = 1 := by
  have h := casimirTransform_criticalCasimir 0
  simpa [criticalCasimir] using h

/-- The closed native quarter range maps into the real half-line starting at one. -/
theorem casimirTransform_native_quarter (lam : ℝ) (hlam : 1 / 4 ≤ lam) :
    (casimirTransform lam).im = 0 ∧ 1 ≤ (casimirTransform lam).re := by
  rw [casimirTransform_of_ge_quarter lam hlam]
  simpa only [Complex.ofReal_im, Complex.ofReal_re, true_and] using Real.one_le_cosh _

/-- Every real critical scattering parameter has a real hyperbolic-cosine transform. -/
theorem casimirTransform_critical_real (t : ℝ) :
    casimirTransform (criticalCasimir t) = (Real.cosh (4 * Real.pi * t) : ℂ) := by
  rw [casimirTransform_criticalCasimir]
  push_cast
  rfl

/-- This entire transform escapes the complete fixed-polynomial obstruction. -/
theorem casimirTransform_not_polynomial :
    ¬ ∃ P : Polynomial ℂ, ∀ w : ℂ, P.eval w = casimirTransform w := by
  rintro ⟨P, hP⟩
  have hreal : Set.Infinite {t : ℝ | (P.eval (criticalCasimir t)).im = 0} := by
    simpa only [hP, casimirTransform_critical_real, Complex.ofReal_im,
      Set.setOf_true] using (Set.infinite_univ : Set.Infinite (Set.univ : Set ℝ))
  obtain ⟨c, hc⟩ := constant_of_infinite_real_locus P hreal
  have he_const (t : ℝ) : (c : ℂ) = (Real.cosh (4 * Real.pi * t) : ℂ) := by
    calc
      (c : ℂ) = P.eval (criticalCasimir t) := by rw [hc, Polynomial.eval_C]
      _ = casimirTransform (criticalCasimir t) := hP _
      _ = _ := casimirTransform_critical_real t
  have hh := congrArg Complex.re ((he_const 1).symm.trans (he_const 0))
  simp only [Complex.ofReal_re, mul_zero, Real.cosh_zero] at hh
  have hgt : 1 < Real.cosh (4 * Real.pi * 1) :=
    Real.one_lt_cosh.mpr (ne_of_gt (by positivity))
  linarith

private theorem cosh_components (z : ℂ) :
    (Complex.cosh z).re = Real.cosh z.re * Real.cos z.im ∧
    (Complex.cosh z).im = Real.sinh z.re * Real.sin z.im := by
  have hz : Complex.cosh z =
      (Real.cosh z.re : ℂ) * (Real.cos z.im : ℂ) +
      (Real.sinh z.re : ℂ) * (Real.sin z.im : ℂ) * I := by
    calc
      Complex.cosh z = Complex.cosh ((z.re : ℂ) + (z.im : ℂ) * I) :=
        congrArg Complex.cosh (Complex.re_add_im z).symm
      _ = _ := by
        rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
          ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
          ← Complex.ofReal_cos, ← Complex.ofReal_sin]
        ring
  simp only [hz, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    I_re, I_im, Complex.add_im, Complex.mul_im]
  constructor <;> ring

/-- Exact real and imaginary components on the scattering Casimir cover. -/
theorem casimirTransform_critical_components (z : ℂ) :
    (casimirTransform (criticalCasimir z)).re =
      Real.cosh (4 * Real.pi * z.re) * Real.cos (4 * Real.pi * z.im) ∧
    (casimirTransform (criticalCasimir z)).im =
      Real.sinh (4 * Real.pi * z.re) * Real.sin (4 * Real.pi * z.im) := by
  rw [casimirTransform_criticalCasimir]
  simpa using cosh_components (4 * Real.pi * z)

/-- Within the open Xi strip at nonzero height, the full native real range detects critical placement. -/
theorem critical_strip_range_iff (z : ℂ) (hre : z.re ≠ 0)
    (hlo : -(1 / 2 : ℝ) < z.im) (hhi : z.im < 1 / 2) :
    ((casimirTransform (criticalCasimir z)).im = 0 ∧
      -1 ≤ (casimirTransform (criticalCasimir z)).re) ↔ z.im = 0 := by
  obtain ⟨hreal, himag⟩ := casimirTransform_critical_components z
  have hnonzero : 4 * Real.pi * z.re ≠ 0 := mul_ne_zero (by positivity) hre
  have hcosh := Real.one_lt_cosh.mpr hnonzero
  constructor
  · rintro ⟨hi, hr⟩
    rw [himag] at hi
    have hsin := (mul_eq_zero.mp hi).resolve_left (Real.sinh_ne_zero.mpr hnonzero)
    have hc : Real.cos (4 * Real.pi * z.im) = 1 := by
      rcases Real.sin_eq_zero_iff_cos_eq.mp hsin with hc | hc
      · exact hc
      · rw [hreal, hc, mul_neg_one] at hr
        linarith
    have ha : 4 * Real.pi * z.im = 0 :=
      (Real.cos_eq_one_iff_of_lt_of_lt (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos])).mp hc
    exact (mul_eq_zero.mp ha).resolve_left (by positivity)
  · intro hz
    rw [hreal, himag, hz, mul_zero, Real.cos_zero, Real.sin_zero, mul_zero, mul_one]
    exact ⟨rfl, by linarith⟩

/-- Within the open Xi strip at nonzero height, the native quarter range detects critical placement. -/
theorem critical_strip_quarter_range_iff (z : ℂ) (hre : z.re ≠ 0)
    (hlo : -(1 / 2 : ℝ) < z.im) (hhi : z.im < 1 / 2) :
    ((casimirTransform (criticalCasimir z)).im = 0 ∧
      1 ≤ (casimirTransform (criticalCasimir z)).re) ↔ z.im = 0 := by
  constructor
  · rintro ⟨hi, hr⟩
    exact (critical_strip_range_iff z hre hlo hhi).mp ⟨hi, by linarith⟩
  · intro hz
    obtain ⟨hr, hi⟩ := casimirTransform_critical_components z
    rw [hr, hi, hz, mul_zero, Real.cos_zero, Real.sin_zero, mul_zero, mul_one]
    exact ⟨rfl, Real.one_le_cosh _⟩

end
end RHTower.SelbergScatteringEntireTransform
