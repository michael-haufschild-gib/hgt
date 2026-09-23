import GaloisForLFunctions.HTGeometry.DigammaGaussSeries
import GaloisForLFunctions.HTGeometry.ExplicitDigammaHerglotzPalette
import GaloisForLFunctions.RHTower.XiWardInteriorTraceSplit

/-!
# The real part of digamma is minimised on the real axis

On every vertical line in the right half-plane the real part of the digamma function attains its
minimum at the real point:

`psi(a) <= Re (psi (a + i y))`   for `a > 0` and every real `y`.

The mechanism is the Gauss series `psi(s) = -gamma + sum_n [1/(n+1) - 1/(s+n)]`: each subtracted
term contributes `Re (1/(a + n + i y)) = (a+n)/((a+n)^(2 : ℕ) + y^(2 : ℕ))`, which is largest at `y = 0`, so
every summand of the series is smallest there.

This is the archimedean primitive behind the large-time half of the completely-monotone question
for the archimedean part of the Euler-ray response: it turns the Gaussian archimedean integral into
`>= psi(1/4)` times the Gaussian mass, uniformly in the height.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- On a vertical line, the real part of a Gauss digamma summand is minimal on the real axis. -/
theorem re_gaussDigammaSeriesTerm_real_le {a : ℝ} (ha : 0 < a) (y : ℝ) (n : ℕ) :
    (gaussDigammaSeriesTerm ((a : ℂ)) n).re ≤
      (gaussDigammaSeriesTerm ((a : ℂ) + (y : ℂ) * Complex.I) n).re := by
  have hpos : 0 < a + (n : ℝ) := by positivity
  have hden : ((a : ℂ) + (y : ℂ) * Complex.I + (n : ℂ)) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, Complex.natCast_re, Complex.zero_re] at hre
    simp at hre
    linarith
  have hdenR : ((a : ℂ) + (n : ℂ)) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp only [Complex.add_re, Complex.ofReal_re, Complex.natCast_re, Complex.zero_re] at hre
    linarith
  have hR : (1 / ((a : ℂ) + (n : ℂ))).re = 1 / (a + (n : ℝ)) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.natCast_re, Complex.natCast_im]
    field_simp
    ring
  have hC : (1 / ((a : ℂ) + (y : ℂ) * Complex.I + (n : ℂ))).re =
      (a + (n : ℝ)) / ((a + (n : ℝ)) ^ (2 : ℕ) + y ^ (2 : ℕ)) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.natCast_re,
      Complex.natCast_im]
    ring_nf
  have hkey : (a + (n : ℝ)) / ((a + (n : ℝ)) ^ (2 : ℕ) + y ^ (2 : ℕ)) ≤ 1 / (a + (n : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (a + (n : ℝ)) ^ (2 : ℕ) + y ^ (2 : ℕ)) hpos]
    nlinarith [sq_nonneg y, hpos]
  rw [gaussDigammaSeriesTerm, gaussDigammaSeriesTerm, Complex.sub_re, Complex.sub_re,
    hR, hC]
  linarith

/-- **The real part of digamma on a vertical line is at least its value at the real point.** -/
theorem digamma_real_le_re_digamma_add_mul_I {a : ℝ} (ha : 0 < a) (y : ℝ) :
    (Complex.digamma ((a : ℂ))).re ≤
      (Complex.digamma ((a : ℂ) + (y : ℂ) * Complex.I)).re := by
  have hreR : ((a : ℂ)).re = a := Complex.ofReal_re a
  have hreC : ((a : ℂ) + (y : ℂ) * Complex.I).re = a := by
    simp [Complex.add_re, Complex.mul_re]
  have hsR := digamma_eq_neg_euler_add_tsum_gauss (s := (a : ℂ)) (by rw [hreR]; exact ha)
  have hsC := digamma_eq_neg_euler_add_tsum_gauss
    (s := (a : ℂ) + (y : ℂ) * Complex.I) (by rw [hreC]; exact ha)
  have hsumR : Summable (fun n : ℕ => gaussDigammaSeriesTerm ((a : ℂ)) n) :=
    summable_norm_iff.mp
      (GaloisForLFunctions.HTGeometry.summable_norm_gaussDigammaSeriesTerm_all _)
  have hsumC : Summable (fun n : ℕ =>
      gaussDigammaSeriesTerm ((a : ℂ) + (y : ℂ) * Complex.I) n) :=
    summable_norm_iff.mp
      (GaloisForLFunctions.HTGeometry.summable_norm_gaussDigammaSeriesTerm_all _)
  rw [hsR, hsC, Complex.add_re, Complex.add_re, Complex.re_tsum hsumR,
    Complex.re_tsum hsumC]
  have hle : ∑' n : ℕ, (gaussDigammaSeriesTerm ((a : ℂ)) n).re ≤
      ∑' n : ℕ, (gaussDigammaSeriesTerm ((a : ℂ) + (y : ℂ) * Complex.I) n).re := by
    refine Summable.tsum_le_tsum (fun n => re_gaussDigammaSeriesTerm_real_le ha y n)
      ((Complex.hasSum_re hsumR.hasSum).summable)
      ((Complex.hasSum_re hsumC.hasSum).summable)
  linarith


/-- **The archimedean logarithmic derivative is minimised on the real axis.**  For every positive
real abscissa the real part of `logDeriv Gamma_R` on the vertical line is at least its value at the
real point.  This is the archimedean half of a completed-explicit-formula domination: the
archimedean contribution never helps a zero by dipping below its real-axis value. -/
theorem re_logDeriv_Gammaℝ_real_le {σ : ℝ} (hσ : 0 < σ) (y : ℝ) :
    (logDeriv Complex.Gammaℝ ((σ : ℂ))).re ≤
      (logDeriv Complex.Gammaℝ ((σ : ℂ) + (y : ℂ) * Complex.I)).re := by
  have hreR : ((σ : ℂ)).re = σ := Complex.ofReal_re σ
  have hreC : ((σ : ℂ) + (y : ℂ) * Complex.I).re = σ := by
    simp [Complex.add_re, Complex.mul_re]
  rw [logDeriv_Gammaℝ_eq (by rw [hreR]; exact hσ),
    logDeriv_Gammaℝ_eq (by rw [hreC]; exact hσ)]
  have hhalfR : ((σ : ℂ)) / 2 = (((σ / 2 : ℝ)) : ℂ) := by
    push_cast; ring
  have hhalfC : ((σ : ℂ) + (y : ℂ) * Complex.I) / 2 =
      (((σ / 2 : ℝ)) : ℂ) + (((y / 2 : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hhalfR, hhalfC]
  set A : ℂ := Complex.digamma (((σ / 2 : ℝ)) : ℂ) with hA
  set B : ℂ := Complex.digamma ((((σ / 2 : ℝ)) : ℂ) +
    (((y / 2 : ℝ)) : ℂ) * Complex.I) with hB
  have hre : ∀ z : ℂ, (-((Real.log Real.pi : ℂ) / 2) + z / 2).re =
      -(Real.log Real.pi / 2) + z.re / 2 := by
    intro z
    simp [Complex.add_re]
  rw [hre A, hre B]
  have hmin := digamma_real_le_re_digamma_add_mul_I (a := σ / 2) (by linarith) (y / 2)
  rw [← hA, ← hB] at hmin
  linarith


/-! ## Monotonicity in the height -/

/-- Real part of the resolvent atom on a vertical line. -/
theorem re_one_div_vertical (a y : ℝ) (n : ℕ) :
    (1 / ((a : ℂ) + (y : ℂ) * Complex.I + (n : ℂ))).re =
      (a + (n : ℝ)) / ((a + (n : ℝ)) ^ (2 : ℕ) + y ^ (2 : ℕ)) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.natCast_re,
    Complex.natCast_im]
  ring_nf

/-- Each Gauss digamma summand increases with the height. -/
theorem re_gaussDigammaSeriesTerm_mono {a : ℝ} (ha : 0 < a) {y z : ℝ}
    (hyz : |y| ≤ |z|) (n : ℕ) :
    (gaussDigammaSeriesTerm ((a : ℂ) + (y : ℂ) * Complex.I) n).re ≤
      (gaussDigammaSeriesTerm ((a : ℂ) + (z : ℂ) * Complex.I) n).re := by
  have hpos : 0 < a + (n : ℝ) := by positivity
  have hsq : y ^ (2 : ℕ) ≤ z ^ (2 : ℕ) := by
    have := sq_abs y
    have := sq_abs z
    nlinarith [abs_nonneg y, abs_nonneg z, hyz]
  have hcmp : (a + (n : ℝ)) / ((a + (n : ℝ)) ^ (2 : ℕ) + z ^ (2 : ℕ)) ≤
      (a + (n : ℝ)) / ((a + (n : ℝ)) ^ (2 : ℕ) + y ^ (2 : ℕ)) := by
    apply div_le_div_of_nonneg_left hpos.le (by positivity)
    linarith
  rw [gaussDigammaSeriesTerm, gaussDigammaSeriesTerm, Complex.sub_re, Complex.sub_re,
    re_one_div_vertical a y n, re_one_div_vertical a z n]
  linarith

/-- **The real part of digamma increases with the height.**  On every vertical line in the right
half-plane, `Re psi(a + i y)` is a nondecreasing function of `|y|`. -/
theorem re_digamma_mono_of_abs_le {a : ℝ} (ha : 0 < a) {y z : ℝ} (hyz : |y| ≤ |z|) :
    (Complex.digamma ((a : ℂ) + (y : ℂ) * Complex.I)).re ≤
      (Complex.digamma ((a : ℂ) + (z : ℂ) * Complex.I)).re := by
  have hreY : ((a : ℂ) + (y : ℂ) * Complex.I).re = a := by
    simp [Complex.add_re, Complex.mul_re]
  have hreZ : ((a : ℂ) + (z : ℂ) * Complex.I).re = a := by
    simp [Complex.add_re, Complex.mul_re]
  have hsY := digamma_eq_neg_euler_add_tsum_gauss
    (s := (a : ℂ) + (y : ℂ) * Complex.I) (by rw [hreY]; exact ha)
  have hsZ := digamma_eq_neg_euler_add_tsum_gauss
    (s := (a : ℂ) + (z : ℂ) * Complex.I) (by rw [hreZ]; exact ha)
  have hsumY : Summable (fun n : ℕ =>
      gaussDigammaSeriesTerm ((a : ℂ) + (y : ℂ) * Complex.I) n) :=
    summable_norm_iff.mp
      (GaloisForLFunctions.HTGeometry.summable_norm_gaussDigammaSeriesTerm_all _)
  have hsumZ : Summable (fun n : ℕ =>
      gaussDigammaSeriesTerm ((a : ℂ) + (z : ℂ) * Complex.I) n) :=
    summable_norm_iff.mp
      (GaloisForLFunctions.HTGeometry.summable_norm_gaussDigammaSeriesTerm_all _)
  rw [hsY, hsZ, Complex.add_re, Complex.add_re, Complex.re_tsum hsumY,
    Complex.re_tsum hsumZ]
  have hle := Summable.tsum_le_tsum
    (fun n => re_gaussDigammaSeriesTerm_mono ha hyz n)
    ((Complex.hasSum_re hsumY.hasSum).summable)
    ((Complex.hasSum_re hsumZ.hasSum).summable)
  linarith

end

end RHTower
