import GaloisForLFunctions.RHTower.XiGuinandWeilContourSynthesis

/-!
# The Gaussian–Hermite test function for the Xi contour synthesis

The rectangle synthesis law of `XiGuinandWeilContourSynthesis` accepts an arbitrary entire test
function `g` and returns the enclosed divisor values.  Passing from a rectangle to the full divisor
requires the top and bottom edges of the rectangle to become negligible, and for the rectangular
window that is a substantial estimate.

For the Gaussian–Hermite test

`G t n s = (s - 1/2)^(2n) * exp (t * (s - 1/2)^2)`,  `t > 0`,

it is immediate.  Its modulus is

`‖G t n s‖ = ‖s - 1/2‖^(2n) * exp (t * ((Re s - 1/2)^2 - (Im s)^2))`,

so on any vertical strip of bounded width the function decays like `exp(-t y^2)` in the height: the
horizontal edges of a tall rectangle contribute nothing in the limit, and the two vertical edges
converge absolutely.  This is the property that makes the Gaussian carrier cheap where the
rectangular one is expensive.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The Gaussian–Hermite test function, centered at the critical line. -/
def xiGaussianTest (t : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  (s - 1 / 2) ^ (2 * n) * Complex.exp ((t : ℂ) * (s - 1 / 2) ^ 2)

theorem differentiable_xiGaussianTest (t : ℝ) (n : ℕ) :
    Differentiable ℂ (xiGaussianTest t n) := by
  unfold xiGaussianTest
  fun_prop

theorem analyticOnNhd_xiGaussianTest (t : ℝ) (n : ℕ) :
    AnalyticOnNhd ℂ (xiGaussianTest t n) Set.univ := fun z _ =>
  ((differentiable_xiGaussianTest t n).differentiableOn (s := Set.univ)).analyticOnNhd
    isOpen_univ z (Set.mem_univ z)

/-- The real part of the Gaussian exponent: positive horizontally, negative vertically. -/
theorem re_gaussianExponent (t : ℝ) (s : ℂ) :
    ((t : ℂ) * (s - 1 / 2) ^ 2).re =
      t * ((s.re - 1 / 2) ^ 2 - s.im ^ 2) := by
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, pow_two,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.div_re,
    Complex.div_im, Complex.one_re, Complex.one_im, Complex.re_ofNat,
    Complex.im_ofNat, Complex.normSq_apply]
  ring_nf

/-- **The modulus of the Gaussian–Hermite test.** -/
theorem norm_xiGaussianTest (t : ℝ) (n : ℕ) (s : ℂ) :
    ‖xiGaussianTest t n s‖ =
      ‖s - 1 / 2‖ ^ (2 * n) *
        Real.exp (t * ((s.re - 1 / 2) ^ 2 - s.im ^ 2)) := by
  rw [xiGaussianTest, norm_mul, norm_pow, Complex.norm_exp, re_gaussianExponent]

/-- **Vertical decay on a strip of bounded width.**  On the horizontal segment at height `y`, with
`|Re s - 1/2| <= R`, the test function is bounded by a Gaussian in `y` times a polynomial factor —
so a tall rectangle's horizontal edges are negligible. -/
theorem norm_xiGaussianTest_le_of_strip {t : ℝ} (ht : 0 < t) (n : ℕ) {R : ℝ}
    (hR : 0 ≤ R) {s : ℂ} (hre : |s.re - 1 / 2| ≤ R) :
    ‖xiGaussianTest t n s‖ ≤
      (R + |s.im|) ^ (2 * n) * Real.exp (t * R ^ 2) *
        Real.exp (-(t * s.im ^ 2)) := by
  rw [norm_xiGaussianTest]
  have hnorm : ‖s - 1 / 2‖ ≤ R + |s.im| := by
    have hre' : (s - 1 / 2).re = s.re - 1 / 2 := by
      simp [Complex.sub_re]
    have him' : (s - 1 / 2).im = s.im := by
      simp [Complex.sub_im]
    calc
      ‖s - 1 / 2‖ ≤ |(s - 1 / 2).re| + |(s - 1 / 2).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |s.re - 1 / 2| + |s.im| := by rw [hre', him']
      _ ≤ R + |s.im| := by linarith
  have hpow : ‖s - 1 / 2‖ ^ (2 * n) ≤ (R + |s.im|) ^ (2 * n) :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm _
  have hexp : Real.exp (t * ((s.re - 1 / 2) ^ 2 - s.im ^ 2)) ≤
      Real.exp (t * R ^ 2) * Real.exp (-(t * s.im ^ 2)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have hsq : (s.re - 1 / 2) ^ 2 ≤ R ^ 2 := by
      have := abs_nonneg (s.re - 1 / 2)
      nlinarith [sq_abs (s.re - 1 / 2), hre, hR]
    nlinarith [ht.le, hsq]
  have hnn : (0 : ℝ) ≤ Real.exp (t * ((s.re - 1 / 2) ^ 2 - s.im ^ 2)) :=
    (Real.exp_pos _).le
  calc
    ‖s - 1 / 2‖ ^ (2 * n) * Real.exp (t * ((s.re - 1 / 2) ^ 2 - s.im ^ 2))
        ≤ (R + |s.im|) ^ (2 * n) *
            Real.exp (t * ((s.re - 1 / 2) ^ 2 - s.im ^ 2)) :=
          mul_le_mul_of_nonneg_right hpow hnn
    _ ≤ (R + |s.im|) ^ (2 * n) *
            (Real.exp (t * R ^ 2) * Real.exp (-(t * s.im ^ 2))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (R + |s.im|) ^ (2 * n) * Real.exp (t * R ^ 2) *
            Real.exp (-(t * s.im ^ 2)) := by ring


/-! ## The horizontal edge vanishes -/

/-- **Gaussian decay beats polynomial growth.**  This is the estimate that makes the horizontal
edges of a tall rectangle negligible for the Gaussian--Hermite test, and it is exactly what the
rectangular window lacks. -/
theorem tendsto_polyGaussian_atTop {t : ℝ} (ht : 0 < t) (n : ℕ) (R : ℝ) :
    Filter.Tendsto (fun Y : ℝ => (R + |Y|) ^ n * Real.exp (-(t * Y ^ 2)))
      Filter.atTop (nhds 0) := by
  have hlin : Filter.Tendsto (fun Y : ℝ => t * Y) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop ht Filter.tendsto_id
  have hcomp : Filter.Tendsto (fun Y : ℝ => (t * Y) ^ n * Real.exp (-(t * Y)))
      Filter.atTop (nhds 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp hlin
  have hconst : Filter.Tendsto
      (fun Y : ℝ => (2 ^ n / t ^ n) * ((t * Y) ^ n * Real.exp (-(t * Y))))
      Filter.atTop (nhds 0) := by
    simpa using hcomp.const_mul (2 ^ n / t ^ n)
  refine squeeze_zero' ?_ ?_ hconst
  · filter_upwards [Filter.eventually_ge_atTop |R|] with Y hY
    have hRY : -R ≤ |Y| :=
      le_trans (le_trans (neg_le_abs R) hY) (le_abs_self Y)
    have : 0 ≤ R + |Y| := by linarith
    positivity
  · filter_upwards [Filter.eventually_ge_atTop |R|, Filter.eventually_ge_atTop (1 : ℝ)]
      with Y hYR hY1
    have hYpos : 0 < Y := lt_of_lt_of_le one_pos hY1
    have habsY : |Y| = Y := abs_of_pos hYpos
    have hRle : R ≤ |R| := le_abs_self R
    have hbase : R + |Y| ≤ 2 * Y := by rw [habsY]; linarith
    have hbase0 : 0 ≤ R + |Y| := by rw [habsY]; linarith [neg_le_abs R]
    have hpow : (R + |Y|) ^ n ≤ (2 * Y) ^ n := pow_le_pow_left₀ hbase0 hbase n
    have hexp : Real.exp (-(t * Y ^ 2)) ≤ Real.exp (-(t * Y)) := by
      rw [Real.exp_le_exp]
      nlinarith [mul_nonneg hYpos.le (sub_nonneg.mpr hY1), ht.le, hYpos.le]
    have hkey : (2 * Y) ^ n * Real.exp (-(t * Y)) =
        (2 ^ n / t ^ n) * ((t * Y) ^ n * Real.exp (-(t * Y))) := by
      rw [mul_pow, mul_pow]
      field_simp
    calc
      (R + |Y|) ^ n * Real.exp (-(t * Y ^ 2))
          ≤ (2 * Y) ^ n * Real.exp (-(t * Y ^ 2)) :=
            mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
      _ ≤ (2 * Y) ^ n * Real.exp (-(t * Y)) := by
            apply mul_le_mul_of_nonneg_left hexp
            positivity
      _ = (2 ^ n / t ^ n) * ((t * Y) ^ n * Real.exp (-(t * Y))) := hkey


/-! ## The vertical edge converges absolutely -/

/-- On a vertical line the Gaussian--Hermite test is dominated by a half-width Gaussian: the
polynomial factor is absorbed because `u^n exp(-c u) <= n! / c^n`. -/
theorem norm_xiGaussianTest_vertical_le {t : ℝ} (ht : 0 < t) (n : ℕ) (c y : ℝ) :
    ‖xiGaussianTest t n ((c : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      (Real.exp (t * (c - 1 / 2) ^ 2) * Real.exp (t / 2 * (c - 1 / 2) ^ 2) *
        ((n.factorial : ℝ) / (t / 2) ^ n)) * Real.exp (-(t / 2 * y ^ 2)) := by
  have hre : ((c : ℂ) + (y : ℂ) * Complex.I).re = c := by
    simp [Complex.add_re, Complex.mul_re]
  have him : ((c : ℂ) + (y : ℂ) * Complex.I).im = y := by
    simp [Complex.add_im, Complex.mul_im]
  have hnormsq : ‖(c : ℂ) + (y : ℂ) * Complex.I - 1 / 2‖ ^ (2 * n) =
      ((c - 1 / 2) ^ 2 + y ^ 2) ^ n := by
    rw [pow_mul, Complex.sq_norm, Complex.normSq_apply]
    congr 1
    simp only [Complex.sub_re, Complex.sub_im, hre, him, Complex.div_re, Complex.div_im,
      Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.normSq_apply]
    ring_nf
  set u : ℝ := (c - 1 / 2) ^ 2 + y ^ 2 with hu
  have hunn : 0 ≤ u := by positivity
  have hhalf : 0 < t / 2 := by linarith
  -- the factorial absorption `u ^ n * exp (-(t/2) u) <= n! / (t/2)^n`
  have habs : u ^ n * Real.exp (-(t / 2 * u)) ≤ (n.factorial : ℝ) / (t / 2) ^ n := by
    have hfac : 0 < (n.factorial : ℝ) := by positivity
    have hcpow : 0 < (t / 2) ^ n := pow_pos hhalf n
    have hseries := Real.pow_div_factorial_le_exp (t / 2 * u)
      (mul_nonneg hhalf.le hunn) n
    rw [div_le_iff₀ hfac] at hseries
    have hmul := mul_le_mul_of_nonneg_right hseries (Real.exp_pos (-(t / 2 * u))).le
    have hcancel : Real.exp (t / 2 * u) * Real.exp (-(t / 2 * u)) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    apply (le_div_iff₀ hcpow).2
    calc
      u ^ n * Real.exp (-(t / 2 * u)) * (t / 2) ^ n =
          (t / 2 * u) ^ n * Real.exp (-(t / 2 * u)) := by rw [mul_pow]; ring
      _ ≤ Real.exp (t / 2 * u) * (n.factorial : ℝ) * Real.exp (-(t / 2 * u)) := hmul
      _ = (n.factorial : ℝ) := by
          rw [mul_comm (Real.exp (t / 2 * u)) ((n.factorial : ℝ)), mul_assoc, hcancel,
            mul_one]
  rw [norm_xiGaussianTest, hnormsq, hre, him]
  have hsplit : Real.exp (t * ((c - 1 / 2) ^ 2 - y ^ 2)) =
      Real.exp (t * (c - 1 / 2) ^ 2) * Real.exp (t / 2 * (c - 1 / 2) ^ 2) *
        Real.exp (-(t / 2 * u)) * Real.exp (-(t / 2 * y ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hu]
    ring
  rw [hsplit]
  have hK : 0 ≤ Real.exp (t * (c - 1 / 2) ^ 2) * Real.exp (t / 2 * (c - 1 / 2) ^ 2) := by
    positivity
  have hE : 0 ≤ Real.exp (-(t / 2 * y ^ 2)) := (Real.exp_pos _).le
  calc
    u ^ n * (Real.exp (t * (c - 1 / 2) ^ 2) * Real.exp (t / 2 * (c - 1 / 2) ^ 2) *
        Real.exp (-(t / 2 * u)) * Real.exp (-(t / 2 * y ^ 2)))
        = (Real.exp (t * (c - 1 / 2) ^ 2) * Real.exp (t / 2 * (c - 1 / 2) ^ 2)) *
            (u ^ n * Real.exp (-(t / 2 * u))) * Real.exp (-(t / 2 * y ^ 2)) := by ring
    _ ≤ (Real.exp (t * (c - 1 / 2) ^ 2) * Real.exp (t / 2 * (c - 1 / 2) ^ 2)) *
            ((n.factorial : ℝ) / (t / 2) ^ n) * Real.exp (-(t / 2 * y ^ 2)) := by
          apply mul_le_mul_of_nonneg_right _ hE
          exact mul_le_mul_of_nonneg_left habs hK

/-- **The vertical edge converges absolutely.**  The Gaussian--Hermite test is integrable along
every vertical line, so the two vertical edges of the exhausting rectangle have well-defined
limits. -/
theorem integrable_xiGaussianTest_vertical {t : ℝ} (ht : 0 < t) (n : ℕ) (c : ℝ) :
    MeasureTheory.Integrable
      (fun y : ℝ => xiGaussianTest t n ((c : ℂ) + (y : ℂ) * Complex.I)) := by
  have hhalf : 0 < t / 2 := by linarith
  have hcont : Continuous
      (fun y : ℝ => xiGaussianTest t n ((c : ℂ) + (y : ℂ) * Complex.I)) := by
    unfold xiGaussianTest
    fun_prop
  refine MeasureTheory.Integrable.mono'
    (((integrable_exp_neg_mul_sq hhalf).const_mul
      (Real.exp (t * (c - 1 / 2) ^ 2) * Real.exp (t / 2 * (c - 1 / 2) ^ 2) *
        ((n.factorial : ℝ) / (t / 2) ^ n))))
    hcont.aestronglyMeasurable ?_
  filter_upwards with y
  simpa using norm_xiGaussianTest_vertical_le ht n c y

end

end RHTower
