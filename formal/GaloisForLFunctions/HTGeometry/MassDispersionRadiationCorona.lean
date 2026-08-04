import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Topology.Algebra.Order.Field

/-!
# Radiation corona of exponentially gauged mass dispersion

For the principal dispersion

`sqrt ((xi - i * lambda)^2 + a^2)`,

the two frequency ends retain only the exponential gauge.  The mass disappears
at both ends: the positive end differs from `xi` by `-i * lambda`, while the
negative end differs from `-xi` by `i * lambda`.  Thus any two masses in the
closed chamber `0 ≤ lambda ≤ a` have asymptotically equal gauged dispersions.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

/-- The squared exponentially gauged mass frequency. -/
noncomputable def massGaugeRadicand (a lambda xi : ℝ) : ℂ :=
  ((xi : ℂ) - (lambda : ℂ) * I) ^ 2 + (a ^ 2 : ℝ)

/-- The principal exponentially gauged mass dispersion. -/
noncomputable def massGaugeDispersion (a lambda xi : ℝ) : ℂ :=
  Complex.sqrt (massGaugeRadicand a lambda xi)

@[simp]
theorem massGaugeRadicand_re (a lambda xi : ℝ) :
    (massGaugeRadicand a lambda xi).re = xi ^ 2 + a ^ 2 - lambda ^ 2 := by
  change (((xi : ℂ) - (lambda : ℂ) * I) ^ 2 + (a ^ 2 : ℝ)).re = _
  simp [pow_two, Complex.mul_re]
  ring

@[simp]
theorem massGaugeRadicand_im (a lambda xi : ℝ) :
    (massGaugeRadicand a lambda xi).im = -2 * xi * lambda := by
  change (((xi : ℂ) - (lambda : ℂ) * I) ^ 2 + (a ^ 2 : ℝ)).im = _
  simp [pow_two, Complex.mul_im]
  ring

/-- The principal complex square root squares to the gauged radicand. -/
theorem massGaugeDispersion_sq (a lambda xi : ℝ) :
    massGaugeDispersion a lambda xi ^ 2 = massGaugeRadicand a lambda xi := by
  simp only [massGaugeDispersion, Complex.sqrt]
  exact Complex.cpow_nat_inv_pow _ (by norm_num)

@[simp]
theorem massGaugeDispersion_re (a lambda xi : ℝ) :
    (massGaugeDispersion a lambda xi).re =
      Real.sqrt ((‖massGaugeRadicand a lambda xi‖ +
        (massGaugeRadicand a lambda xi).re) / 2) := by
  simpa [massGaugeDispersion, Complex.sqrt] using
    Complex.cpow_inv_two_re (x := massGaugeRadicand a lambda xi)

/-- In the closed mass chamber, the real principal frequency dominates the
ungauged absolute frequency. -/
theorem abs_le_massGaugeDispersion_re {a lambda : ℝ} (ha : lambda ≤ a)
    (hlambda : 0 ≤ lambda) (xi : ℝ) :
    |xi| ≤ (massGaugeDispersion a lambda xi).re := by
  rw [massGaugeDispersion_re]
  have ha2 : lambda ^ 2 ≤ a ^ 2 := by nlinarith
  have hzre : xi ^ 2 ≤ (massGaugeRadicand a lambda xi).re := by
    rw [massGaugeRadicand_re]
    nlinarith
  have hnorm :
      (massGaugeRadicand a lambda xi).re ≤ ‖massGaugeRadicand a lambda xi‖ :=
    le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
  have hy :
      0 ≤ (‖massGaugeRadicand a lambda xi‖ +
        (massGaugeRadicand a lambda xi).re) / 2 := by
    nlinarith [sq_nonneg xi]
  rw [Real.le_sqrt (abs_nonneg xi) hy, sq_abs]
  nlinarith

/-- At positive frequency infinity, the mass dispersion approaches the
positive gauged line. -/
theorem tendsto_massGaugeDispersion_sub_line_atTop_zero {a lambda : ℝ}
    (ha : lambda ≤ a) (hlambda : 0 ≤ lambda) :
    Tendsto
      (fun xi : ℝ =>
        massGaugeDispersion a lambda xi - ((xi : ℂ) - (lambda : ℂ) * I))
      atTop (nhds 0) := by
  let den : ℝ → ℂ := fun xi =>
    massGaugeDispersion a lambda xi + ((xi : ℂ) - (lambda : ℂ) * I)
  have hden : Tendsto (fun xi : ℝ => ‖den xi‖) atTop atTop := by
    refine tendsto_atTop.2 fun B => ?_
    filter_upwards [eventually_ge_atTop (max 0 (B / 2))] with xi hxi
    have hxi0 : 0 ≤ xi := le_trans (le_max_left _ _) hxi
    have homega : xi ≤ (massGaugeDispersion a lambda xi).re := by
      simpa [abs_of_nonneg hxi0] using
        abs_le_massGaugeDispersion_re ha hlambda xi
    have hre : 2 * xi ≤ (den xi).re := by
      dsimp [den]
      simp only [ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one, sub_zero]
      linarith
    calc
      B ≤ 2 * xi := by nlinarith [le_max_right (0 : ℝ) (B / 2)]
      _ ≤ (den xi).re := hre
      _ ≤ |(den xi).re| := le_abs_self _
      _ ≤ ‖den xi‖ := Complex.abs_re_le_norm _
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hquot : Tendsto (fun xi : ℝ => a ^ 2 / ‖den xi‖) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  apply hquot.congr'
  filter_upwards [eventually_gt_atTop 0] with xi hxi
  have hxi0 : 0 ≤ xi := hxi.le
  have homega : xi ≤ (massGaugeDispersion a lambda xi).re := by
    simpa [abs_of_nonneg hxi0] using
      abs_le_massGaugeDispersion_re ha hlambda xi
  have hdenre : 0 < (den xi).re := by
    dsimp [den]
    simp only [ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one, sub_zero]
    linarith
  have hdenne : den xi ≠ 0 := by
    intro hzero
    have hzre : (den xi).re = 0 := by simpa using congrArg Complex.re hzero
    linarith
  have hprod :
      (massGaugeDispersion a lambda xi - ((xi : ℂ) - (lambda : ℂ) * I)) *
          den xi = (a ^ 2 : ℝ) := by
    dsimp [den]
    calc
      (massGaugeDispersion a lambda xi - ((xi : ℂ) - (lambda : ℂ) * I)) *
          (massGaugeDispersion a lambda xi + ((xi : ℂ) - (lambda : ℂ) * I)) =
          massGaugeDispersion a lambda xi ^ 2 -
            ((xi : ℂ) - (lambda : ℂ) * I) ^ 2 := by ring
      _ = (a ^ 2 : ℝ) := by
        rw [massGaugeDispersion_sq]
        simp [massGaugeRadicand]
  have hrat :
      massGaugeDispersion a lambda xi - ((xi : ℂ) - (lambda : ℂ) * I) =
        (a ^ 2 : ℝ) / den xi :=
    (eq_div_iff hdenne).2 hprod
  rw [hrat, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg a)]

/-- The positive frequency endpoint of the gauged mass dispersion is
`-i * lambda`, independently of mass. -/
theorem tendsto_massGaugeDispersion_sub_atTop {a lambda : ℝ} (ha : lambda ≤ a)
    (hlambda : 0 ≤ lambda) :
    Tendsto (fun xi : ℝ => massGaugeDispersion a lambda xi - (xi : ℂ)) atTop
      (nhds (-(lambda : ℂ) * I)) := by
  have h :=
    (tendsto_massGaugeDispersion_sub_line_atTop_zero ha hlambda).add_const
      (-(lambda : ℂ) * I)
  convert h using 1
  · funext xi
    ring
  · simp

/-- At negative frequency infinity, the mass dispersion approaches the
negative gauged line. -/
theorem tendsto_massGaugeDispersion_add_line_atBot_zero {a lambda : ℝ}
    (ha : lambda ≤ a) (hlambda : 0 ≤ lambda) :
    Tendsto
      (fun xi : ℝ =>
        massGaugeDispersion a lambda xi + ((xi : ℂ) - (lambda : ℂ) * I))
      atBot (nhds 0) := by
  let den : ℝ → ℂ := fun xi =>
    massGaugeDispersion a lambda xi - ((xi : ℂ) - (lambda : ℂ) * I)
  have hden : Tendsto (fun xi : ℝ => ‖den xi‖) atBot atTop := by
    refine tendsto_atTop.2 fun B => ?_
    filter_upwards [eventually_le_atBot (min 0 (-B / 2))] with xi hxi
    have hxi0 : xi ≤ 0 := le_trans hxi (min_le_left _ _)
    have homega : -xi ≤ (massGaugeDispersion a lambda xi).re := by
      simpa [abs_of_nonpos hxi0] using
        abs_le_massGaugeDispersion_re ha hlambda xi
    have hre : -2 * xi ≤ (den xi).re := by
      dsimp [den]
      simp only [ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one, sub_zero]
      linarith
    calc
      B ≤ -2 * xi := by nlinarith [min_le_right (0 : ℝ) (-B / 2)]
      _ ≤ (den xi).re := hre
      _ ≤ |(den xi).re| := le_abs_self _
      _ ≤ ‖den xi‖ := Complex.abs_re_le_norm _
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hquot : Tendsto (fun xi : ℝ => a ^ 2 / ‖den xi‖) atBot (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  apply hquot.congr'
  filter_upwards [eventually_lt_atBot 0] with xi hxi
  have hxi0 : xi ≤ 0 := hxi.le
  have homega : -xi ≤ (massGaugeDispersion a lambda xi).re := by
    simpa [abs_of_nonpos hxi0] using
      abs_le_massGaugeDispersion_re ha hlambda xi
  have hdenre : 0 < (den xi).re := by
    dsimp [den]
    simp only [ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one, sub_zero]
    linarith
  have hdenne : den xi ≠ 0 := by
    intro hzero
    have hzre : (den xi).re = 0 := by simpa using congrArg Complex.re hzero
    linarith
  have hprod :
      (massGaugeDispersion a lambda xi + ((xi : ℂ) - (lambda : ℂ) * I)) *
          den xi = (a ^ 2 : ℝ) := by
    dsimp [den]
    calc
      (massGaugeDispersion a lambda xi + ((xi : ℂ) - (lambda : ℂ) * I)) *
          (massGaugeDispersion a lambda xi - ((xi : ℂ) - (lambda : ℂ) * I)) =
          massGaugeDispersion a lambda xi ^ 2 -
            ((xi : ℂ) - (lambda : ℂ) * I) ^ 2 := by ring
      _ = (a ^ 2 : ℝ) := by
        rw [massGaugeDispersion_sq]
        simp [massGaugeRadicand]
  have hrat :
      massGaugeDispersion a lambda xi + ((xi : ℂ) - (lambda : ℂ) * I) =
        (a ^ 2 : ℝ) / den xi :=
    (eq_div_iff hdenne).2 hprod
  rw [hrat, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg a)]

/-- The negative frequency endpoint of the gauged mass dispersion is
`i * lambda`, independently of mass. -/
theorem tendsto_massGaugeDispersion_add_atBot {a lambda : ℝ} (ha : lambda ≤ a)
    (hlambda : 0 ≤ lambda) :
    Tendsto (fun xi : ℝ => massGaugeDispersion a lambda xi + (xi : ℂ)) atBot
      (nhds ((lambda : ℂ) * I)) := by
  have h :=
    (tendsto_massGaugeDispersion_add_line_atBot_zero ha hlambda).add_const
      ((lambda : ℂ) * I)
  convert h using 1
  · funext xi
    ring
  · simp

/-- Two masses in the same gauge chamber differ by a symbol vanishing at
positive frequency infinity. -/
theorem tendsto_massGaugeDispersion_sub_mass_atTop {a b lambda : ℝ}
    (ha : lambda ≤ a) (hb : lambda ≤ b) (hlambda : 0 ≤ lambda) :
    Tendsto
      (fun xi : ℝ => massGaugeDispersion a lambda xi - massGaugeDispersion b lambda xi)
      atTop (nhds 0) := by
  have ha' := tendsto_massGaugeDispersion_sub_atTop ha hlambda
  have hb' := tendsto_massGaugeDispersion_sub_atTop hb hlambda
  have h := ha'.sub hb'
  convert h using 1
  · funext xi
    ring
  · simp

/-- Two masses in the same gauge chamber differ by a symbol vanishing at
negative frequency infinity. -/
theorem tendsto_massGaugeDispersion_sub_mass_atBot {a b lambda : ℝ}
    (ha : lambda ≤ a) (hb : lambda ≤ b) (hlambda : 0 ≤ lambda) :
    Tendsto
      (fun xi : ℝ => massGaugeDispersion a lambda xi - massGaugeDispersion b lambda xi)
      atBot (nhds 0) := by
  have ha' := tendsto_massGaugeDispersion_add_atBot ha hlambda
  have hb' := tendsto_massGaugeDispersion_add_atBot hb hlambda
  have h := ha'.sub hb'
  convert h using 1
  · funext xi
    ring
  · simp

/-- The positive-end imaginary growth character is exactly `-lambda`. -/
theorem tendsto_massGaugeDispersion_im_atTop {a lambda : ℝ} (ha : lambda ≤ a)
    (hlambda : 0 ≤ lambda) :
    Tendsto (fun xi : ℝ => (massGaugeDispersion a lambda xi).im) atTop
      (nhds (-lambda)) := by
  have h := (Complex.continuous_im.tendsto _).comp
    (tendsto_massGaugeDispersion_sub_atTop ha hlambda)
  simpa [Function.comp_def] using h

/-- The negative-end imaginary growth character is exactly `lambda`. -/
theorem tendsto_massGaugeDispersion_im_atBot {a lambda : ℝ} (ha : lambda ≤ a)
    (hlambda : 0 ≤ lambda) :
    Tendsto (fun xi : ℝ => (massGaugeDispersion a lambda xi).im) atBot
      (nhds lambda) := by
  have h := (Complex.continuous_im.tendsto _).comp
    (tendsto_massGaugeDispersion_add_atBot ha hlambda)
  simpa [Function.comp_def] using h

/-- The real and imaginary parts of the gauged dispersion retain the exact
frequency--gauge product from the radicand. -/
theorem massGaugeDispersion_re_mul_im (a lambda xi : ℝ) :
    2 * (massGaugeDispersion a lambda xi).re *
        (massGaugeDispersion a lambda xi).im = -2 * xi * lambda := by
  have h := congrArg Complex.im (massGaugeDispersion_sq a lambda xi)
  rw [massGaugeRadicand_im] at h
  simp only [pow_two, mul_im] at h
  nlinarith

/-- Inside the open mass chamber, the real part of the gauged dispersion
strictly dominates the absolute frequency. -/
theorem abs_lt_massGaugeDispersion_re {a lambda : ℝ} (ha : lambda < a)
    (hlambda : 0 ≤ lambda) (xi : ℝ) :
    |xi| < (massGaugeDispersion a lambda xi).re := by
  rw [massGaugeDispersion_re]
  have ha2 : lambda ^ 2 < a ^ 2 := by nlinarith
  have hzre : xi ^ 2 < (massGaugeRadicand a lambda xi).re := by
    rw [massGaugeRadicand_re]
    nlinarith
  have hnorm :
      (massGaugeRadicand a lambda xi).re ≤ ‖massGaugeRadicand a lambda xi‖ :=
    le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
  rw [Real.lt_sqrt (abs_nonneg xi), sq_abs]
  nlinarith

/-- At positive frequency, the imaginary dispersion has the opposite sign. -/
theorem massGaugeDispersion_im_neg_of_pos {a lambda xi : ℝ}
    (ha : lambda < a) (hlambda : 0 < lambda) (hxi : 0 < xi) :
    (massGaugeDispersion a lambda xi).im < 0 := by
  have hp : 0 < (massGaugeDispersion a lambda xi).re :=
    lt_of_lt_of_le (abs_pos.mpr hxi.ne')
      (abs_lt_massGaugeDispersion_re ha hlambda.le xi).le
  have heq := massGaugeDispersion_re_mul_im a lambda xi
  nlinarith

/-- At negative frequency, the imaginary dispersion has the gauge sign. -/
theorem massGaugeDispersion_im_pos_of_neg {a lambda xi : ℝ}
    (ha : lambda < a) (hlambda : 0 < lambda) (hxi : xi < 0) :
    0 < (massGaugeDispersion a lambda xi).im := by
  have hp : 0 < (massGaugeDispersion a lambda xi).re :=
    lt_of_lt_of_le (abs_pos.mpr hxi.ne)
      (abs_lt_massGaugeDispersion_re ha hlambda.le xi).le
  have heq := massGaugeDispersion_re_mul_im a lambda xi
  nlinarith

/-- Zero frequency has no imaginary dispersion inside the open chamber. -/
@[simp]
theorem massGaugeDispersion_im_zero (a : ℝ) {lambda : ℝ} (ha : lambda < a)
    (hlambda : 0 ≤ lambda) :
    (massGaugeDispersion a lambda 0).im = 0 := by
  have hp : 0 < (massGaugeDispersion a lambda 0).re := by
    simpa using abs_lt_massGaugeDispersion_re ha hlambda 0
  have heq := massGaugeDispersion_re_mul_im a lambda 0
  nlinarith

/-- The imaginary dispersion lies strictly inside the radiation interval
`(-lambda, lambda)` at every finite frequency. -/
theorem abs_massGaugeDispersion_im_lt {a lambda : ℝ} (ha : lambda < a)
    (hlambda : 0 < lambda) (xi : ℝ) :
    |(massGaugeDispersion a lambda xi).im| < lambda := by
  rcases lt_trichotomy xi 0 with hxi | hxi | hxi
  · have hq : 0 < (massGaugeDispersion a lambda xi).im :=
      massGaugeDispersion_im_pos_of_neg ha hlambda hxi
    rw [abs_of_pos hq]
    have hp : -xi < (massGaugeDispersion a lambda xi).re := by
      simpa [abs_of_neg hxi] using
        abs_lt_massGaugeDispersion_re ha hlambda.le xi
    have heq := massGaugeDispersion_re_mul_im a lambda xi
    have hmul :
        lambda * (-xi) < lambda * (massGaugeDispersion a lambda xi).re :=
      mul_lt_mul_of_pos_left hp hlambda
    nlinarith
  · subst xi
    rw [massGaugeDispersion_im_zero a ha hlambda.le, abs_zero]
    exact hlambda
  · have hq : (massGaugeDispersion a lambda xi).im < 0 :=
      massGaugeDispersion_im_neg_of_pos ha hlambda hxi
    rw [abs_of_neg hq]
    have hp : xi < (massGaugeDispersion a lambda xi).re := by
      simpa [abs_of_pos hxi] using
        abs_lt_massGaugeDispersion_re ha hlambda.le xi
    have hmul :
        lambda * xi < lambda * (massGaugeDispersion a lambda xi).re :=
      mul_lt_mul_of_pos_left hp hlambda
    have heq := massGaugeDispersion_re_mul_im a lambda xi
    nlinarith

/-- Fourier symbol of the gauged massive half-wave at time `u`. -/
noncomputable def massGaugeHalfWaveSymbol (a lambda u xi : ℝ) : ℂ :=
  Complex.exp (-I * (u : ℂ) * massGaugeDispersion a lambda xi)

/-- Exact pointwise norm of the gauged massive half-wave symbol. -/
theorem norm_massGaugeHalfWaveSymbol (a lambda u xi : ℝ) :
    ‖massGaugeHalfWaveSymbol a lambda u xi‖ =
      Real.exp (u * (massGaugeDispersion a lambda xi).im) := by
  rw [massGaugeHalfWaveSymbol, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- The radiation character gives a uniform pointwise symbol bound. -/
theorem norm_massGaugeHalfWaveSymbol_le {a lambda : ℝ} (ha : lambda < a)
    (hlambda : 0 < lambda) (u xi : ℝ) :
    ‖massGaugeHalfWaveSymbol a lambda u xi‖ ≤ Real.exp (|u| * lambda) := by
  rw [norm_massGaugeHalfWaveSymbol]
  apply Real.exp_le_exp.mpr
  calc
    u * (massGaugeDispersion a lambda xi).im ≤
        |u * (massGaugeDispersion a lambda xi).im| := le_abs_self _
    _ = |u| * |(massGaugeDispersion a lambda xi).im| := abs_mul _ _
    _ ≤ |u| * lambda :=
      mul_le_mul_of_nonneg_left
        (abs_massGaugeDispersion_im_lt ha hlambda xi).le (abs_nonneg u)

/-- At the negative frequency end, the symbol norm converges to the outgoing
radiation character. -/
theorem tendsto_norm_massGaugeHalfWaveSymbol_atBot (a lambda u : ℝ)
    (ha : lambda ≤ a) (hlambda : 0 ≤ lambda) :
    Tendsto (fun xi : ℝ => ‖massGaugeHalfWaveSymbol a lambda u xi‖) atBot
      (nhds (Real.exp (u * lambda))) := by
  simp_rw [norm_massGaugeHalfWaveSymbol]
  exact (Real.continuous_exp.tendsto _).comp
    (tendsto_const_nhds.mul (tendsto_massGaugeDispersion_im_atBot ha hlambda))

/-- At the positive frequency end, the symbol norm converges to the incoming
radiation character. -/
theorem tendsto_norm_massGaugeHalfWaveSymbol_atTop (a lambda u : ℝ)
    (ha : lambda ≤ a) (hlambda : 0 ≤ lambda) :
    Tendsto (fun xi : ℝ => ‖massGaugeHalfWaveSymbol a lambda u xi‖) atTop
      (nhds (Real.exp (u * (-lambda)))) := by
  simp_rw [norm_massGaugeHalfWaveSymbol]
  exact (Real.continuous_exp.tendsto _).comp
    (tendsto_const_nhds.mul (tendsto_massGaugeDispersion_im_atTop ha hlambda))

/-- The exponential radiation envelope is optimal: it is the least uniform
upper bound for the symbol norm. -/
theorem massGaugeHalfWaveSymbol_bound_iff {a lambda : ℝ} (ha : lambda < a)
    (hlambda : 0 < lambda) (u C : ℝ) :
    (∀ xi : ℝ, ‖massGaugeHalfWaveSymbol a lambda u xi‖ ≤ C) ↔
      Real.exp (|u| * lambda) ≤ C := by
  constructor
  · intro h
    by_cases hu : 0 ≤ u
    · have hlim :=
        tendsto_norm_massGaugeHalfWaveSymbol_atBot a lambda u ha.le hlambda.le
      have hle : Real.exp (u * lambda) ≤ C := le_of_tendsto' hlim h
      simpa [abs_of_nonneg hu] using hle
    · have hu' : u < 0 := lt_of_not_ge hu
      have hlim :=
        tendsto_norm_massGaugeHalfWaveSymbol_atTop a lambda u ha.le hlambda.le
      have hle : Real.exp (u * (-lambda)) ≤ C := le_of_tendsto' hlim h
      simpa [abs_of_neg hu'] using hle
  · intro h xi
    exact (norm_massGaugeHalfWaveSymbol_le ha hlambda u xi).trans h

end GaloisForLFunctions.HTGeometry
