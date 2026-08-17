import GaloisForLFunctions.HTGeometry.MassGaugeDampedSymbol
import GaloisForLFunctions.HTGeometry.MassGaugeDispersionExpansion

/-!
# The damped symbol on an outgoing band at sub-linear frequency scale

Placing the frequency band at `-r` with `r = u^q`, `1/2 < q < 1`, the damped symbol restricted to
the band is, after dividing by its value at the band centre, exactly the plane wave `e^{(σ+iu)η}`
times a factor tending to one.

The mechanism is the outgoing expansion: the increment of the dispersion across the band is the
increment of the plane wave up to `O(η/r²) + O(r^{-3})`, and multiplying by `σ + iu` costs
`O(u^{1-2q}) + O(u^{1-3q})`, which vanishes exactly because `q > 1/2`.  This is the scale at which
the analytic damping is still negligible on the exponential clock while the mass correction has
already been resolved.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- An affine numerator against a super-linear power vanishes. -/
theorem tendsto_add_div_rpow_atTop {sigma p : ℝ} (hp : 1 < p) :
    Tendsto (fun u : ℝ => (sigma + u) / u ^ p) atTop (𝓝 0) := by
  have h1 : Tendsto (fun u : ℝ => sigma * u ^ (-p)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < p)).const_mul sigma
    simpa using this
  have h2 : Tendsto (fun u : ℝ => u ^ (1 - p)) atTop (𝓝 0) := by
    have heq : (1 : ℝ) - p = -(p - 1) := by ring
    rw [funext fun u : ℝ => congrArg (fun e : ℝ => u ^ e) heq]
    exact tendsto_rpow_neg_atTop (by linarith)
  have hsum := h1.add h2
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  have hup : (0 : ℝ) < u ^ p := Real.rpow_pos_of_pos hu _
  rw [Real.rpow_neg hu.le, show (1 : ℝ) - p = 1 + -p by ring, Real.rpow_add hu,
    Real.rpow_neg hu.le, Real.rpow_one]
  field_simp

/-- **(24.51) The quantitative band exponent bound.**  On a band of radius `r/2` about `-r` the
exponent that separates the damped symbol from its band-centre plane wave is at most
`(σ+u)(a²|η|/r² + 3a⁴/r³)`. -/
theorem norm_dampedBandExponent_le {a lambda sigma u r eta : ℝ} (hsigma : 0 ≤ sigma)
    (hu : 0 ≤ u) (hr : 0 < r) (heta : |eta| ≤ r / 2) :
    ‖((sigma : ℂ) + (u : ℝ) * Complex.I)
        * (massGaugeDispersion a lambda (eta - r) - massGaugeDispersion a lambda (-r)
          + (eta : ℂ))‖
      ≤ (sigma + u) * (a ^ 2 * |eta| / r ^ 2 + 3 * a ^ 4 / r ^ 3) := by
  have habs0 : 0 ≤ |eta| := abs_nonneg eta
  have hetar : |eta| < r := by linarith
  have hhalf : r / 2 ≤ r - |eta| := by linarith
  have hpos : (0 : ℝ) < r - |eta| := by linarith
  have hincr := norm_massGaugeDispersion_increment_le (a := a) (lambda := lambda) hr hetar
  have hcoef : ‖((sigma : ℂ) + (u : ℝ) * Complex.I)‖ ≤ sigma + u := by
    refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
    simp [abs_of_nonneg hsigma, abs_of_nonneg hu]
  have hb1 : a ^ 2 * |eta| / (2 * (r - |eta|) * r) ≤ a ^ 2 * |eta| / r ^ 2 := by
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    nlinarith [hhalf, hr]
  have hb2 : a ^ 4 / (4 * (r - |eta|) ^ 3) ≤ 2 * (a ^ 4 / r ^ 3) := by
    have hstep : a ^ 4 / (4 * (r - |eta|) ^ 3) ≤ a ^ 4 / (4 * (r / 2) ^ 3) := by
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      gcongr
    have hval : a ^ 4 / (4 * (r / 2) ^ 3) = 2 * (a ^ 4 / r ^ 3) := by
      field_simp
      ring
    linarith [hstep, hval]
  have hb3 : a ^ 4 / (4 * r ^ 3) ≤ 1 * (a ^ 4 / r ^ 3) := by
    rw [one_mul]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    nlinarith [pow_pos hr 3]
  have hsum : a ^ 2 * |eta| / (2 * (r - |eta|) * r)
      + a ^ 4 / (4 * (r - |eta|) ^ 3) + a ^ 4 / (4 * r ^ 3)
      ≤ a ^ 2 * |eta| / r ^ 2 + 3 * a ^ 4 / r ^ 3 := by
    have h3eq : 3 * a ^ 4 / r ^ 3 = 3 * (a ^ 4 / r ^ 3) := by ring
    rw [h3eq]
    linarith
  calc ‖((sigma : ℂ) + (u : ℝ) * Complex.I)
        * (massGaugeDispersion a lambda (eta - r) - massGaugeDispersion a lambda (-r)
          + (eta : ℂ))‖
      = ‖((sigma : ℂ) + (u : ℝ) * Complex.I)‖
        * ‖massGaugeDispersion a lambda (eta - r) - massGaugeDispersion a lambda (-r)
          + (eta : ℂ)‖ := norm_mul _ _
    _ ≤ (sigma + u) * (a ^ 2 * |eta| / (2 * (r - |eta|) * r)
          + a ^ 4 / (4 * (r - |eta|) ^ 3) + a ^ 4 / (4 * r ^ 3)) :=
        mul_le_mul hcoef hincr (norm_nonneg _) (by linarith)
    _ ≤ (sigma + u) * (a ^ 2 * |eta| / r ^ 2 + 3 * a ^ 4 / r ^ 3) :=
        mul_le_mul_of_nonneg_left hsum (by linarith)

/-- **(24.51) The quantitative band ratio.**  On the band the damped symbol differs from its
band-centre value times the plane wave `e^{(σ+iu)η}` by at most `|N| e^{ση}` times twice the band
exponent. -/
theorem norm_dampedBand_sub_model_le {a lambda sigma u r eta : ℝ}
    (hsmall : ‖((sigma : ℂ) + (u : ℝ) * Complex.I)
      * (massGaugeDispersion a lambda (eta - r) - massGaugeDispersion a lambda (-r)
        + (eta : ℂ))‖ ≤ 1) :
    ‖massGaugeDampedSymbol a lambda sigma u (eta - r)
        - massGaugeDampedSymbol a lambda sigma u (-r)
          * Complex.exp (((sigma : ℂ) + (u : ℝ) * Complex.I) * (eta : ℂ))‖
      ≤ ‖massGaugeDampedSymbol a lambda sigma u (-r)‖ * Real.exp (sigma * eta)
        * (2 * ‖((sigma : ℂ) + (u : ℝ) * Complex.I)
          * (massGaugeDispersion a lambda (eta - r) - massGaugeDispersion a lambda (-r)
            + (eta : ℂ))‖) := by
  set c : ℂ := (sigma : ℂ) + (u : ℝ) * Complex.I with hc
  set z : ℂ := c * (massGaugeDispersion a lambda (eta - r) - massGaugeDispersion a lambda (-r)
    + (eta : ℂ)) with hz
  have hfactor : massGaugeDampedSymbol a lambda sigma u (eta - r)
      = massGaugeDampedSymbol a lambda sigma u (-r) * Complex.exp (c * (eta : ℂ))
        * Complex.exp (-z) := by
    rw [massGaugeDampedSymbol, massGaugeDampedSymbol, ← Complex.exp_add, ← Complex.exp_add, hz]
    congr 1
    ring
  have hphase : ‖Complex.exp (c * (eta : ℂ))‖ = Real.exp (sigma * eta) := by
    rw [Complex.norm_exp]
    congr 1
    rw [hc]
    simp [Complex.mul_re, Complex.add_re, Complex.add_im]
  have hdiff : massGaugeDampedSymbol a lambda sigma u (eta - r)
      - massGaugeDampedSymbol a lambda sigma u (-r) * Complex.exp (c * (eta : ℂ))
      = massGaugeDampedSymbol a lambda sigma u (-r) * Complex.exp (c * (eta : ℂ))
        * (Complex.exp (-z) - 1) := by
    rw [hfactor]
    ring
  rw [hdiff, norm_mul, norm_mul, hphase]
  have hexp : ‖Complex.exp (-z) - 1‖ ≤ 2 * ‖z‖ := by
    have hnorm : ‖-z‖ ≤ 1 := by
      rw [norm_neg]
      exact hsmall
    have := Complex.norm_exp_sub_one_le hnorm
    rwa [norm_neg] at this
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- **(24.51)** The band exponent vanishes at sub-linear frequency scale. -/
theorem tendsto_dampedBandExponent {a lambda sigma q eta : ℝ} (hsigma : 0 ≤ sigma)
    (hq : 1 / 2 < q) (heta : 0 ≤ eta) :
    Tendsto (fun u : ℝ => ((sigma : ℂ) + (u : ℝ) * Complex.I)
        * (massGaugeDispersion a lambda (eta - u ^ q) - massGaugeDispersion a lambda (-(u ^ q))
          + (eta : ℂ))) atTop (𝓝 0) := by
  have hq0 : 0 < q := by linarith
  have hmaj : Tendsto (fun u : ℝ =>
      (sigma + u) * (a ^ 2 * eta / u ^ (2 * q) + 3 * a ^ 4 / u ^ (3 * q))) atTop (𝓝 0) := by
    have h2 : Tendsto (fun u : ℝ => (sigma + u) / u ^ (2 * q)) atTop (𝓝 0) :=
      tendsto_add_div_rpow_atTop (by linarith)
    have h3 : Tendsto (fun u : ℝ => (sigma + u) / u ^ (3 * q)) atTop (𝓝 0) :=
      tendsto_add_div_rpow_atTop (by linarith)
    have hsum := (h2.const_mul (a ^ 2 * eta)).add (h3.const_mul (3 * a ^ 4))
    rw [mul_zero, mul_zero, add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have h2p : (0 : ℝ) < u ^ (2 * q) := Real.rpow_pos_of_pos hu _
    have h3p : (0 : ℝ) < u ^ (3 * q) := Real.rpow_pos_of_pos hu _
    field_simp
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop hq0).eventually_ge_atTop (2 * eta + 1)] with u hu1 hur
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu1
  have hr0 : (0 : ℝ) < u ^ q := Real.rpow_pos_of_pos hu0 _
  have hetar : eta < u ^ q := by linarith
  have hhalf : u ^ q / 2 ≤ u ^ q - eta := by linarith
  have hpos : (0 : ℝ) < u ^ q - eta := by linarith
  have hincr := norm_massGaugeDispersion_increment_le (a := a) (lambda := lambda) hr0
    (by rw [abs_of_nonneg heta]; exact hetar)
  rw [abs_of_nonneg heta] at hincr
  have hcoef : ‖((sigma : ℂ) + (u : ℝ) * Complex.I)‖ ≤ sigma + u := by
    refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
    simp [abs_of_nonneg hsigma, abs_of_nonneg hu0.le]
  have hsq : u ^ (2 * q) = (u ^ q) ^ 2 := by
    rw [mul_comm, Real.rpow_mul hu0.le]
    norm_num
  have hcu : u ^ (3 * q) = (u ^ q) ^ 3 := by
    rw [mul_comm, Real.rpow_mul hu0.le]
    norm_num
  have hbandbound : a ^ 2 * eta / (2 * (u ^ q - eta) * u ^ q)
      + a ^ 4 / (4 * (u ^ q - eta) ^ 3) + a ^ 4 / (4 * (u ^ q) ^ 3)
      ≤ a ^ 2 * eta / u ^ (2 * q) + 3 * a ^ 4 / u ^ (3 * q) := by
    rw [hsq, hcu]
    have hb1 : a ^ 2 * eta / (2 * (u ^ q - eta) * u ^ q) ≤ a ^ 2 * eta / (u ^ q) ^ 2 := by
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      nlinarith [hhalf, hr0]
    have hb2 : a ^ 4 / (4 * (u ^ q - eta) ^ 3) ≤ 2 * (a ^ 4 / (u ^ q) ^ 3) := by
      have hstep : a ^ 4 / (4 * (u ^ q - eta) ^ 3) ≤ a ^ 4 / (4 * (u ^ q / 2) ^ 3) := by
        refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
        gcongr
      have hval : a ^ 4 / (4 * (u ^ q / 2) ^ 3) = 2 * (a ^ 4 / (u ^ q) ^ 3) := by
        field_simp
        ring
      linarith [hstep, hval]
    have hb3 : a ^ 4 / (4 * (u ^ q) ^ 3) ≤ 1 * (a ^ 4 / (u ^ q) ^ 3) := by
      rw [one_mul]
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      nlinarith [pow_pos hr0 3]
    have h3eq : 3 * a ^ 4 / (u ^ q) ^ 3 = 3 * (a ^ 4 / (u ^ q) ^ 3) := by ring
    rw [h3eq]
    linarith
  calc ‖((sigma : ℂ) + (u : ℝ) * Complex.I)
        * (massGaugeDispersion a lambda (eta - u ^ q) - massGaugeDispersion a lambda (-(u ^ q))
          + (eta : ℂ))‖
      = ‖((sigma : ℂ) + (u : ℝ) * Complex.I)‖
        * ‖massGaugeDispersion a lambda (eta - u ^ q) - massGaugeDispersion a lambda (-(u ^ q))
          + (eta : ℂ)‖ := norm_mul _ _
    _ ≤ (sigma + u) * (a ^ 2 * eta / (2 * (u ^ q - eta) * u ^ q)
          + a ^ 4 / (4 * (u ^ q - eta) ^ 3) + a ^ 4 / (4 * (u ^ q) ^ 3)) :=
        mul_le_mul hcoef hincr (norm_nonneg _) (by linarith)
    _ ≤ (sigma + u) * (a ^ 2 * eta / u ^ (2 * q) + 3 * a ^ 4 / u ^ (3 * q)) :=
        mul_le_mul_of_nonneg_left hbandbound (by linarith)

/-- **(24.51)** After removing the plane wave, the damped symbol on the band is asymptotically its
value at the band centre. -/
theorem tendsto_dampedBandRatio {a lambda sigma q eta : ℝ} (hsigma : 0 ≤ sigma)
    (hq : 1 / 2 < q) (heta : 0 ≤ eta) :
    Tendsto (fun u : ℝ => massGaugeDampedSymbol a lambda sigma u (eta - u ^ q)
        * Complex.exp (((sigma : ℂ) + (u : ℝ) * Complex.I)
          * massGaugeDispersion a lambda (-(u ^ q)))
        * Complex.exp (-((sigma : ℂ) + (u : ℝ) * Complex.I) * (eta : ℂ)))
      atTop (𝓝 1) := by
  have hexp := tendsto_dampedBandExponent (a := a) (lambda := lambda) hsigma hq heta
  have hneg : Tendsto (fun u : ℝ => -(((sigma : ℂ) + (u : ℝ) * Complex.I)
      * (massGaugeDispersion a lambda (eta - u ^ q) - massGaugeDispersion a lambda (-(u ^ q))
        + (eta : ℂ)))) atTop (𝓝 0) := by
    simpa using hexp.neg
  have hcont := (Complex.continuous_exp.tendsto 0).comp hneg
  simp only [Complex.exp_zero, Function.comp_def] at hcont
  refine hcont.congr fun u => ?_
  rw [massGaugeDampedSymbol, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-- **(24.51) The band-centre scalar has exponential type `λ`.**  The damping costs only `σ r`,
which is `o(u)` at every sub-linear frequency scale, while the radiation gain is the full `λ`. -/
theorem tendsto_log_norm_dampedSymbol_center {a lambda sigma q : ℝ} (ha : lambda ≤ a)
    (hlambda : 0 ≤ lambda) (hsigma : 0 ≤ sigma) (hq0 : 0 < q) (hq1 : q < 1) :
    Tendsto (fun u : ℝ => Real.log ‖massGaugeDampedSymbol a lambda sigma u (-(u ^ q))‖ / u)
      atTop (𝓝 lambda) := by
  have hIm : Tendsto (fun u : ℝ => (massGaugeDispersion a lambda (-(u ^ q))).im) atTop
      (𝓝 lambda) := by
    have hbot : Tendsto (fun u : ℝ => -(u ^ q)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_rpow_atTop hq0)
    exact (tendsto_massGaugeDispersion_im_atBot ha hlambda).comp hbot
  have hmaj : Tendsto (fun u : ℝ =>
      sigma * (u ^ q + a ^ 2 / (2 * u ^ q) + a ^ 4 / (4 * (u ^ q) ^ 3)) / u) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => sigma * u ^ (-(1 - q))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < 1 - q)).const_mul sigma
    have h2 : Tendsto (fun u : ℝ => (sigma * a ^ 2 / 2) * u ^ (-(q + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < q + 1)).const_mul
        (sigma * a ^ 2 / 2)
    have h3 : Tendsto (fun u : ℝ => (sigma * a ^ 4 / 4) * u ^ (-(3 * q + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < 3 * q + 1)).const_mul
        (sigma * a ^ 4 / 4)
    have hsum := (h1.add h2).add h3
    rw [add_zero, add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have hr : (0 : ℝ) < u ^ q := Real.rpow_pos_of_pos hu _
    have hcube : (u ^ q) ^ 3 = u ^ (3 * q) := by
      rw [← Real.rpow_natCast (u ^ q) 3, ← Real.rpow_mul hu.le]
      congr 1
      ring
    have h3p : (0 : ℝ) < u ^ (3 * q) := Real.rpow_pos_of_pos hu _
    have e1 : u ^ (-(1 - q)) = u ^ q / u := by
      rw [show -(1 - q) = q - 1 by ring, Real.rpow_sub hu, Real.rpow_one]
    have e2 : u ^ (-(q + 1)) = 1 / (u ^ q * u) := by
      rw [show -(q + 1) = -q - 1 by ring, Real.rpow_sub hu, Real.rpow_neg hu.le, Real.rpow_one]
      field_simp
    have e3 : u ^ (-(3 * q + 1)) = 1 / (u ^ (3 * q) * u) := by
      rw [show -(3 * q + 1) = -(3 * q) - 1 by ring, Real.rpow_sub hu, Real.rpow_neg hu.le,
        Real.rpow_one]
      field_simp
    rw [hcube, e1, e2, e3]
    field_simp
  have hRe : Tendsto (fun u : ℝ => sigma * (massGaugeDispersion a lambda (-(u ^ q))).re / u)
      atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hmaj
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      have hnn : 0 ≤ (massGaugeDispersion a lambda (-(u ^ q))).re := sqrt_re_nonneg _
      positivity
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      have hr : (0 : ℝ) < u ^ q := Real.rpow_pos_of_pos hu _
      have hle := massGaugeDispersion_re_le (a := a) (lambda := lambda) hr
      have hmul : sigma * (massGaugeDispersion a lambda (-(u ^ q))).re
          ≤ sigma * (u ^ q + a ^ 2 / (2 * u ^ q) + a ^ 4 / (4 * (u ^ q) ^ 3)) :=
        mul_le_mul_of_nonneg_left hle hsigma
      exact div_le_div_of_nonneg_right hmul hu.le
  have hsum := hIm.add hRe.neg
  rw [neg_zero, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  rw [norm_massGaugeDampedSymbol, Real.log_exp]
  field_simp
  ring

/-- The imaginary part of the dispersion approaches `λ` fast enough that the approach is invisible
on the exponential clock: `u(λ − Im ω(−u^q)) → 0` for every `q > 1/2`. -/
theorem tendsto_mul_im_sub_lambda {a lambda q : ℝ} (hlambda : 0 ≤ lambda) (hq : 1 / 2 < q) :
    Tendsto (fun u : ℝ => u * ((massGaugeDispersion a lambda (-(u ^ q))).im - lambda))
      atTop (𝓝 0) := by
  have hq0 : 0 < q := by linarith
  have hmaj : Tendsto (fun u : ℝ =>
      u * (a ^ 2 * lambda / (2 * (u ^ q) ^ 2) + a ^ 4 / (4 * (u ^ q) ^ 3))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => (a ^ 2 * lambda / 2) * u ^ (-(2 * q - 1))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < 2 * q - 1)).const_mul
        (a ^ 2 * lambda / 2)
    have h2 : Tendsto (fun u : ℝ => (a ^ 4 / 4) * u ^ (-(3 * q - 1))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < 3 * q - 1)).const_mul
        (a ^ 4 / 4)
    have hsum := h1.add h2
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have hr : (0 : ℝ) < u ^ q := Real.rpow_pos_of_pos hu _
    have hsq : (u ^ q) ^ 2 = u ^ (2 * q) := by
      rw [← Real.rpow_natCast (u ^ q) 2, ← Real.rpow_mul hu.le]
      congr 1
      ring
    have hcu : (u ^ q) ^ 3 = u ^ (3 * q) := by
      rw [← Real.rpow_natCast (u ^ q) 3, ← Real.rpow_mul hu.le]
      congr 1
      ring
    have h2p : (0 : ℝ) < u ^ (2 * q) := Real.rpow_pos_of_pos hu _
    have h3p : (0 : ℝ) < u ^ (3 * q) := Real.rpow_pos_of_pos hu _
    have e1 : u ^ (-(2 * q - 1)) = u / u ^ (2 * q) := by
      rw [show -(2 * q - 1) = 1 - 2 * q by ring, Real.rpow_sub hu, Real.rpow_one]
    have e2 : u ^ (-(3 * q - 1)) = u / u ^ (3 * q) := by
      rw [show -(3 * q - 1) = 1 - 3 * q by ring, Real.rpow_sub hu, Real.rpow_one]
    rw [hsq, hcu, e1, e2]
    field_simp
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  have hr : (0 : ℝ) < u ^ q := Real.rpow_pos_of_pos hu _
  have hlt : (-(u ^ q) : ℝ) < 0 := by linarith
  have hbound := norm_massGaugeDispersion_sub_le (a := a) (lambda := lambda) hlt
  set z0 : ℂ := outgoingBase lambda (-(u ^ q)) with hz0
  have hz0re : z0.re = u ^ q := by
    rw [hz0, outgoingBase_re]
    ring
  have hz0im : z0.im = lambda := by
    rw [hz0, outgoingBase_im]
  have hz0sq : ‖z0‖ ^ 2 = (u ^ q) ^ 2 + lambda ^ 2 := by
    rw [hz0, normSq_outgoingBase]
    ring
  have hdivim : (((a : ℝ) : ℂ) ^ 2 / (2 * z0)).im = -(a ^ 2 * lambda / (2 * ‖z0‖ ^ 2)) := by
    have hns : Complex.normSq z0 = ‖z0‖ ^ 2 := Complex.normSq_eq_norm_sq z0
    rw [Complex.div_im]
    simp [Complex.normSq_mul, hns, hz0re, hz0im, pow_two]
    field_simp
  have hsplit : (massGaugeDispersion a lambda (-(u ^ q))).im - lambda
      = (massGaugeDispersion a lambda (-(u ^ q)) - (z0 + ((a : ℝ) : ℂ) ^ 2 / (2 * z0))).im
        + (((a : ℝ) : ℂ) ^ 2 / (2 * z0)).im := by
    simp only [Complex.sub_im, Complex.add_im, hz0im]
    ring
  have hrem : |(massGaugeDispersion a lambda (-(u ^ q))
      - (z0 + ((a : ℝ) : ℂ) ^ 2 / (2 * z0))).im| ≤ a ^ 4 / (4 * (u ^ q) ^ 3) := by
    refine le_trans (Complex.abs_im_le_norm _) (le_trans hbound ?_)
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    nlinarith [sq_nonneg lambda, hr, mul_pos hr hr]
  have hdiv : |(((a : ℝ) : ℂ) ^ 2 / (2 * z0)).im| ≤ a ^ 2 * lambda / (2 * (u ^ q) ^ 2) := by
    rw [hdivim, abs_neg, abs_of_nonneg (by positivity)]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    rw [hz0sq]
    nlinarith [sq_nonneg lambda, hr]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hu, hsplit]
  have habs := abs_add_le (massGaugeDispersion a lambda (-(u ^ q))
    - (z0 + ((a : ℝ) : ℂ) ^ 2 / (2 * z0))).im (((a : ℝ) : ℂ) ^ 2 / (2 * z0)).im
  have hsumb : |(massGaugeDispersion a lambda (-(u ^ q))
      - (z0 + ((a : ℝ) : ℂ) ^ 2 / (2 * z0))).im + (((a : ℝ) : ℂ) ^ 2 / (2 * z0)).im|
      ≤ a ^ 2 * lambda / (2 * (u ^ q) ^ 2) + a ^ 4 / (4 * (u ^ q) ^ 3) := by
    linarith [habs, hrem, hdiv]
  exact mul_le_mul_of_nonneg_left hsumb hu.le


/-- **An explicit lower bound for the band-centre scalar.**  The only losses are the saturation
defect of the radiation gain and the damping cost at the band centre. -/
theorem le_log_norm_dampedSymbol_center {a lambda sigma q : ℝ} (hsigma : 0 ≤ sigma)
    {u : ℝ} (hu : 0 < u) :
    lambda * u - u * (lambda - (massGaugeDispersion a lambda (-(u ^ q))).im)
        - sigma * (u ^ q + a ^ 2 / (2 * u ^ q) + a ^ 4 / (4 * (u ^ q) ^ 3))
      ≤ Real.log ‖massGaugeDampedSymbol a lambda sigma u (-(u ^ q))‖ := by
  have hr : (0 : ℝ) < u ^ q := Real.rpow_pos_of_pos hu _
  have hre := massGaugeDispersion_re_le (a := a) (lambda := lambda) hr
  rw [norm_massGaugeDampedSymbol, Real.log_exp]
  have hmul : sigma * (massGaugeDispersion a lambda (-(u ^ q))).re
      ≤ sigma * (u ^ q + a ^ 2 / (2 * u ^ q) + a ^ 4 / (4 * (u ^ q) ^ 3)) :=
    mul_le_mul_of_nonneg_left hre hsigma
  nlinarith [hmul]


end GaloisForLFunctions.HTGeometry
