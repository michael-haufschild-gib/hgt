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
  have hincr := norm_massGaugeDispersion_increment_le (a := a) (lambda := lambda) hr0 heta hetar
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

end GaloisForLFunctions.HTGeometry
