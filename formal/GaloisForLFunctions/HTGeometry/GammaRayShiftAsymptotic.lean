import GaloisForLFunctions.HTGeometry.GammaComplexShiftIntegral
import GaloisForLFunctions.HTGeometry.DigammaHalfPlaneAsymptotic

/-!
# The Gamma shift ratio along a complex ray

Let `α` have positive real part and let `w` be a fixed complex shift.  Along the ray
`z_n = 1 + α n` the ratio of two Gamma values differs from the corresponding complex power by
`1 + o(1)`:

`Γ(1 + α n + w) / (Γ(1 + α n) · (1 + α n)^w) ⟶ 1`.

The mechanism is the complex-direction shift law together with the half-plane digamma asymptotic:
the exponent is `∫₀¹ w (ψ(z_n + u w) − log z_n) du`, and both `ψ(ζ) − log ζ` and
`log(z_n + u w) − log z_n` are `O(1/‖z_n‖)`.

The companion statement replaces the base point by the pure ray point: `(1 + α n)^w` and
`α^w n^w` differ by `1 + o(1)` as well, because the principal logarithm is additive on
`α · n` for a positive integer `n` and a direction of positive real part.
-/

open Filter Set Topology Function intervalIntegral

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-! ## The ray base point -/

/-- The base point of the ray. -/
def rayPoint (α : ℂ) (n : ℕ) : ℂ := 1 + α * (n : ℂ)

theorem rayPoint_re (α : ℂ) (n : ℕ) : (rayPoint α n).re = 1 + n * α.re := by
  simp [rayPoint, Complex.add_re, Complex.mul_re]
  ring

theorem rayPoint_re_pos {α : ℂ} (hre : 0 < α.re) (n : ℕ) : 0 < (rayPoint α n).re := by
  rw [rayPoint_re]
  have := Nat.cast_nonneg (α := ℝ) n
  nlinarith

theorem rayPoint_re_le_norm (α : ℂ) (n : ℕ) : (rayPoint α n).re ≤ ‖rayPoint α n‖ :=
  Complex.re_le_norm _

theorem rayPoint_ne_zero {α : ℂ} (hre : 0 < α.re) (n : ℕ) : rayPoint α n ≠ 0 := by
  intro h
  have := rayPoint_re_pos hre n
  rw [h] at this
  simp at this

theorem tendsto_rayPoint_re_atTop {α : ℂ} (hre : 0 < α.re) :
    Tendsto (fun n : ℕ => (rayPoint α n).re) atTop atTop := by
  refine Tendsto.congr (fun n => (rayPoint_re α n).symm) ?_
  exact Filter.tendsto_atTop_add_const_left atTop 1
    (Filter.Tendsto.atTop_mul_const hre tendsto_natCast_atTop_atTop)

/-- The principal logarithm of a small unit perturbation is at most twice the perturbation. -/
theorem norm_log_one_add_le_two_mul {ξ : ℂ} (h : ‖ξ‖ ≤ 1 / 2) :
    ‖Complex.log (1 + ξ)‖ ≤ 2 * ‖ξ‖ := by
  have hlt : ‖ξ‖ < 1 := by linarith
  have hbound := Complex.norm_log_sub_logTaylor_le 0 hlt (z := ξ)
  have htay : Complex.logTaylor 1 ξ = 0 := by
    rw [Complex.logTaylor]
    simp
  rw [htay, sub_zero] at hbound
  norm_num at hbound
  have hinv : (1 - ‖ξ‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  nlinarith [norm_nonneg ξ, hbound, hinv]

/-! ## The logarithm along the ray -/

/-- The principal logarithm is additive along a positive-real-part direction scaled by a positive
integer. -/
theorem log_mul_natCast_of_re_pos {α : ℂ} (hre : 0 < α.re) {n : ℕ} (hn : 1 ≤ n) :
    Complex.log (α * (n : ℂ)) = Complex.log α + Complex.log (n : ℂ) := by
  have hα : α ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : ((n : ℂ)) ≠ 0 := by
    simpa using (ne_of_gt hnpos)
  have hargn : Complex.arg ((n : ℂ)) = 0 := by
    rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) from by push_cast; ring]
    exact Complex.arg_ofReal_of_nonneg (le_of_lt hnpos)
  have hargα : |Complex.arg α| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  refine (Complex.log_mul_eq_add_log_iff hα hn0).mpr ?_
  rw [hargn, add_zero]
  have hpi : 0 < Real.pi := Real.pi_pos
  constructor
  · have := (abs_lt.mp hargα).1
    linarith
  · have := (abs_lt.mp hargα).2
    linarith

/-- The complex power of a positive-real-part direction scaled by a positive integer splits. -/
theorem cpow_mul_natCast_of_re_pos {α : ℂ} (hre : 0 < α.re) (w : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    (α * (n : ℂ)) ^ w = α ^ w * (n : ℂ) ^ w := by
  have hα : α ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : ((n : ℂ)) ≠ 0 := by simpa using (ne_of_gt hnpos)
  have hmul : α * (n : ℂ) ≠ 0 := mul_ne_zero hα hn0
  rw [Complex.cpow_def_of_ne_zero hmul, Complex.cpow_def_of_ne_zero hα,
    Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_add, log_mul_natCast_of_re_pos hre hn]
  congr 1
  ring

/-! ## The shift ratio -/

/-- The exponent of the shift ratio along the ray. -/
def rayShiftExponent (α w : ℂ) (n : ℕ) : ℂ :=
  (∫ u in (0 : ℝ)..1, w * Complex.digamma (rayPoint α n + (u : ℂ) * w))
    - w * Complex.log (rayPoint α n)

/-- **The shift ratio is the exponential of the exponent.** -/
theorem gamma_ray_shift_ratio_eq_exp {α w : ℂ} (hre : 0 < α.re) {n : ℕ}
    (hseg : 0 < (rayPoint α n + w).re) :
    Complex.Gamma (rayPoint α n + w)
        / (Complex.Gamma (rayPoint α n) * rayPoint α n ^ w)
      = Complex.exp (rayShiftExponent α w n) := by
  have hz := rayPoint_re_pos hre n
  have hz0 := rayPoint_ne_zero hre n
  have hΓ : Complex.Gamma (rayPoint α n) ≠ 0 := gamma_ne_zero_of_re_pos hz
  have hshift := gamma_shift_exp_integral_complex hz hseg
  have hcpow : rayPoint α n ^ w
      = Complex.exp (w * Complex.log (rayPoint α n)) := by
    rw [Complex.cpow_def_of_ne_zero hz0]
    ring_nf
  rw [hshift, hcpow, rayShiftExponent, Complex.exp_sub]
  have hexpne : Complex.exp (w * Complex.log (rayPoint α n)) ≠ 0 := Complex.exp_ne_zero _
  field_simp

/-- **The exponent of the shift ratio is `O(1/n)`.** -/
theorem norm_rayShiftExponent_le {α w : ℂ} (hre : 0 < α.re) {n : ℕ}
    (hn : 2 * ‖w‖ + 4 ≤ (rayPoint α n).re) :
    ‖rayShiftExponent α w n‖
      ≤ ‖w‖ * (3 / ((rayPoint α n).re - ‖w‖) + 2 * ‖w‖ / (rayPoint α n).re) := by
  have hR : (2 : ℝ) * ‖w‖ + 4 ≤ (rayPoint α n).re := hn
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hzre : 0 < (rayPoint α n).re := by linarith
  have hznorm : (rayPoint α n).re ≤ ‖rayPoint α n‖ := rayPoint_re_le_norm α n
  have hz0 := rayPoint_ne_zero hre n
  -- the pointwise estimate on the segment
  have hpoint : ∀ u ∈ Set.uIoc (0 : ℝ) 1,
      ‖w * Complex.digamma (rayPoint α n + (u : ℂ) * w) - w * Complex.log (rayPoint α n)‖
        ≤ ‖w‖ * (3 / ((rayPoint α n).re - ‖w‖) + 2 * ‖w‖ / (rayPoint α n).re) := by
    intro u hu
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
    have hu0 : (0 : ℝ) ≤ u := le_of_lt hu.1
    have hu1 : u ≤ 1 := hu.2
    set ζ : ℂ := rayPoint α n + (u : ℂ) * w with hζ
    have hnormuw : ‖(u : ℂ) * w‖ ≤ ‖w‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
      nlinarith [norm_nonneg w]
    have hζre : (rayPoint α n).re - ‖w‖ ≤ ζ.re := by
      have hle : |((u : ℂ) * w).re| ≤ ‖(u : ℂ) * w‖ := Complex.abs_re_le_norm _
      have := abs_le.mp (le_trans hle hnormuw)
      rw [hζ]
      simp only [Complex.add_re]
      linarith [this.1]
    have hζrepos : 0 < ζ.re := by linarith
    have hζnorm : (2 : ℝ) ≤ ‖ζ‖ := by
      have := Complex.re_le_norm ζ
      linarith
    -- the digamma defect
    have hdig : ‖Complex.digamma ζ - Complex.log ζ‖ ≤ 3 / ((rayPoint α n).re - ‖w‖) := by
      refine le_trans (norm_digamma_sub_log_le_of_re_pos hζrepos hζnorm) ?_
      have hpos : (0 : ℝ) < (rayPoint α n).re - ‖w‖ := by linarith
      have : (rayPoint α n).re - ‖w‖ ≤ ‖ζ‖ := le_trans hζre (Complex.re_le_norm ζ)
      exact div_le_div_of_nonneg_left (by norm_num) hpos this
    -- the logarithm defect
    have hlog : ‖Complex.log ζ - Complex.log (rayPoint α n)‖
        ≤ 2 * ‖w‖ / (rayPoint α n).re := by
      set ξ : ℂ := (u : ℂ) * w / rayPoint α n with hξ
      have hznormpos : (0 : ℝ) < ‖rayPoint α n‖ := by linarith
      have hξnorm : ‖ξ‖ ≤ ‖w‖ / (rayPoint α n).re := by
        rw [hξ, norm_div, div_le_div_iff₀ hznormpos hzre]
        nlinarith [hnormuw, hznorm, norm_nonneg ((u : ℂ) * w), hw0, hzre]
      have hξhalf : ‖ξ‖ ≤ 1 / 2 := by
        refine le_trans hξnorm ?_
        rw [div_le_div_iff₀ hzre (by norm_num)]
        linarith
      have hξlt : ‖ξ‖ < 1 := by linarith
      have hfac : ζ = rayPoint α n * (1 + ξ) := by
        rw [hζ, hξ]
        field_simp
      have honere : 0 < (1 + ξ).re := by
        have hle : |ξ.re| ≤ ‖ξ‖ := Complex.abs_re_le_norm _
        have := abs_le.mp (le_trans hle hξhalf)
        simp only [Complex.add_re, Complex.one_re]
        linarith [this.1]
      have hone0 : (1 + ξ) ≠ 0 := by
        intro h
        rw [h] at honere
        simp at honere
      have hargz : |Complex.arg (rayPoint α n)| < Real.pi / 2 :=
        Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hzre)
      have hargw : |Complex.arg (1 + ξ)| < Real.pi / 2 :=
        Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl honere)
      have hpi : 0 < Real.pi := Real.pi_pos
      have hsplit : Complex.log ζ = Complex.log (rayPoint α n) + Complex.log (1 + ξ) := by
        rw [hfac]
        refine (Complex.log_mul_eq_add_log_iff hz0 hone0).mpr ?_
        constructor
        · have h1 := (abs_lt.mp hargz).1
          have h2 := (abs_lt.mp hargw).1
          linarith
        · have h1 := (abs_lt.mp hargz).2
          have h2 := (abs_lt.mp hargw).2
          linarith
      rw [hsplit, add_sub_cancel_left]
      refine le_trans (norm_log_one_add_le_two_mul hξhalf) ?_
      have hle2 : 2 * ‖ξ‖ ≤ 2 * (‖w‖ / (rayPoint α n).re) := by linarith
      calc 2 * ‖ξ‖ ≤ 2 * (‖w‖ / (rayPoint α n).re) := hle2
        _ = 2 * ‖w‖ / (rayPoint α n).re := by ring
    have hcomb : ‖Complex.digamma ζ - Complex.log (rayPoint α n)‖
        ≤ 3 / ((rayPoint α n).re - ‖w‖) + 2 * ‖w‖ / (rayPoint α n).re := by
      have hsplit : Complex.digamma ζ - Complex.log (rayPoint α n)
          = (Complex.digamma ζ - Complex.log ζ)
            + (Complex.log ζ - Complex.log (rayPoint α n)) := by ring
      rw [hsplit]
      exact le_trans (norm_add_le _ _) (add_le_add hdig hlog)
    have hmulout : w * Complex.digamma ζ - w * Complex.log (rayPoint α n)
        = w * (Complex.digamma ζ - Complex.log (rayPoint α n)) := by ring
    rw [hmulout, norm_mul]
    exact mul_le_mul_of_nonneg_left hcomb hw0
  -- integrate
  have hcont : ContinuousOn (fun u : ℝ => w * Complex.digamma (rayPoint α n + (u : ℂ) * w))
      (Set.uIcc 0 1) := by
    refine (continuousOn_digamma_segment (rayPoint α n) w).mono ?_
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
    have hu0 : (0 : ℝ) ≤ u := hu.1
    have hu1 : u ≤ 1 := hu.2
    have hnormuw : ‖(u : ℂ) * w‖ ≤ ‖w‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
      nlinarith [norm_nonneg w]
    have hle : |((u : ℂ) * w).re| ≤ ‖(u : ℂ) * w‖ := Complex.abs_re_le_norm _
    have habs := abs_le.mp (le_trans hle hnormuw)
    show 0 < (rayPoint α n + (u : ℂ) * w).re
    simp only [Complex.add_re]
    linarith [habs.1]
  have hint : IntervalIntegrable
      (fun u : ℝ => w * Complex.digamma (rayPoint α n + (u : ℂ) * w))
      MeasureTheory.volume 0 1 := hcont.intervalIntegrable
  have hrewrite : rayShiftExponent α w n
      = ∫ u in (0 : ℝ)..1,
        (w * Complex.digamma (rayPoint α n + (u : ℂ) * w) - w * Complex.log (rayPoint α n)) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
      intervalIntegral.integral_const, rayShiftExponent]
    simp
  rw [hrewrite]
  have := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  simpa using this

/-- **The exponent of the shift ratio vanishes.** -/
theorem tendsto_rayShiftExponent {α w : ℂ} (hre : 0 < α.re) :
    Tendsto (fun n : ℕ => rayShiftExponent α w n) atTop (𝓝 0) := by
  have hRtop := tendsto_rayPoint_re_atTop hre
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hgtop : Tendsto
      (fun n : ℕ => ‖w‖ * (3 / ((rayPoint α n).re - ‖w‖) + 2 * ‖w‖ / (rayPoint α n).re))
      atTop (𝓝 0) := by
    have hb : Tendsto (fun n : ℕ => (rayPoint α n).re - ‖w‖) atTop atTop := by
      simpa [sub_eq_add_neg] using Filter.tendsto_atTop_add_const_right atTop (-‖w‖) hRtop
    have h1 : Tendsto (fun n : ℕ => 3 / ((rayPoint α n).re - ‖w‖)) atTop (𝓝 0) := by
      have := hb.inv_tendsto_atTop.const_mul (3 : ℝ)
      simpa [div_eq_mul_inv] using this
    have h2 : Tendsto (fun n : ℕ => 2 * ‖w‖ / (rayPoint α n).re) atTop (𝓝 0) := by
      have := hRtop.inv_tendsto_atTop.const_mul (2 * ‖w‖)
      simpa [div_eq_mul_inv] using this
    have := (h1.add h2).const_mul ‖w‖
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hgtop
  filter_upwards [hRtop.eventually_ge_atTop (2 * ‖w‖ + 4)] with n hn
  exact norm_rayShiftExponent_le hre hn

/-- **The Gamma shift ratio along a complex ray.** -/
theorem tendsto_gamma_ray_shift_ratio {α w : ℂ} (hre : 0 < α.re) :
    Tendsto (fun n : ℕ => Complex.Gamma (rayPoint α n + w)
        / (Complex.Gamma (rayPoint α n) * rayPoint α n ^ w)) atTop (𝓝 1) := by
  have hexp := (Complex.continuous_exp.tendsto 0).comp (tendsto_rayShiftExponent (α := α) (w := w) hre)
  simp only [Function.comp_def, Complex.exp_zero] at hexp
  refine hexp.congr' ?_
  have hRtop := tendsto_rayPoint_re_atTop hre
  filter_upwards [hRtop.eventually_ge_atTop (‖w‖ + 1)] with n hn
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hseg : 0 < (rayPoint α n + w).re := by
    have hle : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm _
    have := abs_le.mp hle
    simp only [Complex.add_re]
    linarith [this.1, hn]
  exact (gamma_ray_shift_ratio_eq_exp hre hseg).symm

end

end GaloisForLFunctions.HTGeometry
