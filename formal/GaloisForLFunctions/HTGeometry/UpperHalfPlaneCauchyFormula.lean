import GaloisForLFunctions.HTGeometry.UpperHalfPlaneCauchyVanishing
import GaloisForLFunctions.HTGeometry.DslopeLocalFactor

noncomputable section

/-!
# The Cauchy integral formula on the closed upper half-plane

A function holomorphic on the closed upper half-plane whose modulus decays like `1/|z|` there is
recovered from its boundary values by the Cauchy integral.  The companion vanishing statement — the
same integral against a point *below* the axis is zero — is the contour theorem of
`UpperHalfPlaneCauchyVanishing`; here the pole sits inside the contour.

The kernel is regularised rather than indented.  Subtracting the mirrored Cauchy kernel scaled to
the same residue produces a function with a removable singularity at `w`, which is exactly a divided
slope, so it is holomorphic on the whole closed half-plane and decays quadratically; its contour
integral vanishes.  What is subtracted integrates to the Poisson normalisation `π / Im w`, and the
residue factor `w - conj w = 2i Im w` turns that into `2πi`.
-/

open MeasureTheory Set Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

theorem differentiableAt_dslope_of_ne {f : ℂ → ℂ} {a z : ℂ} (hz : z ≠ a)
    (hf : DifferentiableAt ℂ f z) : DifferentiableAt ℂ (dslope f a) z := by
  have hne : a - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hne' : z - a ≠ 0 := sub_ne_zero.mpr hz
  have hev : dslope f a =ᶠ[𝓝 z] fun ζ : ℂ => (f ζ - f a) / (ζ - a) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with ζ hζ
    rw [dslope_of_ne _ hζ, slope_def_field]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  exact (hf.sub_const _).div (differentiableAt_id.sub_const _) hne'

/-- **The Poisson normalisation** `∫ dx/((x-a)² + b²) = π/b`. -/
theorem integral_inv_sub_sq_add_sq {a b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, ((x - a) ^ (2 : ℕ) + b ^ (2 : ℕ))⁻¹) = Real.pi / b := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hfun : ∀ x : ℝ, ((x - a) ^ (2 : ℕ) + b ^ (2 : ℕ))⁻¹
      = (b ^ (2 : ℕ))⁻¹ * (1 + ((x - a) / b) ^ (2 : ℕ))⁻¹ := by
    intro x
    rw [← mul_inv]
    congr 1
    field_simp
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hfun),
    MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub_right_eq_self (fun x : ℝ => (1 + (x / b) ^ (2 : ℕ))⁻¹) a,
    MeasureTheory.Measure.integral_comp_div (fun u : ℝ => (1 + u ^ (2 : ℕ))⁻¹) b,
    integral_univ_inv_one_add_sq, smul_eq_mul, abs_of_pos hb]
  field_simp

theorem integrable_inv_sub_sq_add_sq {a b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => ((x - a) ^ (2 : ℕ) + b ^ (2 : ℕ))⁻¹) volume := by
  have hbase : Integrable (fun x : ℝ => ((b ^ (2 : ℕ))⁻¹ * (1 + ((x - a) / b) ^ (2 : ℕ))⁻¹)) volume :=
    ((integrable_inv_one_add_sq.comp_div (ne_of_gt hb)).comp_sub_right a).const_mul _
  refine hbase.congr ?_
  filter_upwards with x
  rw [← mul_inv]
  congr 1
  field_simp
  ring

/-- The product of the two conjugate Cauchy factors is the real Poisson denominator. -/
theorem cauchyPair_eq_ofReal (w : ℂ) (x : ℝ) :
    (((x : ℂ) - w) * ((x : ℂ) - (starRingEnd ℂ) w))
      = ((((x - w.re) ^ (2 : ℕ) + w.im ^ (2 : ℕ) : ℝ)) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.ofReal_re]
    simp [Complex.mul_re, Complex.sub_re, Complex.sub_im]
    ring
  · simp only [Complex.ofReal_im]
    simp [Complex.mul_im, Complex.sub_re, Complex.sub_im]
    ring

theorem integrable_cauchyPair {w : ℂ} (hw : 0 < w.im) :
    Integrable (fun x : ℝ => (((x : ℂ) - w) * ((x : ℂ) - (starRingEnd ℂ) w))⁻¹) volume := by
  have hb := integrable_inv_sub_sq_add_sq (a := w.re) hw
  have hcoe : Integrable
      (fun x : ℝ => (((((x - w.re) ^ (2 : ℕ) + w.im ^ (2 : ℕ) : ℝ)) : ℂ))⁻¹) volume := by
    have hc : Integrable (fun x : ℝ => (((((x - w.re) ^ (2 : ℕ) + w.im ^ (2 : ℕ))⁻¹ : ℝ)) : ℂ)) volume :=
      MeasureTheory.Integrable.ofReal hb
    refine hc.congr ?_
    filter_upwards with x
    rw [Complex.ofReal_inv]
  refine hcoe.congr ?_
  filter_upwards with x
  rw [cauchyPair_eq_ofReal]

theorem integral_cauchyPair {w : ℂ} (hw : 0 < w.im) :
    (∫ x : ℝ, (((x : ℂ) - w) * ((x : ℂ) - (starRingEnd ℂ) w))⁻¹)
      = ((Real.pi / w.im : ℝ) : ℂ) := by
  have hfun : ∀ x : ℝ, (((x : ℂ) - w) * ((x : ℂ) - (starRingEnd ℂ) w))⁻¹
      = ((((x - w.re) ^ (2 : ℕ) + w.im ^ (2 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) := by
    intro x
    rw [cauchyPair_eq_ofReal, ← Complex.ofReal_inv]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hfun)]
  have h := integral_ofReal (𝕜 := ℂ) (μ := (volume : Measure ℝ))
    (f := fun x : ℝ => ((x - w.re) ^ (2 : ℕ) + w.im ^ (2 : ℕ))⁻¹)
  exact h.trans (by rw [integral_inv_sub_sq_add_sq hw]; rfl)

/-- **The Cauchy integral formula for the closed upper half-plane.**  A function holomorphic on the
closed upper half-plane and decaying like `1/|z|` there reproduces itself from its boundary values.

The singular kernel is regularised by subtracting the mirrored Cauchy kernel with the same residue:
the difference is a divided slope, hence holomorphic across the pole, and decays quadratically, so
the contour theorem applies to it.  The subtracted term is the Poisson normalisation `π / Im w`. -/
theorem integral_div_sub_eq_of_upperHalfPlane_farDecay {u : ℂ → ℂ} {M R : ℝ}
    (hdiff : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ u z) (hR : 0 < R)
    (hfar : ∀ z : ℂ, 0 ≤ z.im → R ≤ ‖z‖ → ‖u z‖ ≤ M / ‖z‖)
    {w : ℂ} (hw : 0 < w.im) :
    (∫ x : ℝ, u ((x : ℝ) : ℂ) / (((x : ℝ) : ℂ) - w)) = 2 * (Real.pi : ℂ) * I * u w := by
  have hwc : ((starRingEnd ℂ) w).im = -w.im := by simp
  have hwn : ‖(starRingEnd ℂ) w‖ = ‖w‖ := by simp
  set c : ℂ := u w * (w - (starRingEnd ℂ) w) with hc
  set g : ℂ → ℂ := fun z => u z - c / (z - (starRingEnd ℂ) w) with hgdef
  have hden : ∀ z : ℂ, 0 ≤ z.im → z - (starRingEnd ℂ) w ≠ 0 := by
    intro z hz hzero
    have hzw : z = (starRingEnd ℂ) w := sub_eq_zero.mp hzero
    rw [hzw, hwc] at hz
    linarith
  have hgw : g w = 0 := by
    show u w - c / (w - (starRingEnd ℂ) w) = 0
    rw [hc, mul_div_assoc, div_self (hden w hw.le), mul_one, sub_self]
  have hgdiff : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ g z := by
    intro z hz
    exact (hdiff z hz).sub ((differentiableAt_const _).div
      (differentiableAt_id.sub_const _) (hden z hz))
  have hnearw : ∀ᶠ ζ in 𝓝 w, DifferentiableAt ℂ g ζ := by
    filter_upwards [Metric.ball_mem_nhds w hw] with ζ hζ
    refine hgdiff ζ ?_
    have h2 : ‖ζ - w‖ < w.im := by
      rw [Metric.mem_ball, Complex.dist_eq] at hζ
      exact hζ
    have h1 : |(ζ - w).im| ≤ ‖ζ - w‖ := Complex.abs_im_le_norm (ζ - w)
    have h3 : |ζ.im - w.im| < w.im := by
      have : (ζ - w).im = ζ.im - w.im := by simp
      rw [this] at h1
      linarith
    have h4 := abs_lt.mp h3
    linarith [h4.1]
  have hdsdiff : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ (dslope g w) z := by
    intro z hz
    rcases eq_or_ne z w with rfl | hne
    · exact differentiableAt_dslope_of_eventually_differentiableAt hnearw
    · exact differentiableAt_dslope_of_ne hne (hgdiff z hz)
  set R' : ℝ := 2 * (R + ‖w‖) + 1 with hR'def
  have hwnn : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hR'0 : 0 < R' := by rw [hR'def]; linarith
  have hfar' : ∀ z : ℂ, 0 ≤ z.im → R' ≤ ‖z‖ →
      ‖dslope g w z‖ ≤ (2 * M + 4 * ‖c‖) / ‖z‖ ^ (2 : ℕ) := by
    intro z hz hzR
    have hzn : 0 < ‖z‖ := lt_of_lt_of_le hR'0 hzR
    have hhalf : ‖w‖ ≤ ‖z‖ / 2 := by rw [hR'def] at hzR; linarith
    have hzw : ‖z‖ / 2 ≤ ‖z - w‖ := by
      have h := norm_sub_norm_le z w
      linarith
    have hzwc : ‖z‖ / 2 ≤ ‖z - (starRingEnd ℂ) w‖ := by
      have h := norm_sub_norm_le z ((starRingEnd ℂ) w)
      rw [hwn] at h
      linarith
    have hzh : 0 < ‖z‖ / 2 := by linarith
    have hne : z ≠ w := by
      intro h
      rw [h] at hzn hzw
      rw [sub_self, norm_zero] at hzw
      linarith
    have hu := hfar z hz (by rw [hR'def] at hzR; linarith)
    have hg : ‖g z‖ ≤ (M + 2 * ‖c‖) / ‖z‖ := by
      have h1 : ‖c / (z - (starRingEnd ℂ) w)‖ ≤ 2 * ‖c‖ / ‖z‖ := by
        rw [norm_div]
        rw [div_le_div_iff₀ (lt_of_lt_of_le hzh hzwc) hzn]
        nlinarith [norm_nonneg c]
      calc ‖g z‖ ≤ ‖u z‖ + ‖c / (z - (starRingEnd ℂ) w)‖ := norm_sub_le _ _
        _ ≤ M / ‖z‖ + 2 * ‖c‖ / ‖z‖ := add_le_add hu h1
        _ = (M + 2 * ‖c‖) / ‖z‖ := by ring
    rw [dslope_of_ne _ hne, slope_def_field, hgw, sub_zero, norm_div]
    rw [div_le_div_iff₀ (lt_of_lt_of_le hzh hzw) (by positivity)]
    have hM : 0 ≤ M := by
      have h := mul_le_mul_of_nonneg_right hu (le_of_lt hzn)
      rw [div_mul_cancel₀ _ (ne_of_gt hzn)] at h
      nlinarith [norm_nonneg (u z)]
    have hgz : ‖g z‖ * ‖z‖ ≤ M + 2 * ‖c‖ := by
      have := mul_le_mul_of_nonneg_right hg (le_of_lt hzn)
      rwa [div_mul_cancel₀ _ (ne_of_gt hzn)] at this
    have hstep := mul_le_mul_of_nonneg_right hgz (le_of_lt hzn)
    have hcn : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
    nlinarith [norm_nonneg (g z)]
  have hzero := integral_eq_zero_of_upperHalfPlane_farDecay hdsdiff hR'0 hfar'
  have hintds := integrable_ofReal_of_farDecay hdsdiff hR'0 hfar'
  have hxne : ∀ x : ℝ, ((x : ℝ) : ℂ) ≠ w := by
    intro x h
    rw [← h] at hw
    simp at hw
  have hpt : ∀ x : ℝ, u ((x : ℝ) : ℂ) / (((x : ℝ) : ℂ) - w)
      = dslope g w ((x : ℝ) : ℂ)
        + c * ((((x : ℝ) : ℂ) - w) * (((x : ℝ) : ℂ) - (starRingEnd ℂ) w))⁻¹ := by
    intro x
    have h1 : ((x : ℝ) : ℂ) - w ≠ 0 := sub_ne_zero.mpr (hxne x)
    have h2 : ((x : ℝ) : ℂ) - (starRingEnd ℂ) w ≠ 0 := hden ((x : ℝ) : ℂ) (by simp)
    rw [dslope_of_ne _ (hxne x), slope_def_field, hgw, sub_zero]
    show u ((x : ℝ) : ℂ) / (((x : ℝ) : ℂ) - w)
      = (u ((x : ℝ) : ℂ) - c / (((x : ℝ) : ℂ) - (starRingEnd ℂ) w)) / (((x : ℝ) : ℂ) - w)
        + c * ((((x : ℝ) : ℂ) - w) * (((x : ℝ) : ℂ) - (starRingEnd ℂ) w))⁻¹
    field_simp
    ring
  have hint2 : Integrable (fun x : ℝ =>
      c * ((((x : ℝ) : ℂ) - w) * (((x : ℝ) : ℂ) - (starRingEnd ℂ) w))⁻¹) volume :=
    (integrable_cauchyPair hw).const_mul c
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_add hintds hint2, hzero, zero_add,
    MeasureTheory.integral_const_mul, integral_cauchyPair hw, hc]
  have hsub : w - (starRingEnd ℂ) w = 2 * I * ((w.im : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im]
    · simp [Complex.mul_re, Complex.mul_im]
      ring
  have him : ((w.im : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt hw
  rw [hsub, Complex.ofReal_div]
  field_simp


end GaloisForLFunctions.HTGeometry
