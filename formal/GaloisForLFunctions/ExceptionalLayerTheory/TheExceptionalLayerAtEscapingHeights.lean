import GaloisForLFunctions.ExceptionalLayerTheory.ThePrimeCurrentAtExponentialScales
import GaloisForLFunctions.HTGeometry.GammaRayShiftAsymptotic
import GaloisForLFunctions.HTGeometry.GammaShiftRatioAsymptotic

/-!
# The exceptional layer at escaping heights

At exponential damping, division by the top real Gaussian mode removes
the growth of the exceptional layer. Its ordinates remain visible in a
finite oscillatory profile. The complete infinite-current error is retained.
-/

open Complex Filter Set Topology intervalIntegral RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

open HTGeometry

private def gammaShiftExponent (z w : ℂ) : ℂ :=
  (∫ u in (0 : ℝ)..1, w * Complex.digamma (z + (u : ℂ) * w)) - w * Complex.log z

private theorem gamma_shift_ratio_eq_exp {z w : ℂ}
    (hz : 0 < z.re) (hzw : 0 < (z + w).re) :
    Complex.Gamma (z + w) / (Complex.Gamma z * z ^ w) =
      Complex.exp (gammaShiftExponent z w) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hΓ := gamma_ne_zero_of_re_pos hz
  rw [gamma_shift_exp_integral_complex hz hzw, Complex.cpow_def_of_ne_zero hz0,
    gammaShiftExponent, Complex.exp_sub]
  rw [mul_comm (Complex.log z) w]
  field_simp

/- The norm, rather than the real part, controls the error. This permits
vertical base points whose real parts remain fixed. -/
private theorem norm_gammaShiftExponent_le {z w : ℂ}
    (hz : 0 < z.re) (hzw : 0 < (z + w).re) (hlarge : 2 * ‖w‖ + 4 ≤ ‖z‖) :
    ‖gammaShiftExponent z w‖ ≤
      ‖w‖ * (3 / (‖z‖ - ‖w‖) + 2 * ‖w‖ / ‖z‖) := by
  have hw0 := norm_nonneg w
  have hnz : 0 < ‖z‖ := by linarith only [hlarge, hw0]
  have hz0 := norm_pos_iff.mp hnz
  have hden : 0 < ‖z‖ - ‖w‖ := by linarith only [hlarge, hw0]
  have hpoint : ∀ u ∈ Set.uIoc (0 : ℝ) 1,
      ‖w * Complex.digamma (z + (u : ℂ) * w) - w * Complex.log z‖ ≤
        ‖w‖ * (3 / (‖z‖ - ‖w‖) + 2 * ‖w‖ / ‖z‖) := by
    intro u hu
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    have hu0 := hu.1.le
    have huw : ‖(u : ℂ) * w‖ ≤ ‖w‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
      exact mul_le_of_le_one_left hw0 hu.2
    have hseg := segment_re_pos hz hzw ⟨hu0, hu.2⟩
    have hnorm : ‖z‖ - ‖w‖ ≤ ‖z + (u : ℂ) * w‖ := by
      have hb := norm_sub_le (z + (u : ℂ) * w) ((u : ℂ) * w)
      rw [add_sub_cancel_right] at hb
      linarith only [hb, huw]
    have hnorm2 : 2 ≤ ‖z + (u : ℂ) * w‖ := by
      linarith only [hnorm, hlarge, hw0]
    have hdig : ‖Complex.digamma (z + (u : ℂ) * w) -
        Complex.log (z + (u : ℂ) * w)‖ ≤ 3 / (‖z‖ - ‖w‖) :=
      (norm_digamma_sub_log_le_of_re_pos hseg hnorm2).trans
        (div_le_div_of_nonneg_left (by norm_num) hden hnorm)
    let ξ : ℂ := (u : ℂ) * w / z
    have hξ : ‖ξ‖ ≤ ‖w‖ / ‖z‖ := by
      dsimp only [ξ]
      rw [norm_div]
      exact div_le_div_of_nonneg_right huw hnz.le
    have hξhalf : ‖ξ‖ ≤ 1 / 2 := by
      refine hξ.trans ?_
      rw [div_le_iff₀ hnz]
      linarith only [hlarge]
    have hfac : z + (u : ℂ) * w = z * (1 + ξ) := by
      dsimp only [ξ]
      field_simp
    have hone : 0 < (1 + ξ).re := by
      have hb := (abs_le.mp ((Complex.abs_re_le_norm ξ).trans hξhalf)).1
      simp only [Complex.add_re, Complex.one_re]
      linarith only [hb]
    have hone0 : 1 + ξ ≠ 0 := by intro h; simp [h] at hone
    have hargz := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
    have hargξ := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hone)
    have hlogsplit : Complex.log (z + (u : ℂ) * w) =
        Complex.log z + Complex.log (1 + ξ) := by
      rw [hfac]
      refine (Complex.log_mul_eq_add_log_iff hz0 hone0).mpr ⟨?_, ?_⟩
      · linarith only [(abs_lt.mp hargz).1, (abs_lt.mp hargξ).1]
      · linarith only [(abs_lt.mp hargz).2, (abs_lt.mp hargξ).2]
    have hlog : ‖Complex.log (z + (u : ℂ) * w) - Complex.log z‖ ≤
        2 * ‖w‖ / ‖z‖ := by
      rw [hlogsplit, add_sub_cancel_left]
      have hb := HTGeometry.norm_log_one_add_le_two_mul hξhalf
      calc
        _ ≤ 2 * ‖ξ‖ := hb
        _ ≤ 2 * (‖w‖ / ‖z‖) := by gcongr
        _ = _ := by ring
    have hsum : ‖Complex.digamma (z + (u : ℂ) * w) - Complex.log z‖ ≤
        3 / (‖z‖ - ‖w‖) + 2 * ‖w‖ / ‖z‖ := by
      calc
        _ = ‖(Complex.digamma (z + (u : ℂ) * w) -
            Complex.log (z + (u : ℂ) * w)) +
            (Complex.log (z + (u : ℂ) * w) - Complex.log z)‖ := by congr 1; ring
        _ ≤ _ := (norm_add_le _ _).trans (add_le_add hdig hlog)
    rw [← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_left hsum hw0
  have hcont := (continuousOn_digamma_segment z w).mono
    (show Set.uIcc (0 : ℝ) 1 ⊆ {u : ℝ | 0 < (z + (u : ℂ) * w).re} from by
      intro u hu
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
      exact segment_re_pos hz hzw hu)
  have heq : gammaShiftExponent z w = ∫ u in (0 : ℝ)..1,
      (w * Complex.digamma (z + (u : ℂ) * w) - w * Complex.log z) := by
    rw [intervalIntegral.integral_sub hcont.intervalIntegrable intervalIntegrable_const,
      intervalIntegral.integral_const, gammaShiftExponent]
    simp
  rw [heq]
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hpoint

private theorem tendsto_gammaShiftExponent_vertical {r : ℝ} (hr : 0 < r) (γ : ℝ) :
    Tendsto (fun t : ℝ => gammaShiftExponent ((r : ℂ) - t * I) ((γ : ℂ) * I))
      atTop (𝓝 0) := by
  let z : ℝ → ℂ := fun t => (r : ℂ) - t * I
  let w : ℂ := (γ : ℂ) * I
  have hz : ∀ t, 0 < (z t).re := by intro t; simpa [z] using hr
  have hzw : ∀ t, 0 < (z t + w).re := by intro t; simpa [z, w] using hr
  have hnorm : Tendsto (fun t => ‖z t‖) atTop atTop := by
    refine tendsto_atTop_mono (fun t => ?_) tendsto_id
    have hb := Complex.abs_im_le_norm (z t)
    simp only [z, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
      add_zero, zero_sub, abs_neg] at hb
    exact (le_abs_self t).trans hb
  have hden := Filter.tendsto_atTop_add_const_right atTop (-‖w‖) hnorm
  have hbound : Tendsto (fun t => ‖w‖ *
      (3 / (‖z t‖ - ‖w‖) + 2 * ‖w‖ / ‖z t‖)) atTop (𝓝 0) := by
    have h₁ := hden.inv_tendsto_atTop.const_mul (3 : ℝ)
    have h₂ := hnorm.inv_tendsto_atTop.const_mul (2 * ‖w‖)
    simpa [sub_eq_add_neg, div_eq_mul_inv] using
      (h₁.add h₂).const_mul ‖w‖
  have hexponent : Tendsto (fun t => gammaShiftExponent (z t) w) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hbound
    filter_upwards [hnorm.eventually_ge_atTop (2 * ‖w‖ + 4)] with t ht
    exact norm_gammaShiftExponent_le (hz t) (hzw t) ht
  exact hexponent

/-- A fixed imaginary shift of Gamma on a descending vertical line has
 the principal complex power as its asymptotic ratio. -/
theorem tendsto_gamma_imaginary_shift_ratio {r : ℝ} (hr : 0 < r) (γ : ℝ) :
    Tendsto (fun t : ℝ => Complex.Gamma ((r : ℂ) - t * I + γ * I) /
      (Complex.Gamma ((r : ℂ) - t * I) * ((r : ℂ) - t * I) ^ ((γ : ℂ) * I)))
      atTop (𝓝 1) := by
  have he := (Complex.continuous_exp.tendsto 0).comp
    (tendsto_gammaShiftExponent_vertical hr γ)
  simp only [Function.comp_def, Complex.exp_zero] at he
  refine he.congr fun t => ?_
  exact (gamma_shift_ratio_eq_exp (by simpa using hr) (by simpa using hr)).symm

private theorem negative_vertical_log {r : ℝ} (hr : 0 < r) :
    Tendsto (fun t : ℝ => Complex.log ((r : ℂ) - t * I) -
      ((Real.log t : ℂ) - (Real.pi / 2 : ℂ) * I)) atTop (𝓝 0) := by
  have h := (Complex.continuous_conj.tendsto 0).comp (tendsto_log_vertical_sub_vertLog r)
  simp only [Function.comp_def, map_zero] at h
  refine h.congr fun t => ?_
  have hz : 0 < ((r : ℂ) + t * I).re := by simpa using hr
  have harg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  have hne : ((r : ℂ) + t * I).arg ≠ Real.pi := by
    have hu := (abs_lt.mp harg).2
    linarith only [hu, Real.pi_pos]
  have hlog := Complex.log_conj ((r : ℂ) + t * I) hne
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
    mul_neg, ← sub_eq_add_neg] at hlog
  rw [map_sub, ← hlog]
  simp [vertLog, sub_eq_add_neg, map_ofNat]

/-- The ordinate wave has phase `γ(at+log(t/2))/2` and amplitude `exp(πγ/4)`. -/
def exceptionalOrdinateWave (γ a t : ℝ) : ℂ :=
  Complex.exp (((γ / 2 : ℝ) : ℂ) * I *
    (((a * t + Real.log (t / 2) : ℝ) : ℂ) - (Real.pi / 2 : ℂ) * I))

theorem norm_exceptionalOrdinateWave (γ a t : ℝ) :
    ‖exceptionalOrdinateWave γ a t‖ = Real.exp (Real.pi * γ / 4) := by
  rw [exceptionalOrdinateWave, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.I_re, Complex.I_im]
  ring

private theorem gaussianKernel_ratio_eq_shift_exp {z w : ℂ}
    (hz : 0 < z.re) (hzw : 0 < (z + w).re) (a t : ℝ) :
    gaussianMBKernel (Real.exp (-a * t)) (2 * (z + w)) /
      gaussianMBKernel (Real.exp (-a * t)) (2 * z) =
      Complex.exp (gammaShiftExponent z w + w * Complex.log z + ((a * t : ℝ) : ℂ) * w) := by
  have hy0 : (Real.exp (-a * t) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have hΓ := gamma_ne_zero_of_re_pos hz
  have h₂ : (2 * z : ℂ) / 2 = z := by ring
  have h₁ : (2 * (z + w) : ℂ) / 2 = z + w := by ring
  rw [gaussianMBKernel, gaussianMBKernel, h₁, h₂,
    Complex.cpow_def_of_ne_zero hy0, Complex.cpow_def_of_ne_zero hy0,
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp,
    gamma_shift_exp_integral_complex hz hzw]
  let Q : ℂ := ∫ u in (0 : ℝ)..1, w * Complex.digamma (z + (u : ℂ) * w)
  change ((1 / 2 : ℂ) * (Complex.Gamma z * Complex.exp Q) *
      Complex.exp (((-a * t : ℝ) : ℂ) * -(z + w))) /
    ((1 / 2 : ℂ) * Complex.Gamma z * Complex.exp (((-a * t : ℝ) : ℂ) * -z)) = _
  have hex : gammaShiftExponent z w + w * Complex.log z + ((a * t : ℝ) : ℂ) * w =
      Q + ((a * t : ℝ) : ℂ) * w := by dsimp only [gammaShiftExponent, Q]; ring
  rw [hex]
  apply (div_eq_iff (mul_ne_zero
    (mul_ne_zero (by norm_num : (1 / 2 : ℂ) ≠ 0) hΓ) (Complex.exp_ne_zero _))).mpr
  have he : Q + ((-a * t : ℝ) : ℂ) * -(z + w) =
      (Q + ((a * t : ℝ) : ℂ) * w) + ((-a * t : ℝ) : ℂ) * -z := by
    push_cast
    ring
  calc
    _ = ((1 / 2 : ℂ) * Complex.Gamma z) *
        Complex.exp (Q + ((-a * t : ℝ) : ℂ) * -(z + w)) := by rw [Complex.exp_add]; ring
    _ = _ := by rw [he, Complex.exp_add]; ring

private theorem tendsto_ordinateExponent {r : ℝ} (hr : 0 < r) (γ : ℝ) :
    Tendsto (fun t : ℝ =>
      gammaShiftExponent ((r : ℂ) - ((t / 2 : ℝ) : ℂ) * I) (((γ / 2 : ℝ) : ℂ) * I) +
      (((γ / 2 : ℝ) : ℂ) * I) *
        (Complex.log ((r : ℂ) - ((t / 2 : ℝ) : ℂ) * I) -
          ((Real.log (t / 2) : ℂ) - (Real.pi / 2 : ℂ) * I))) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => t / 2) atTop atTop := by
    simpa only [div_eq_mul_inv, id_eq] using
      Filter.Tendsto.atTop_mul_const (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹) tendsto_id
  have h₁ := (tendsto_gammaShiftExponent_vertical hr (γ / 2)).comp ht
  have h₂ := ((negative_vertical_log hr).comp ht).const_mul (((γ / 2 : ℝ) : ℂ) * I)
  simpa only [Function.comp_def, mul_zero, add_zero] using h₁.add h₂

/-- A top-layer mode, divided by the real reference mode, recovers its
ordinate wave at escaping heights. -/
theorem tendsto_gaussianMode_ratio_sub_ordinateWave {β σ : ℝ} (hσβ : σ < β)
    (γ a : ℝ) :
    Tendsto (fun t : ℝ =>
      gaussianMBKernel (Real.exp (-a * t))
        (((β : ℂ) + γ * I) - ((σ : ℂ) + t * I)) /
      gaussianMBKernel (Real.exp (-a * t)) ((β : ℂ) - ((σ : ℂ) + t * I)) -
      exceptionalOrdinateWave γ a t) atTop (𝓝 0) := by
  let r : ℝ := (β - σ) / 2
  have hr : 0 < r := by dsimp only [r]; positivity
  let z : ℝ → ℂ := fun t => (r : ℂ) - ((t / 2 : ℝ) : ℂ) * I
  let w : ℂ := ((γ / 2 : ℝ) : ℂ) * I
  let E : ℝ → ℂ := fun t => gammaShiftExponent (z t) w +
    w * (Complex.log (z t) - ((Real.log (t / 2) : ℂ) - (Real.pi / 2 : ℂ) * I))
  have hE : Tendsto E atTop (𝓝 0) := tendsto_ordinateExponent hr γ
  have he : Tendsto (fun t => Complex.exp (E t) - 1) atTop (𝓝 0) := by
    have h := ((Complex.continuous_exp.tendsto 0).comp hE).sub_const 1
    simpa only [Function.comp_def, Complex.exp_zero, sub_self] using h
  have hidentity : ∀ t : ℝ,
      gaussianMBKernel (Real.exp (-a * t))
        (((β : ℂ) + γ * I) - ((σ : ℂ) + t * I)) /
      gaussianMBKernel (Real.exp (-a * t)) ((β : ℂ) - ((σ : ℂ) + t * I)) =
      exceptionalOrdinateWave γ a t * Complex.exp (E t) := by
    intro t
    have hz : 0 < (z t).re := by simpa [z] using hr
    have hzw : 0 < (z t + w).re := by simpa [z, w] using hr
    have hnum : ((β : ℂ) + γ * I) - ((σ : ℂ) + t * I) = 2 * (z t + w) := by
      dsimp only [z, w, r]
      push_cast
      ring
    have hden : (β : ℂ) - ((σ : ℂ) + t * I) = 2 * z t := by
      dsimp only [z, r]
      push_cast
      ring
    rw [hnum, hden, gaussianKernel_ratio_eq_shift_exp hz hzw,
      exceptionalOrdinateWave, ← Complex.exp_add]
    congr 1
    dsimp only [E, w]
    push_cast
    ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hb := he.norm.const_mul (Real.exp (Real.pi * γ / 4))
  simp only [norm_zero, mul_zero] at hb
  refine hb.congr fun t => ?_
  rw [hidentity, ← mul_sub_one, norm_mul, norm_exceptionalOrdinateWave]

/-- Every strictly lower real part disappears relative to the top Gaussian
mode at any positive exponential damping speed. -/
theorem tendsto_gaussianMode_ratio_zero_of_re_lt {ρ : ℂ} {β σ a : ℝ}
    (hρ : ρ.re < β) (ha : 0 < a) :
    Tendsto (fun t : ℝ =>
      gaussianMBKernel (Real.exp (-a * t)) (ρ - ((σ : ℂ) + t * I)) /
      gaussianMBKernel (Real.exp (-a * t)) ((β : ℂ) - ((σ : ℂ) + t * I)))
      atTop (𝓝 0) := by
  obtain ⟨C, D, N, M, hC, hD, hb⟩ := exists_gaussianMode_exponential_bounds ρ σ
  obtain ⟨C₁, D₁, N₁, M₁, hC₁, hD₁, hb₁⟩ :=
    exists_gaussianMode_exponential_bounds (β : ℂ) σ
  have hδ : 0 < a * (β - ρ.re) / 2 := by positivity
  apply tendsto_zero_of_eventually_norm_le_polyExp
    (C := C * D₁) (N := N + M₁) hδ
  filter_upwards [eventually_ge_atTop (max (|ρ.im| + 2) 2)] with t ht
  have ht0 : 0 ≤ t := (by norm_num : (0 : ℝ) ≤ 2).trans
    ((le_max_right _ _).trans ht)
  have h₁ := (hb t ((le_max_left _ _).trans ht) a).1
  have h₂ := (hb₁ t (by simpa using (le_max_right (|ρ.im| + 2) 2).trans ht) a).2
  rw [div_eq_mul_inv, norm_mul]
  calc
    _ ≤ (C * t ^ N * Real.exp (gaussianObservationRate ρ σ a * t)) *
        (D₁ * t ^ M₁ * Real.exp (-(gaussianObservationRate (β : ℂ) σ a * t))) :=
      mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)
    _ = (C * D₁) * t ^ (N + M₁) * Real.exp (-(a * (β - ρ.re) / 2 * t)) := by
      rw [pow_add]
      have hex : -(a * (β - ρ.re) / 2 * t) =
          gaussianObservationRate ρ σ a * t - gaussianObservationRate (β : ℂ) σ a * t := by
        simp only [gaussianObservationRate, Complex.ofReal_re]
        ring
      rw [hex, sub_eq_add_neg, Real.exp_add]
      ring

/-- Failure of AAL makes the complete pole-subtracted prime current recover
an actual nonempty top-layer profile above its exponential observation threshold.
Every omitted zero is retained in the vanishing infinite-current error. -/
theorem not_asymptoticAbscissaLaw_has_escaping_layer_profile :
    ¬ AsymptoticAbscissaLaw →
      ∃ (F : Finset XiZeroCopy) (θ σ β : ℝ),
        1 / 2 ≤ θ ∧ θ < σ ∧ σ < β ∧ β < 1 ∧
        (∃ q ∈ F, (xiZero q).re = β) ∧
        (∀ q ∈ F, (xiZero q).re ≤ β) ∧
        (∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ) ∧
        ∀ a : ℝ, 0 < a → Real.pi / 2 < a * (β - σ) →
          Tendsto (fun t : ℝ =>
            (gaussianDampedPrimeSum ((σ : ℂ) + t * I) (Real.exp (-a * t)) +
                (Real.exp (-(Real.exp (-a * t))) : ℂ) *
                  logDeriv riemannZeta ((σ : ℂ) + t * I) -
                gaussianMBKernel (Real.exp (-a * t)) (1 - ((σ : ℂ) + t * I))) /
              gaussianMBKernel (Real.exp (-a * t)) ((β : ℂ) - ((σ : ℂ) + t * I)) +
              ∑ q ∈ F.filter (fun q => (xiZero q).re = β),
                exceptionalOrdinateWave (xiZero q).im a t) atTop (𝓝 0) := by
  classical
  intro hnot
  obtain ⟨F, θ, σ, hθ, hgap, hσ1, ⟨q₁, hq₁F, hq₁⟩, hrest, hfull⟩ :=
    not_asymptoticAbscissaLaw_has_full_exponential_expansion hnot
  obtain ⟨q₀, hq₀F, hmax⟩ := F.exists_max_image (fun q => (xiZero q).re) ⟨q₁, hq₁F⟩
  let β : ℝ := (xiZero q₀).re
  have hσβ : σ < β := hq₁.trans_le (hmax q₁ hq₁F)
  have hβ1 : β < 1 := xiZeroCopy_re_lt_one q₀
  refine ⟨F, θ, σ, β, hθ, hgap, hσβ, hβ1, ⟨q₀, hq₀F, rfl⟩, hmax, hrest, ?_⟩
  intro a ha hsuper
  have hr : 0 < gaussianObservationRate (β : ℂ) σ a := by
    simp only [gaussianObservationRate, Complex.ofReal_re]
    linarith only [hsuper]
  have hinv := tendsto_inv_gaussianMode_zero_of_positive_rate (β : ℂ) σ a hr
  have herror := ((hfull a ha).tendsto_at ⟨le_rfl, hσ1.le⟩).mul hinv
  simp only [mul_zero] at herror
  have hmode : ∀ q ∈ F, Tendsto (fun t : ℝ =>
      gaussianMBKernel (Real.exp (-a * t)) (xiZero q - ((σ : ℂ) + t * I)) /
        gaussianMBKernel (Real.exp (-a * t)) ((β : ℂ) - ((σ : ℂ) + t * I)) -
      if (xiZero q).re = β then exceptionalOrdinateWave (xiZero q).im a t else 0)
        atTop (𝓝 0) := by
    intro q hq
    by_cases heq : (xiZero q).re = β
    · have hρ : xiZero q = (β : ℂ) + (xiZero q).im * I := by
        apply Complex.ext
        · simpa using heq
        · simp
      have hh := tendsto_gaussianMode_ratio_sub_ordinateWave hσβ (xiZero q).im a
      simpa only [if_pos heq, ← hρ] using hh
    · have hlt : (xiZero q).re < β := lt_of_le_of_ne (hmax q hq) heq
      simpa only [if_neg heq, sub_zero] using
        tendsto_gaussianMode_ratio_zero_of_re_lt (σ := σ) hlt ha
  have hsum := tendsto_finsetSum F hmode
  simp only [Finset.sum_const_zero] at hsum
  have hh := herror.sub hsum
  simp only [sub_zero] at hh
  refine hh.congr fun t => ?_
  dsimp only [exceptionalGaussianExpansionError]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_filter]
  simp only [div_eq_mul_inv]
  ring

#print axioms tendsto_gaussianMode_ratio_sub_ordinateWave
#print axioms not_asymptoticAbscissaLaw_has_escaping_layer_profile

#print axioms tendsto_gaussianMode_ratio_zero_of_re_lt

#print axioms tendsto_gamma_imaginary_shift_ratio

end GaloisForLFunctions.ExceptionalLayerTheory
