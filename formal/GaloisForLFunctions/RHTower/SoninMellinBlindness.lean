import GaloisForLFunctions.RHTower.SoninMellinWeight
import GaloisForLFunctions.RHTower.SoninAnnulusPacketAsymptotics

/-!
# Fixed Mellin conormals do not see the wavepacket

The Mellin transform of the wavepacket at a fixed exponent is an oscillatory integral against a
fixed smooth compactly supported weight, corrected by a multiple of a constant.  Both pieces decay
faster than every power of the carrier, so no fixed Mellin evaluation detects the packet at any
finite order in the frequency.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter
open scoped Topology FourierTransform ContDiff

/-- The Mellin transform of the wavepacket at exponent `s`, written on the positive axis. -/
def soninPacketMellin (b c : ℝ) (hbc : b < c) (s : ℂ) (κ : ℝ) : ℂ :=
  ∫ x : ℝ, soninMellinWeight b c hbc s x *
    ((Real.cos (κ * x) : ℂ) - (soninPacketMean b c hbc κ : ℂ))

theorem integrable_soninMellinWeight_mul (b c : ℝ) (hb : 0 < b) (hbc : b < c) (s : ℂ)
    {f : ℝ → ℂ} (hf : Continuous f) :
    Integrable (fun x : ℝ => soninMellinWeight b c hbc s x * f x) volume := by
  refine Continuous.integrable_of_hasCompactSupport
    (((contDiff_soninMellinWeight b c hb hbc s).continuous).mul hf) ?_
  exact (hasCompactSupport_soninMellinWeight b c hbc s).mul_right

theorem integrable_mul_soninMellinWeight (b c : ℝ) (hb : 0 < b) (hbc : b < c) (s : ℂ)
    {f : ℝ → ℂ} (hf : Continuous f) :
    Integrable (fun x : ℝ => f x * soninMellinWeight b c hbc s x) volume := by
  refine Continuous.integrable_of_hasCompactSupport
    (hf.mul ((contDiff_soninMellinWeight b c hb hbc s).continuous)) ?_
  exact (hasCompactSupport_soninMellinWeight b c hbc s).mul_left

/-- The Mellin transform splits into an oscillatory integral and a constant multiple. -/
theorem soninPacketMellin_eq (b c : ℝ) (hb : 0 < b) (hbc : b < c) (s : ℂ) (κ : ℝ) :
    soninPacketMellin b c hbc s κ =
      (∫ x : ℝ, soninMellinWeight b c hbc s x * (Real.cos (κ * x) : ℂ)) -
        (soninPacketMean b c hbc κ : ℂ) * ∫ x : ℝ, soninMellinWeight b c hbc s x := by
  have hI1 : Integrable (fun x : ℝ =>
      soninMellinWeight b c hbc s x * ((Real.cos (κ * x) : ℝ) : ℂ)) volume :=
    integrable_soninMellinWeight_mul b c hb hbc s
      (f := fun x : ℝ => ((Real.cos (κ * x) : ℝ) : ℂ)) (by fun_prop)
  have hW : Integrable (soninMellinWeight b c hbc s) volume := by
    refine Continuous.integrable_of_hasCompactSupport
      ((contDiff_soninMellinWeight b c hb hbc s).continuous) ?_
    exact hasCompactSupport_soninMellinWeight b c hbc s
  have hI2 : Integrable (fun x : ℝ =>
      (soninPacketMean b c hbc κ : ℂ) * soninMellinWeight b c hbc s x) volume :=
    hW.const_mul _
  unfold soninPacketMellin
  rw [show (∫ x : ℝ, soninMellinWeight b c hbc s x *
      ((Real.cos (κ * x) : ℂ) - (soninPacketMean b c hbc κ : ℂ))) =
      ∫ x : ℝ, (soninMellinWeight b c hbc s x * ((Real.cos (κ * x) : ℝ) : ℂ) -
        (soninPacketMean b c hbc κ : ℂ) * soninMellinWeight b c hbc s x) from
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring),
    integral_sub hI1 hI2, integral_const_mul]

/-- The cosine-modulated integral of the weight is the average of two transform values. -/
theorem integral_soninMellinWeight_mul_cos_eq
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (s : ℂ) (w : ℝ) :
    (∫ x : ℝ, soninMellinWeight b c hbc s x * (Real.cos (2 * Real.pi * w * x) : ℂ)) =
      (2 : ℂ)⁻¹ * 𝓕 (soninMellinWeight b c hbc s) w +
        (2 : ℂ)⁻¹ * 𝓕 (soninMellinWeight b c hbc s) (-w) := by
  have hE1 : Integrable (fun x : ℝ =>
      (2 : ℂ)⁻¹ * (Complex.exp ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) *
        soninMellinWeight b c hbc s x)) volume :=
    (integrable_mul_soninMellinWeight b c hb hbc s
      (f := fun x : ℝ => Complex.exp ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I))
      (by fun_prop)).const_mul _
  have hE2 : Integrable (fun x : ℝ =>
      (2 : ℂ)⁻¹ * (Complex.exp ((↑(-2 * Real.pi * x * -w) : ℂ) * Complex.I) *
        soninMellinWeight b c hbc s x)) volume :=
    (integrable_mul_soninMellinWeight b c hb hbc s
      (f := fun x : ℝ => Complex.exp ((↑(-2 * Real.pi * x * -w) : ℂ) * Complex.I))
      (by fun_prop)).const_mul _
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add hE1 hE2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have key : ∀ z : ℂ, (2 : ℂ)⁻¹ * Complex.exp (z * Complex.I) +
      (2 : ℂ)⁻¹ * Complex.exp (-z * Complex.I) = Complex.cos z := by
    intro z
    rw [Complex.cos]
    ring
  have h1 : ((-2 * Real.pi * x * -w : ℝ) : ℂ) = ((2 * Real.pi * w * x : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : ((-2 * Real.pi * x * w : ℝ) : ℂ) = -((2 * Real.pi * w * x : ℝ) : ℂ) := by
    push_cast; ring
  have hcos : ((Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ) =
      (2 : ℂ)⁻¹ * Complex.exp ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) +
        (2 : ℂ)⁻¹ * Complex.exp ((↑(-2 * Real.pi * x * -w) : ℂ) * Complex.I) := by
    rw [Complex.ofReal_cos, h1, h2, add_comm, ← key ((↑(2 * Real.pi * w * x : ℝ) : ℂ))]
  show soninMellinWeight b c hbc s x * ((Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ) =
    (2 : ℂ)⁻¹ * (Complex.exp ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) *
        soninMellinWeight b c hbc s x) +
      (2 : ℂ)⁻¹ * (Complex.exp ((↑(-2 * Real.pi * x * -w) : ℂ) * Complex.I) *
        soninMellinWeight b c hbc s x)
  rw [hcos]
  ring

/-- The cosine-modulated integral of any continuous compactly supported weight is the average of
two transform values. -/
theorem integral_mul_cos_eq_fourier_avg {g : ℝ → ℂ}
    (hcont : Continuous g) (hsupp : HasCompactSupport g) (w : ℝ) :
    (∫ x : ℝ, g x * (Real.cos (2 * Real.pi * w * x) : ℂ)) =
      (2 : ℂ)⁻¹ * 𝓕 g w + (2 : ℂ)⁻¹ * 𝓕 g (-w) := by
  have hE1 : Integrable (fun x : ℝ =>
      (2 : ℂ)⁻¹ * (Complex.exp ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) * g x)) volume := by
    refine (Continuous.integrable_of_hasCompactSupport ?_ ?_).const_mul _
    · exact (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)).mul hcont
    · exact hsupp.mul_left
  have hE2 : Integrable (fun x : ℝ =>
      (2 : ℂ)⁻¹ * (Complex.exp ((↑(-2 * Real.pi * x * -w) : ℂ) * Complex.I) * g x)) volume := by
    refine (Continuous.integrable_of_hasCompactSupport ?_ ?_).const_mul _
    · exact (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)).mul hcont
    · exact hsupp.mul_left
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add hE1 hE2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have key : ∀ z : ℂ, (2 : ℂ)⁻¹ * Complex.exp (z * Complex.I) +
      (2 : ℂ)⁻¹ * Complex.exp (-z * Complex.I) = Complex.cos z := by
    intro z
    rw [Complex.cos]
    ring
  have h1 : ((-2 * Real.pi * x * -w : ℝ) : ℂ) = ((2 * Real.pi * w * x : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : ((-2 * Real.pi * x * w : ℝ) : ℂ) = -((2 * Real.pi * w * x : ℝ) : ℂ) := by
    push_cast; ring
  have hcos : ((Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ) =
      (2 : ℂ)⁻¹ * Complex.exp ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) +
        (2 : ℂ)⁻¹ * Complex.exp ((↑(-2 * Real.pi * x * -w) : ℂ) * Complex.I) := by
    rw [Complex.ofReal_cos, h1, h2, add_comm, ← key ((↑(2 * Real.pi * w * x : ℝ) : ℂ))]
  show g x * ((Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ) =
    (2 : ℂ)⁻¹ * (Complex.exp ((↑(-2 * Real.pi * x * w) : ℂ) * Complex.I) * g x) +
      (2 : ℂ)⁻¹ * (Complex.exp ((↑(-2 * Real.pi * x * -w) : ℂ) * Complex.I) * g x)
  rw [hcos]
  ring

/-- **Rapid decay of a smooth compactly supported oscillatory integral.** -/
theorem tendsto_pow_mul_norm_integral_mul_cos {g : ℝ → ℂ}
    (hsupp : HasCompactSupport g) (hsmooth : ContDiff ℝ ∞ g) (N : ℕ) :
    Tendsto (fun w : ℝ => w ^ N * ‖∫ x : ℝ, g x * (Real.cos (2 * Real.pi * w * x) : ℂ)‖)
      atTop (𝓝 0) := by
  have hcont : Continuous g := hsmooth.continuous
  have hpos := tendsto_pow_mul_norm_fourier_atTop hsupp hsmooth N
  have hneg := tendsto_pow_mul_norm_fourier_neg_atTop hsupp hsmooth N
  have hmaj : Tendsto (fun w : ℝ =>
      (2 : ℝ)⁻¹ * (w ^ N * ‖𝓕 g w‖) + (2 : ℝ)⁻¹ * (w ^ N * ‖𝓕 g (-w)‖)) atTop (𝓝 0) := by
    simpa using (hpos.const_mul ((2 : ℝ)⁻¹)).add (hneg.const_mul ((2 : ℝ)⁻¹))
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
    rw [integral_mul_cos_eq_fourier_avg hcont hsupp w]
    calc w ^ N * ‖(2 : ℂ)⁻¹ * 𝓕 g w + (2 : ℂ)⁻¹ * 𝓕 g (-w)‖
        ≤ w ^ N * (‖(2 : ℂ)⁻¹ * 𝓕 g w‖ + ‖(2 : ℂ)⁻¹ * 𝓕 g (-w)‖) := by
          gcongr
          exact norm_add_le _ _
      _ = (2 : ℝ)⁻¹ * (w ^ N * ‖𝓕 g w‖) + (2 : ℝ)⁻¹ * (w ^ N * ‖𝓕 g (-w)‖) := by
          rw [norm_mul, norm_mul]
          simp only [norm_inv, Complex.norm_ofNat]
          ring

/-- The complexified profile is smooth. -/
theorem contDiff_ofReal_soninAnnulusBump (b c : ℝ) (hbc : b < c) :
    ContDiff ℝ ∞ (fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp
    ((soninAnnulusBumpData b c hbc).contDiff.add
      ((soninAnnulusBumpData b c hbc).contDiff.comp contDiff_neg))

/-- The complexified profile has compact support. -/
theorem hasCompactSupport_ofReal_soninAnnulusBump (b c : ℝ) (hb : 0 < b) (hbc : b < c) :
    HasCompactSupport (fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ)) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (hasCompactSupport_soninAnnulusBump b c hb hbc) ?_
  intro x hx
  refine subset_tsupport _ ?_
  intro h0
  exact hx (by simp [h0])

/-- **Rapid decay of the mean correction.** -/
theorem tendsto_pow_mul_abs_soninPacketMean (b c : ℝ) (hb : 0 < b) (hbc : b < c) (N : ℕ) :
    Tendsto (fun w : ℝ => w ^ N * |soninPacketMean b c hbc (2 * Real.pi * w)|)
      atTop (𝓝 0) := by
  have hmass := integral_soninAnnulusBump_pos b c hb hbc
  have hdecay := tendsto_pow_mul_norm_integral_mul_cos
    (hasCompactSupport_ofReal_soninAnnulusBump b c hb hbc)
    (contDiff_ofReal_soninAnnulusBump b c hbc) N
  have hlim : Tendsto (fun w : ℝ =>
      (w ^ N * ‖∫ x : ℝ, (soninAnnulusBump b c hbc x : ℂ) *
        ((Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ)‖) /
          ∫ x : ℝ, soninAnnulusBump b c hbc x) atTop (𝓝 0) := by
    simpa using hdecay.div_const (∫ x : ℝ, soninAnnulusBump b c hbc x)
  refine hlim.congr fun w => ?_
  have hreal : (∫ x : ℝ, (soninAnnulusBump b c hbc x : ℂ) *
      ((Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ)) =
      ((∫ x : ℝ, soninAnnulusBump b c hbc x * Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    push_cast
    ring
  rw [hreal, Complex.norm_real, Real.norm_eq_abs, soninPacketMean, abs_div,
    abs_of_pos hmass]
  ring

/-- **`(4c)`.**  Every fixed Mellin exponent is blind to the wavepacket to all orders in the
carrier. -/
theorem tendsto_pow_mul_norm_soninPacketMellin
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (s : ℂ) (N : ℕ) :
    Tendsto (fun w : ℝ => w ^ N * ‖soninPacketMellin b c hbc s (2 * Real.pi * w)‖)
      atTop (𝓝 0) := by
  have hW : Integrable (soninMellinWeight b c hbc s) volume := by
    refine Continuous.integrable_of_hasCompactSupport
      ((contDiff_soninMellinWeight b c hb hbc s).continuous) ?_
    exact hasCompactSupport_soninMellinWeight b c hbc s
  have hosc := tendsto_pow_mul_norm_integral_mul_cos
    (hasCompactSupport_soninMellinWeight b c hbc s)
    (contDiff_soninMellinWeight b c hb hbc s) N
  have hmean := tendsto_pow_mul_abs_soninPacketMean b c hb hbc N
  have hmaj : Tendsto (fun w : ℝ =>
      (w ^ N * ‖∫ x : ℝ, soninMellinWeight b c hbc s x *
          ((Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ)‖) +
        (w ^ N * |soninPacketMean b c hbc (2 * Real.pi * w)|) *
          ‖∫ x : ℝ, soninMellinWeight b c hbc s x‖) atTop (𝓝 0) := by
    simpa using hosc.add (hmean.mul_const ‖∫ x : ℝ, soninMellinWeight b c hbc s x‖)
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
    rw [soninPacketMellin_eq b c hb hbc s (2 * Real.pi * w)]
    calc w ^ N * ‖(∫ x : ℝ, soninMellinWeight b c hbc s x *
            ((Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ)) -
          (soninPacketMean b c hbc (2 * Real.pi * w) : ℂ) *
            ∫ x : ℝ, soninMellinWeight b c hbc s x‖
        ≤ w ^ N * (‖∫ x : ℝ, soninMellinWeight b c hbc s x *
              ((Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ)‖ +
            ‖(soninPacketMean b c hbc (2 * Real.pi * w) : ℂ) *
              ∫ x : ℝ, soninMellinWeight b c hbc s x‖) := by
          gcongr
          exact norm_sub_le _ _
      _ = (w ^ N * ‖∫ x : ℝ, soninMellinWeight b c hbc s x *
              ((Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ)‖) +
            (w ^ N * |soninPacketMean b c hbc (2 * Real.pi * w)|) *
              ‖∫ x : ℝ, soninMellinWeight b c hbc s x‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          ring

end RHTower
