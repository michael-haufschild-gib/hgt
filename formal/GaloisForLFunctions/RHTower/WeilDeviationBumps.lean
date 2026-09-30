import GaloisForLFunctions.RHTower.WeilDeviationPacketLimit
import GaloisForLFunctions.HTGeometry.FourierPowerBound
import GaloisForLFunctions.HTGeometry.FiniteRegularityFourierDecay

/-!
# Test functions for the excess rigidity argument

- **Smooth compactly supported amplitudes.** For `h ∈ C_c^∞`:
  - `𝓕h` has the Cauchy profile `‖𝓕h(x)‖ ≤ C/(1 + x²)` and finite moments `∫ ‖𝓕h(s)‖ |s|(1 + s²)`;
  - `𝓕h` is differentiable, and its derivative has the same profile.
  These are the hypotheses of the packet limit.
- **Real transforms.** The transform of an even real integrable function is real.
- **The positive-definite packet** `G = (m ⋆ m)/(m ⋆ m)(0)`, `m` an even bump. It satisfies
  `0 ≤ G ≤ 1`, `G(0) = 1`, and `𝓕G = (𝓕m)²/c ≥ 0`.
-/

open Complex MeasureTheory Filter Topology Set FourierTransform
open scoped Real ComplexConjugate ContDiff Convolution

namespace RHTower.WeilExcess

noncomputable section

/-! ## Smooth compactly supported amplitudes -/

section Smooth

variable {h : ℝ → ℂ} (hs : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
include hs hc

theorem exists_fourier_profile_smooth : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖𝓕 h x‖ ≤ C / (1 + x ^ 2) := by
  obtain ⟨C₀, hC₀, h₀⟩ := GaloisForLFunctions.HTGeometry.exists_pow_mul_norm_fourierIntegral_le hc hs 0
  obtain ⟨C₂, hC₂, h₂⟩ := GaloisForLFunctions.HTGeometry.exists_pow_mul_norm_fourierIntegral_le hc hs 2
  refine ⟨C₀ + C₂, by positivity, fun x => ?_⟩
  rw [le_div_iff₀ (by positivity)]
  have a := h₀ x
  have b := h₂ x
  rw [pow_zero, one_mul] at a
  rw [sq_abs] at b
  nlinarith [norm_nonneg (𝓕 h x)]

theorem integrable_fourier_smooth : Integrable (𝓕 h) := by
  obtain ⟨C, hC0, hC⟩ := exists_fourier_profile_smooth hs hc
  have hi : Integrable fun x : ℝ => C * (1 + x ^ 2)⁻¹ := integrable_inv_one_add_sq.const_mul C
  refine hi.mono' (continuous_fourier_integrable
    (hs.continuous.integrable_of_hasCompactSupport hc)).aestronglyMeasurable
    (Eventually.of_forall fun x => (hC x).trans (le_of_eq (by rw [div_eq_mul_inv])))

theorem integrable_fourier_moment_smooth :
    Integrable fun s => ‖𝓕 h s‖ * (|s| * (1 + s ^ 2)) := by
  obtain ⟨C₀, hC₀, h₀⟩ := GaloisForLFunctions.HTGeometry.exists_pow_mul_norm_fourierIntegral_le hc hs 0
  obtain ⟨C₅, hC₅, h₅⟩ := GaloisForLFunctions.HTGeometry.exists_pow_mul_norm_fourierIntegral_le hc hs 5
  have hi : Integrable fun x : ℝ => (4 * (C₀ + C₅)) * (1 + x ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul _
  refine hi.mono' ((continuous_fourier_integrable
    (hs.continuous.integrable_of_hasCompactSupport hc)).norm.mul
      (continuous_abs.mul (continuous_const.add (continuous_pow 2)))).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have a := h₀ x
  have b := h₅ x
  rw [pow_zero, one_mul] at a
  set N := ‖𝓕 h x‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  set y := |x| with hy
  have hy0 : 0 ≤ y := abs_nonneg x
  have hx2 : x ^ 2 = y ^ 2 := (sq_abs x).symm
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity),
    hx2]
  have key : y * (1 + y ^ 2) * (1 + y ^ 2) ≤ 4 + 4 * y ^ 5 := by
    rcases le_or_gt y 1 with h1 | h1
    · have h2 : y ^ 2 ≤ 1 := pow_le_one₀ hy0 h1
      have h3 : y * (1 + y ^ 2) ≤ 2 := by nlinarith
      have h4 : y * (1 + y ^ 2) * (1 + y ^ 2) ≤ 2 * 2 :=
        mul_le_mul h3 (by linarith) (by positivity) (by norm_num)
      have : (0 : ℝ) ≤ 4 * y ^ 5 := by positivity
      linarith
    · have h2 : 1 ≤ y ^ 2 := one_le_pow₀ h1.le
      have h3 : 1 + y ^ 2 ≤ 2 * y ^ 2 := by linarith
      have h4 : y * (1 + y ^ 2) * (1 + y ^ 2) ≤ y * (2 * y ^ 2) * (2 * y ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h3 hy0) h3 (by positivity) (by positivity)
      have h5 : y * (2 * y ^ 2) * (2 * y ^ 2) = 4 * y ^ 5 := by ring
      linarith
  calc N * (y * (1 + y ^ 2)) * (1 + y ^ 2) = N * (y * (1 + y ^ 2) * (1 + y ^ 2)) := by ring
    _ ≤ N * (4 + 4 * y ^ 5) := mul_le_mul_of_nonneg_left key hN0
    _ = 4 * N + 4 * (y ^ 5 * N) := by ring
    _ ≤ 4 * C₀ + 4 * C₅ := by linarith
    _ = 4 * (C₀ + C₅) := by ring

/-- The derivative of the transform: `(𝓕h)' = 𝓕(−2πi x h)`. -/
theorem hasDerivAt_fourier_smooth (w : ℝ) :
    HasDerivAt (𝓕 h) (𝓕 (fun x : ℝ => (-2 * π * I * x) • h x) w) w := by
  have hi : Integrable h := hs.continuous.integrable_of_hasCompactSupport hc
  have hxi : Integrable fun x : ℝ => x • h x :=
    ((continuous_id.smul hs.continuous)).integrable_of_hasCompactSupport (hc.smul_left)
  exact Real.hasDerivAt_fourier hi hxi w

theorem exists_deriv_fourier_profile_smooth :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖𝓕 (fun x : ℝ => (-2 * π * I * x) • h x) x‖ ≤ C / (1 + x ^ 2) := by
  have h0 : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := ofRealCLM.contDiff
  have h1 : ContDiff ℝ ∞ (fun x : ℝ => (-2 * π * I * (x : ℂ))) := contDiff_const.mul h0
  have hs' : ContDiff ℝ ∞ (fun x : ℝ => (-2 * π * I * x) • h x) := h1.smul hs
  have hc' : HasCompactSupport (fun x : ℝ => (-2 * π * I * x) • h x) :=
    HasCompactSupport.smul_left (f := fun x : ℝ => (-2 * π * I * (x : ℂ))) hc
  exact exists_fourier_profile_smooth hs' hc'

end Smooth

/-! ## Real transforms -/

/-- The transform of an even real integrable function is real. -/
theorem fourier_ofReal_even_im {f : ℝ → ℝ} (heven : ∀ x, f (-x) = f x) (ξ : ℝ) :
    (𝓕 (fun x => (f x : ℂ)) ξ).im = 0 := by
  have hconj : (starRingEnd ℂ) (𝓕 (fun x => (f x : ℂ)) ξ) = 𝓕 (fun x => (f x : ℂ)) ξ := by
    rw [fourier_eq_integral, ← integral_conj]
    rw [← integral_neg_eq_self (fun x => Complex.exp (-(2 * π * x * ξ : ℝ) * I) * (f x : ℂ))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [map_mul, Complex.conj_ofReal, heven, ← Complex.exp_conj, map_neg, Complex.conj_I]
    congr 2
    push_cast; ring
  have := congrArg Complex.im hconj
  rw [Complex.conj_im] at this
  linarith

/-! ## The positive-definite packet -/

/-- The even bump `m` supported in `[−1, 1]`, equal to `1` on `[−1/2, 1/2]`. -/
def pdBaseBump : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The autocorrelation `m ⋆ m`. -/
def pdConv (x : ℝ) : ℝ :=
  ∫ t, pdBaseBump t * pdBaseBump (x - t)

theorem pdConv_eq_convolution :
    pdConv = convolution (pdBaseBump : ℝ → ℝ) (pdBaseBump : ℝ → ℝ) (ContinuousLinearMap.lsmul ℝ ℝ)
      volume := by
  funext x
  rw [convolution_def]
  rfl

theorem contDiff_pdConv : ContDiff ℝ ∞ pdConv := by
  rw [pdConv_eq_convolution]
  exact pdBaseBump.hasCompactSupport.contDiff_convolution_left _ pdBaseBump.contDiff
    pdBaseBump.continuous.locallyIntegrable

theorem hasCompactSupport_pdConv : HasCompactSupport pdConv := by
  rw [pdConv_eq_convolution]
  exact pdBaseBump.hasCompactSupport.convolution _ pdBaseBump.hasCompactSupport

theorem pdConv_nonneg (x : ℝ) : 0 ≤ pdConv x :=
  integral_nonneg fun _ => mul_nonneg pdBaseBump.nonneg pdBaseBump.nonneg

theorem pdConv_le_zero (x : ℝ) : pdConv x ≤ pdConv 0 := by
  have hm : Continuous (pdBaseBump : ℝ → ℝ) := pdBaseBump.continuous
  have hmc : HasCompactSupport (pdBaseBump : ℝ → ℝ) := pdBaseBump.hasCompactSupport
  have hsq : Integrable fun t => pdBaseBump t * pdBaseBump t :=
    (hm.mul hm).integrable_of_hasCompactSupport hmc.mul_right
  have hsq' : Integrable fun t => pdBaseBump (x - t) * pdBaseBump (x - t) := by
    have := hsq.comp_sub_left x
    simpa using this
  have hprod : Integrable fun t => pdBaseBump t * pdBaseBump (x - t) :=
    (hm.mul (hm.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hmc.mul_right
  have hshift : (∫ t, pdBaseBump (x - t) * pdBaseBump (x - t)) =
      ∫ t, pdBaseBump t * pdBaseBump t := by
    have := integral_sub_left_eq_self (μ := volume)
      (fun t => pdBaseBump t * pdBaseBump t) x
    simpa using this
  have hmono : (∫ t, pdBaseBump t * pdBaseBump (x - t)) ≤
      ∫ t, (pdBaseBump t * pdBaseBump t + pdBaseBump (x - t) * pdBaseBump (x - t)) / 2 := by
    refine integral_mono hprod ((hsq.add hsq').div_const 2) fun t => ?_
    nlinarith [sq_nonneg (pdBaseBump t - pdBaseBump (x - t))]
  rw [integral_div, integral_add hsq hsq', hshift] at hmono
  have e : pdConv 0 = ∫ t, pdBaseBump t * pdBaseBump t := by
    unfold pdConv; congr 1; funext t; rw [zero_sub, pdBaseBump.neg]
  have e2 : pdConv x = ∫ t, pdBaseBump t * pdBaseBump (x - t) := rfl
  linarith

theorem pdConv_zero_pos : 0 < pdConv 0 := by
  unfold pdConv
  have hm : Continuous (pdBaseBump : ℝ → ℝ) := pdBaseBump.continuous
  have hint : Integrable fun t => pdBaseBump t * pdBaseBump (0 - t) :=
    (hm.mul (hm.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      pdBaseBump.hasCompactSupport.mul_right
  rw [integral_pos_iff_support_of_nonneg (fun t => mul_nonneg pdBaseBump.nonneg
    pdBaseBump.nonneg) hint]
  have hsub : Ioo (-1 : ℝ) 1 ⊆ Function.support fun t => pdBaseBump t * pdBaseBump (0 - t) := by
    intro t ht
    rw [Function.mem_support]
    have h1 : t ∈ Metric.ball (0 : ℝ) pdBaseBump.rOut := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      show |t| < 1
      exact abs_lt.mpr ⟨ht.1, ht.2⟩
    have h2 : 0 - t ∈ Metric.ball (0 : ℝ) pdBaseBump.rOut := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, zero_sub, abs_neg]
      show |t| < 1
      exact abs_lt.mpr ⟨ht.1, ht.2⟩
    exact (mul_pos (pdBaseBump.pos_of_mem_ball h1) (pdBaseBump.pos_of_mem_ball h2)).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  simp

theorem pdConv_neg (x : ℝ) : pdConv (-x) = pdConv x := by
  rw [pdConv_eq_convolution]
  exact convolution_neg_of_neg_eq _ (Eventually.of_forall fun t => pdBaseBump.neg t)
    (Eventually.of_forall fun t => pdBaseBump.neg t)

/-- **The positive-definite packet** `G = (m ⋆ m)/(m ⋆ m)(0)`. -/
def pdPacket (x : ℝ) : ℝ := pdConv x / pdConv 0

theorem pdPacket_zero : pdPacket 0 = 1 := div_self pdConv_zero_pos.ne'

theorem pdPacket_nonneg (x : ℝ) : 0 ≤ pdPacket x :=
  div_nonneg (pdConv_nonneg x) pdConv_zero_pos.le

theorem pdPacket_le_one (x : ℝ) : pdPacket x ≤ 1 := by
  rw [pdPacket, div_le_one pdConv_zero_pos]; exact pdConv_le_zero x

theorem pdPacket_neg (x : ℝ) : pdPacket (-x) = pdPacket x := by
  simp only [pdPacket, pdConv_neg]

theorem contDiff_pdPacket : ContDiff ℝ ∞ pdPacket :=
  contDiff_pdConv.div_const _

theorem hasCompactSupport_pdPacket : HasCompactSupport pdPacket := by
  refine hasCompactSupport_pdConv.mono' fun x hx => subset_tsupport _ ?_
  rw [Function.mem_support] at hx ⊢
  intro h0; apply hx; rw [pdPacket, h0, zero_div]

/-- The complex packet. -/
def pdPacketC (x : ℝ) : ℂ := (pdPacket x : ℂ)

theorem contDiff_pdPacketC : ContDiff ℝ ∞ pdPacketC :=
  Complex.ofRealCLM.contDiff.comp contDiff_pdPacket

theorem hasCompactSupport_pdPacketC : HasCompactSupport pdPacketC :=
  hasCompactSupport_pdPacket.comp_left Complex.ofReal_zero

/-- **The transform of the packet is nonnegative.** -/
theorem fourier_pdPacketC_nonneg (w : ℝ) :
    (𝓕 pdPacketC w).im = 0 ∧ 0 ≤ (𝓕 pdPacketC w).re := by
  set mC : ℝ → ℂ := fun x => ((pdBaseBump x : ℝ) : ℂ) with hmC
  have hmi : Integrable mC :=
    (Complex.continuous_ofReal.comp pdBaseBump.continuous).integrable_of_hasCompactSupport
      (pdBaseBump.hasCompactSupport.comp_left Complex.ofReal_zero)
  have hconv : pdPacketC = fun x => ((pdConv 0)⁻¹ : ℂ) *
      (mC ⋆[ContinuousLinearMap.mul ℂ ℂ] mC) x := by
    funext x
    simp only [pdPacketC, pdPacket, div_eq_mul_inv]
    push_cast
    rw [mul_comm]
    congr 1
    rw [convolution_def, pdConv, ← integral_complex_ofReal]
    push_cast
    rfl
  have hF : 𝓕 pdPacketC w = ((pdConv 0)⁻¹ : ℂ) * (𝓕 mC w * 𝓕 mC w) := by
    rw [← Real.fourier_mul_convolution_eq hmi hmi, hconv, fourier_eq_integral, fourier_eq_integral,
      ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  have him := fourier_ofReal_even_im (f := fun x => pdBaseBump x) (fun x => pdBaseBump.neg x) w
  have hre : 𝓕 mC w = ((𝓕 mC w).re : ℂ) := Complex.ext (by simp) (by simpa using him)
  rw [hF, hre]
  constructor
  · simp [← Complex.ofReal_inv, ← Complex.ofReal_mul]
  · rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
    exact mul_nonneg (inv_nonneg.mpr pdConv_zero_pos.le) (mul_self_nonneg _)

theorem pdPacket_eq_zero_of_two_le {x : ℝ} (hx : 2 ≤ |x|) : pdPacket x = 0 := by
  rw [pdPacket, pdConv]
  have h0 : (fun t => pdBaseBump t * pdBaseBump (x - t)) = fun _ => (0 : ℝ) := by
    funext t
    by_cases ht : |t| < 1
    · have : 1 ≤ |x - t| := by
        have := abs_sub_abs_le_abs_sub x t
        linarith
      rw [pdBaseBump.zero_of_le_dist (x := x - t) (by
        rw [Real.dist_eq, sub_zero]; exact this), mul_zero]
    · push Not at ht
      rw [pdBaseBump.zero_of_le_dist (x := t) (by rw [Real.dist_eq, sub_zero]; exact ht), zero_mul]
  rw [h0, integral_zero, zero_div]

/-! ## The flat bump and the flattened packet -/

/-- A bump equal to `1` on `[−1, 1]` and supported in `[−2, 2]`. -/
def excessFlatBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

/-- A cutoff equal to `1` on `[−2, 2]` and supported in `[−3, 3]`. -/
def excessWideCutoff : ContDiffBump (0 : ℝ) := ⟨2, 3, by norm_num, by norm_num⟩

theorem excessFlatBump_eq_one {x : ℝ} (hx : |x| ≤ 1) : excessFlatBump x = 1 :=
  excessFlatBump.one_of_mem_closedBall (by rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hx)

theorem excessFlatBump_eq_zero {x : ℝ} (hx : 2 ≤ |x|) : excessFlatBump x = 0 :=
  excessFlatBump.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hx)

theorem excessWideCutoff_eq_one {x : ℝ} (hx : |x| ≤ 2) : excessWideCutoff x = 1 :=
  excessWideCutoff.one_of_mem_closedBall (by rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hx)

/-- The flattening amplitude `h₁ = (1 − G) χ`, smooth, compactly supported, vanishing at `0`. -/
def excessFlatAmplitude (x : ℝ) : ℂ := ((1 - pdPacket x) * excessWideCutoff x : ℝ)

theorem excessFlatAmplitude_zero : excessFlatAmplitude 0 = 0 := by
  simp [excessFlatAmplitude, pdPacket_zero]

theorem contDiff_excessFlatAmplitude : ContDiff ℝ ∞ excessFlatAmplitude :=
  ofRealCLM.contDiff.comp ((contDiff_const.sub contDiff_pdPacket).mul excessWideCutoff.contDiff)

theorem hasCompactSupport_excessFlatAmplitude : HasCompactSupport excessFlatAmplitude := by
  refine excessWideCutoff.hasCompactSupport.mono' fun x hx => subset_tsupport _ ?_
  rw [Function.mem_support] at hx ⊢
  intro h0; apply hx; simp [excessFlatAmplitude, h0]

/-- The flattening correction `c_ε = (1 − G) B(·/ε)`. -/
def excessFlatCorrection (ε x : ℝ) : ℂ := ((1 - pdPacket x) * excessFlatBump (x / ε) : ℝ)

/-- The flattened packet `β_ε = G + (1 − G) B(·/ε)`. -/
def excessFlatPacket (ε x : ℝ) : ℝ := pdPacket x + (1 - pdPacket x) * excessFlatBump (x / ε)

theorem excessFlatPacket_nonneg (ε x : ℝ) : 0 ≤ excessFlatPacket ε x :=
  add_nonneg (pdPacket_nonneg x) (mul_nonneg (by linarith [pdPacket_le_one x]) excessFlatBump.nonneg)

theorem excessFlatPacket_le_one (ε x : ℝ) : excessFlatPacket ε x ≤ 1 := by
  have h1 := pdPacket_le_one x
  have h2 : excessFlatBump (x / ε) ≤ 1 := excessFlatBump.le_one
  have h3 : 0 ≤ 1 - pdPacket x := by linarith
  unfold excessFlatPacket
  nlinarith [mul_le_mul_of_nonneg_left h2 h3]

theorem excessFlatPacket_eq_one {ε x : ℝ} (hε : 0 < ε) (hx : |x| ≤ ε) : excessFlatPacket ε x = 1 := by
  have : |x / ε| ≤ 1 := by rw [abs_div, abs_of_pos hε, div_le_one hε]; exact hx
  simp [excessFlatPacket, excessFlatBump_eq_one this]

theorem excessFlatPacket_eq_zero {ε x : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1) (hx : 2 ≤ |x|) :
    excessFlatPacket ε x = 0 := by
  have h1 : 2 ≤ |x / ε| := by
    rw [abs_div, abs_of_pos hε0, le_div_iff₀ hε0]; nlinarith [abs_nonneg x]
  simp [excessFlatPacket, pdPacket_eq_zero_of_two_le hx, excessFlatBump_eq_zero h1]

theorem contDiff_excessFlatPacket (ε : ℝ) : ContDiff ℝ ∞ (excessFlatPacket ε) :=
  contDiff_pdPacket.add ((contDiff_const.sub contDiff_pdPacket).mul
    (excessFlatBump.contDiff.comp (contDiff_id.div_const ε)))

/-- The flattened packet splits as `G` plus the correction. -/
theorem excessFlatPacket_eq (ε x : ℝ) :
    ((excessFlatPacket ε x : ℝ) : ℂ) = pdPacketC x + excessFlatCorrection ε x := by
  simp [excessFlatPacket, pdPacketC, excessFlatCorrection]

/-- On the scale of the correction, the correction is the flattening amplitude times the flat
bump: `c_ε = h₁ · B(·/ε)` for `ε ≤ 1`. -/
theorem excessFlatCorrection_eq {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1) (x : ℝ) :
    excessFlatCorrection ε x = excessFlatAmplitude x * ((excessFlatBump (x / ε) : ℝ) : ℂ) := by
  simp only [excessFlatCorrection, excessFlatAmplitude]
  by_cases hx : |x| ≤ 2
  · rw [excessWideCutoff_eq_one hx]; push_cast; ring
  · push Not at hx
    have h1 : 2 ≤ |x / ε| := by
      rw [abs_div, abs_of_pos hε0, le_div_iff₀ hε0]; nlinarith [abs_nonneg x]
    rw [excessFlatBump_eq_zero h1]; push_cast; ring

end

end RHTower.WeilExcess
