import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheAliasingConstantOfTheTiltedSpline
import GaloisForLFunctions.RHTower.EvenSectorFullPositivity
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# The next coefficient of the tilted-spline aliasing

The periodic numerator has four nonconstant cosine modes. Two integrations
by parts make their averages against compact C² windows smaller than the
quadratic inverse-frequency scale. The next rational-tail coefficient can
therefore be read without an oscillatory term at that scale. Along `c → ∞`
and `c³/N → 0`, the scaled horizon aliasing has a two-term expansion whose
next coefficient is a negative multiple of the inverse-tenth-power moment.
-/

noncomputable section

open Finset MeasureTheory Filter Topology Zeta23
open scoped FourierTransform ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open ArithmeticDegenerationTheory SpacingScaleHarmonicAnalysis
  RenormalizedArithmeticPotentialTheory.CompletedShell

/-- The tilted numerator has precisely four nonconstant cosine modes. -/
theorem splineNumerator_cosine_expansion (x : ℝ) :
    let a := Real.sinh 1 ^ 2 + 1 / 2
    splineNumerator x = a ^ 4 + 3 * a ^ 2 / 4 + 3 / 128 +
      (-2 * a ^ 3 - 3 * a / 8) * Real.cos (2 * x) +
      (3 * a ^ 2 / 4 + 1 / 32) * Real.cos (4 * x) -
      a / 8 * Real.cos (6 * x) + 1 / 128 * Real.cos (8 * x) := by
  have hs : Real.sin x ^ 2 = (1 - Real.cos (2 * x)) / 2 := by
    nlinarith only [Real.cos_two_mul x, Real.sin_sq_add_cos_sq x]
  have h4 : Real.cos (4 * x) = 2 * Real.cos (2 * x) ^ 2 - 1 := by
    rw [show 4 * x = 2 * (2 * x) by ring, Real.cos_two_mul]
  have h6 : Real.cos (6 * x) = 4 * Real.cos (2 * x) ^ 3 - 3 * Real.cos (2 * x) := by
    rw [show 6 * x = 3 * (2 * x) by ring, Real.cos_three_mul]
  have h8 : Real.cos (8 * x) = 2 * Real.cos (4 * x) ^ 2 - 1 := by
    rw [show 8 * x = 2 * (4 * x) by ring, Real.cos_two_mul]
  dsimp only
  rw [splineNumerator, hs, h8, h6, h4]
  ring



private theorem integral_cos_natmul_pi (k : ℕ) (hk : k ≠ 0) :
    (∫ x in (0 : ℝ)..Real.pi, Real.cos ((k : ℝ) * x)) = 0 := by
  rw [intervalIntegral.integral_comp_mul_left Real.cos (by exact_mod_cast hk : (k : ℝ) ≠ 0),
    integral_cos]
  simp [Real.sin_nat_mul_pi]

/-- The mean of the periodic numerator, as an explicit positive polynomial. -/
theorem splineNumeratorMean_eq :
    let a := Real.sinh 1 ^ 2 + 1 / 2
    splineNumeratorMean = a ^ 4 + 3 * a ^ 2 / 4 + 3 / 128 := by
  let a := Real.sinh 1 ^ 2 + 1 / 2
  change splineNumeratorMean = a ^ 4 + 3 * a ^ 2 / 4 + 3 / 128
  have hcos (k : ℝ) : IntervalIntegrable (fun x => Real.cos (k * x)) volume 0 Real.pi :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  unfold splineNumeratorMean
  simp_rw [splineNumerator_cosine_expansion]
  rw [intervalIntegral.integral_add
      (((intervalIntegrable_const.add ((hcos 2).const_mul _)).add ((hcos 4).const_mul _)).sub
        ((hcos 6).const_mul _)) ((hcos 8).const_mul _),
    intervalIntegral.integral_sub
      ((intervalIntegrable_const.add ((hcos 2).const_mul _)).add ((hcos 4).const_mul _))
      ((hcos 6).const_mul _),
    intervalIntegral.integral_add (intervalIntegrable_const.add ((hcos 2).const_mul _))
      ((hcos 4).const_mul _),
    intervalIntegral.integral_add intervalIntegrable_const ((hcos 2).const_mul _)]
  simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul]
  have hc2 := integral_cos_natmul_pi 2 (by norm_num)
  have hc4 := integral_cos_natmul_pi 4 (by norm_num)
  have hc6 := integral_cos_natmul_pi 6 (by norm_num)
  have hc8 := integral_cos_natmul_pi 8 (by norm_num)
  norm_num only [Nat.cast_ofNat] at hc2 hc4 hc6 hc8
  rw [hc2, hc4, hc6, hc8]
  simp only [mul_zero, add_zero, sub_zero]
  dsimp only [a]
  field_simp

private theorem paperFT_neg_real_eq_fourier (g : ℝ → ℂ) (t : ℝ) :
    paperFT g (-(t : ℂ)) = 𝓕 g (t * (2 * Real.pi)⁻¹) := by
  rw [paperFT, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with x
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
  rw [mul_comm (g x)]
  congr 2
  push_cast
  field_simp

private theorem tendsto_paperFT_neg_atTop (g : ℝ → ℂ) :
    Tendsto (fun t : ℝ => paperFT g (-(t : ℂ))) atTop (𝓝 0) := by
  have h := ((Real.zero_at_infty_fourier g).mono_left atTop_le_cocompact).comp
    ((tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop).atTop_mul_const
      (inv_pos.mpr (by positivity : 0 < 2 * Real.pi)))
  simpa only [paperFT_neg_real_eq_fourier, Function.comp_def, id_eq] using h

/-- Twice differentiated compact transforms have vanishing quadratic Fourier tails. -/
theorem tendsto_sq_mul_paperFT_neg {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ 2 * paperFT g (-(t : ℂ))) atTop (𝓝 0) := by
  have h := (tendsto_paperFT_neg_atTop (deriv (deriv g))).neg
  simp only [neg_zero] at h
  refine h.congr fun t => ?_
  rw [RHTower.EvenSector.paperFT_deriv_deriv_of_compact hg hgc]
  ring

private theorem re_paperFT_neg_real {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (t : ℝ) :
    (paperFT (fun x => (F x : ℂ)) (-(t : ℂ))).re = ∫ x, F x * Real.cos (t * x) := by
  have hi : Integrable (fun x : ℝ => (F x : ℂ) * Complex.exp (Complex.I * -(t : ℂ) * x)) :=
    ((Complex.continuous_ofReal.comp hF).mul (by fun_prop)).integrable_of_hasCompactSupport
      (hFc.comp_left (g := Complex.ofReal) rfl).mul_right
  rw [paperFT]
  have hre : (∫ x : ℝ, (F x : ℂ) * Complex.exp (Complex.I * -(t : ℂ) * x)).re =
      ∫ x : ℝ, ((F x : ℂ) * Complex.exp (Complex.I * -(t : ℂ) * x)).re :=
    (Complex.reCLM.integral_comp_comm hi).symm
  rw [hre]
  apply integral_congr_ae
  filter_upwards with x
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im, Real.cos_neg]

/-- Every nonconstant cosine mode has quadratic averaging error tending to zero. -/
theorem tendsto_sq_mul_cos_average {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) {j : ℝ} (hj : 0 < j) :
    Tendsto (fun t : ℝ => t ^ 2 * ∫ x, F x * Real.cos (j * t * x)) atTop (𝓝 0) := by
  have hgc : HasCompactSupport (fun x => (F x : ℂ)) := hFc.comp_left (g := Complex.ofReal) rfl
  have hg : ContDiff ℝ 2 (fun x => (F x : ℂ)) := Complex.ofRealCLM.contDiff.comp hF
  have hzero : Tendsto (fun t : ℝ => t ^ 2 * ∫ x, F x * Real.cos (t * x))
      atTop (𝓝 0) := by
    have h := (Complex.continuous_re.tendsto 0).comp (tendsto_sq_mul_paperFT_neg hg hgc)
    simpa only [Function.comp_def, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
      re_paperFT_neg_real hF.continuous hFc, Complex.zero_re] using h
  have h := hzero.comp
    ((tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop).atTop_mul_const hj)
  have h' := h.div_const (j ^ 2)
  simp only [zero_div] at h'
  refine h'.congr fun t => ?_
  simp only [Function.comp_def, id_eq]
  rw [show t * j = j * t by ring]
  field_simp



/-- The periodic numerator contributes no term at quadratic inverse frequency. -/
theorem tendsto_sq_mul_numerator_average {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) :
    Tendsto (fun t : ℝ => t ^ 2 * ((∫ x, F x * splineNumerator (t * x)) -
      splineNumeratorMean * ∫ x, F x)) atTop (𝓝 0) := by
  let a := Real.sinh 1 ^ 2 + 1 / 2
  have iF : Integrable F := hF.continuous.integrable_of_hasCompactSupport hFc
  have iC (t j : ℝ) : Integrable fun x => F x * Real.cos (j * t * x) :=
    (hF.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hFc.mul_right
  have hsplit (t : ℝ) : (∫ x, F x * splineNumerator (t * x)) -
      splineNumeratorMean * ∫ x, F x =
      (-2 * a ^ 3 - 3 * a / 8) * (∫ x, F x * Real.cos (2 * t * x)) +
      (3 * a ^ 2 / 4 + 1 / 32) * (∫ x, F x * Real.cos (4 * t * x)) -
      a / 8 * (∫ x, F x * Real.cos (6 * t * x)) +
      1 / 128 * (∫ x, F x * Real.cos (8 * t * x)) := by
    have heq : (fun x => F x * splineNumerator (t * x)) = fun x =>
        splineNumeratorMean * F x +
        (-2 * a ^ 3 - 3 * a / 8) * (F x * Real.cos (2 * t * x)) +
        (3 * a ^ 2 / 4 + 1 / 32) * (F x * Real.cos (4 * t * x)) -
        a / 8 * (F x * Real.cos (6 * t * x)) +
        1 / 128 * (F x * Real.cos (8 * t * x)) := by
      funext x
      rw [splineNumerator_cosine_expansion, splineNumeratorMean_eq]
      simp only [mul_assoc]
      dsimp only [a]
      ring
    have i0 : Integrable (fun x => splineNumeratorMean * F x) := iF.const_mul _
    have i2 : Integrable (fun x => (-2 * a ^ 3 - 3 * a / 8) *
        (F x * Real.cos (2 * t * x))) := (iC t 2).const_mul _
    have i4 : Integrable (fun x => (3 * a ^ 2 / 4 + 1 / 32) *
        (F x * Real.cos (4 * t * x))) := (iC t 4).const_mul _
    have i6 : Integrable (fun x => (a / 8) *
        (F x * Real.cos (6 * t * x))) := (iC t 6).const_mul _
    have i8 : Integrable (fun x => (1 / 128 : ℝ) *
        (F x * Real.cos (8 * t * x))) := (iC t 8).const_mul _
    have hs8 := integral_add (((i0.add i2).add i4).sub i6) i8
    have hs6 := integral_sub ((i0.add i2).add i4) i6
    have hs4 := integral_add (i0.add i2) i4
    have hs2 := integral_add i0 i2
    simp only [Pi.add_apply, Pi.sub_apply] at hs8 hs6 hs4 hs2
    rw [heq, hs8, hs6, hs4, hs2]
    simp only [integral_const_mul]
    ring
  have h2 := tendsto_sq_mul_cos_average hF hFc (j := 2) (by norm_num)
  have h4 := tendsto_sq_mul_cos_average hF hFc (j := 4) (by norm_num)
  have h6 := tendsto_sq_mul_cos_average hF hFc (j := 6) (by norm_num)
  have h8 := tendsto_sq_mul_cos_average hF hFc (j := 8) (by norm_num)
  have hlim := (((h2.const_mul (-2 * a ^ 3 - 3 * a / 8)).add
    (h4.const_mul (3 * a ^ 2 / 4 + 1 / 32))).sub (h6.const_mul (a / 8))).add
    (h8.const_mul (1 / 128))
  simp only [mul_zero, add_zero, sub_zero] at hlim
  exact hlim.congr fun t => by rw [hsplit]; ring

/-- The first correction to the inverse-eighth-power spline tail is negative;
the remainder is nonnegative and bounded by the next inverse power. -/
theorem splineWeight_second_remainder {z : ℝ} (hz : 0 < z) :
    0 ≤ splineWeight z - (z ^ 8)⁻¹ + 4 * (z ^ 10)⁻¹ ∧
      splineWeight z - (z ^ 8)⁻¹ + 4 * (z ^ 10)⁻¹ ≤ 10 * (z ^ 12)⁻¹ := by
  have hid : splineWeight z - (z ^ 8)⁻¹ + 4 * (z ^ 10)⁻¹ =
      (z ^ 12)⁻¹ * (z ^ 2 * (10 * z ^ 6 + 20 * z ^ 4 + 15 * z ^ 2 + 4) /
        (1 + z ^ 2) ^ 4) := by
    unfold splineWeight
    field_simp
    ring
  rw [hid]
  have hden : 0 < (1 + z ^ 2) ^ 4 := by positivity
  have hratio : z ^ 2 * (10 * z ^ 6 + 20 * z ^ 4 + 15 * z ^ 2 + 4) /
      (1 + z ^ 2) ^ 4 ≤ 10 := by
    rw [div_le_iff₀ hden]
    nlinarith only [show 0 ≤ 20 * z ^ 6 + 45 * z ^ 4 + 36 * z ^ 2 + 10 by positivity]
  refine ⟨by positivity, ?_⟩
  simpa only [mul_comm (10 : ℝ)] using
    mul_le_mul_of_nonneg_left hratio (inv_nonneg.mpr (pow_nonneg hz.le 12))



/-- Exponentiating the variable preserves the smoothness of a compact window;
the extension across zero is locally zero. -/
theorem contDiff_logProfile {g : ℝ → ℝ} {A : ℝ} (hg : ContDiff ℝ 2 g)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0) : ContDiff ℝ 2 (logProfile g) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases le_or_gt x 0 with hx | hx
  · have hev : logProfile g =ᶠ[𝓝 x] fun _ => 0 :=
      (gt_mem_nhds (lt_of_le_of_lt hx (Real.exp_pos (-A)))).mono fun t ht =>
        logProfile_eq_zero_of_lt hsupp ht
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hev : logProfile g =ᶠ[𝓝 x] fun t => g (Real.log t) :=
      (lt_mem_nhds hx).mono fun t ht => by simp only [logProfile, if_pos ht]
    exact (hg.contDiffAt.comp x (Real.contDiffAt_log.mpr hx.ne')).congr_of_eventuallyEq hev

/-- The logarithmic profile vanishes outside the unit interval. -/
theorem hasCompactSupport_logProfile {g : ℝ → ℝ} {A : ℝ}
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0) : HasCompactSupport (logProfile g) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro x hx
  have heq := horizonProfile_eq_zero_of_notMem hsupp 1 hx
  rw [← logProfile_eq_horizonProfile] at heq
  exact_mod_cast heq

/-- Quadratic averaging on a logarithmic window, in the linear variable. -/
theorem tendsto_sq_mul_logProfile_average {g : ℝ → ℝ} {A : ℝ}
    (hg : ContDiff ℝ 2 g) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0) (hA : 0 ≤ A) :
    Tendsto (fun t : ℝ => t ^ 2 * ((∫ x in (0 : ℝ)..1,
      logProfile g x * splineNumerator (t * x)) -
      splineNumeratorMean * ∫ y, Real.exp y * g y)) atTop (𝓝 0) := by
  have hlim := tendsto_sq_mul_numerator_average (contDiff_logProfile hg hsupp)
    (hasCompactSupport_logProfile hsupp)
  have hbase : (∫ x, logProfile g x) = ∫ y, Real.exp y * g y := by
    rw [← integral_logProfile hg hsupp hA, intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    have heq := horizonProfile_eq_zero_of_notMem hsupp 1 hx
    rw [← logProfile_eq_horizonProfile] at heq
    exact_mod_cast heq
  rw [hbase] at hlim
  refine hlim.congr fun t => ?_
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  have heq := horizonProfile_eq_zero_of_notMem hsupp 1 hx
  rw [← logProfile_eq_horizonProfile] at heq
  have hz : logProfile g x = 0 := by exact_mod_cast heq
  rw [hz, zero_mul]

/-- The coefficient of an inverse power in one tilted-spline harmonic. -/
def splineTailCoefficient (p k : ℕ) : ℝ :=
  1 / 64 * (4 / Real.pi) ^ p * (((k : ℝ) + 1) ^ p)⁻¹

/-- Removing the first two rational-tail terms leaves a nonnegative remainder,
with its harmonic index retained in the summable bound. -/
theorem harmonic_second_remainder {c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (k : ℕ) {H2 : ℝ} (hH2 : 0 ≤ H2) :
    let q := splineNumerator (Real.pi * (k + 1) * c / 4 * x)
    let R := c ^ 2 * (H2 * (c ^ 8 * shellSpectrum tiltedUnitSpline
      ((k + 1) * (c * x))) - splineTailCoefficient 8 k * (H2 * (x ^ 8)⁻¹ * q)) +
      4 * splineTailCoefficient 10 k * (H2 * (x ^ 10)⁻¹ * q)
    0 ≤ R ∧ R ≤ 10 * splineTailCoefficient 12 k *
      (Real.sinh 1 ^ 2 + 1) ^ 4 * H2 * (c ^ 2)⁻¹ * (x ^ 12)⁻¹ := by
  have hpi := Real.pi_pos
  set z := Real.pi * ((k + 1) * (c * x)) / 4 with hz
  have hz0 : 0 < z := by positivity
  have hzeq : Real.pi * (k + 1) * c / 4 * x = z := by rw [hz]; ring
  dsimp only
  rw [shellSpectrum_tiltedUnitSpline, hzeq]
  have hq0 := splineNumerator_nonneg z
  have hqB := splineNumerator_le z
  have hid8 : c ^ 10 * (z ^ 8)⁻¹ =
      64 * c ^ 2 * splineTailCoefficient 8 k * (x ^ 8)⁻¹ := by
    rw [hz, splineTailCoefficient]
    field_simp
  have hid10 : c ^ 10 * (z ^ 10)⁻¹ =
      64 * splineTailCoefficient 10 k * (x ^ 10)⁻¹ := by
    rw [hz, splineTailCoefficient]
    field_simp
  have hid12 : c ^ 10 * (z ^ 12)⁻¹ =
      64 * splineTailCoefficient 12 k * (c ^ 2)⁻¹ * (x ^ 12)⁻¹ := by
    rw [hz, splineTailCoefficient]
    field_simp
  have hid : c ^ 2 * (H2 * (c ^ 8 * (1 / 64 * (splineNumerator z * splineWeight z))) -
      splineTailCoefficient 8 k * (H2 * (x ^ 8)⁻¹ * splineNumerator z)) +
      4 * splineTailCoefficient 10 k * (H2 * (x ^ 10)⁻¹ * splineNumerator z) =
      (1 / 64 * H2 * splineNumerator z) *
        (c ^ 10 * (splineWeight z - (z ^ 8)⁻¹ + 4 * (z ^ 10)⁻¹)) := by
    simp only [mul_add, mul_sub]
    rw [show c ^ 10 * (4 * (z ^ 10)⁻¹) =
      4 * (c ^ 10 * (z ^ 10)⁻¹) by ring, hid8, hid10]
    ring
  rw [hid]
  have hr := splineWeight_second_remainder hz0
  refine ⟨mul_nonneg (by positivity) (mul_nonneg (by positivity) hr.1), ?_⟩
  calc (1 / 64 * H2 * splineNumerator z) *
        (c ^ 10 * (splineWeight z - (z ^ 8)⁻¹ + 4 * (z ^ 10)⁻¹))
      ≤ (1 / 64 * H2 * splineNumerator z) * (c ^ 10 * (10 * (z ^ 12)⁻¹)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr.2 (by positivity)) (by positivity)
    _ ≤ (1 / 64 * H2 * (Real.sinh 1 ^ 2 + 1) ^ 4) *
        (c ^ 10 * (10 * (z ^ 12)⁻¹)) := by gcongr
    _ = 10 * splineTailCoefficient 12 k * (Real.sinh 1 ^ 2 + 1) ^ 4 *
        H2 * (c ^ 2)⁻¹ * (x ^ 12)⁻¹ := by
      rw [show c ^ 10 * (10 * (z ^ 12)⁻¹) = 10 * (c ^ 10 * (z ^ 12)⁻¹) by ring, hid12]
      ring


/-- At any fixed harmonic, the logarithmic window's discrete numerator average
has error smaller than `c⁻²` when `c³/N → 0`. -/
theorem tendsto_sq_mul_modulated_average {g : ℝ → ℝ} {A : ℝ}
    (hg : ContDiff ℝ 2 g) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0) (hA : 0 ≤ A)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (hc3N : Tendsto (fun N : ℕ => c N ^ 3 / N) atTop (𝓝 0))
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun N : ℕ => c N ^ 2 * ((N : ℝ)⁻¹ *
      ∑ n ∈ Finset.Icc 1 N, logProfile g (n / N) * splineNumerator (r * c N * (n / N)) -
      splineNumeratorMean * ∫ y, Real.exp y * g y)) atTop (𝓝 0) := by
  obtain ⟨Bg, -, hBg, -⟩ := exists_bound_lipschitz hg hsupp
  obtain ⟨Lg, hLg⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hsupp) hg (by norm_num)
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hBg 0)
  have hc2N : Tendsto (fun N : ℕ => c N ^ 2 / N) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => by positivity) (fun N => ?_) hc3N
    exact div_le_div_of_nonneg_right
      (pow_le_pow_right₀ (hc1 N) (by norm_num : 2 ≤ 3)) (Nat.cast_nonneg N)
  have havg : Tendsto (fun N : ℕ => c N ^ 2 *
      ((∫ x in (0 : ℝ)..1, logProfile g x * splineNumerator (r * c N * x)) -
        splineNumeratorMean * ∫ y, Real.exp y * g y)) atTop (𝓝 0) := by
    have ht := ((tendsto_sq_mul_logProfile_average hg hsupp hA).comp
      (hcinf.const_mul_atTop hr)).div_const (r ^ 2)
    simp only [zero_div] at ht
    refine ht.congr fun N => ?_
    simp only [Function.comp_def]
    field_simp
  have hbound := (hc2N.const_mul
    ((Lg : ℝ) * Real.exp (2 * A) * (Real.sinh 1 ^ 2 + 1) ^ 4)).add
    (hc3N.const_mul (Bg * r * (4 * (Real.sinh 1 ^ 2 + 1) ^ 3)))
  simp only [mul_zero, add_zero] at hbound
  have hdiff : Tendsto (fun N : ℕ => c N ^ 2 * ((N : ℝ)⁻¹ *
      ∑ n ∈ Finset.Icc 1 N, logProfile g (n / N) * splineNumerator (r * c N * (n / N)) -
      ∫ x in (0 : ℝ)..1, logProfile g x * splineNumerator (r * c N * x)))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hc0 : 0 < c N := by linarith [hc1 N]
    have hb := abs_riemann_modulated_sub_le hg hsupp hA hBg hLg
      (mul_pos hr hc0).le hN
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc c N ^ 2 * |(N : ℝ)⁻¹ *
          ∑ n ∈ Finset.Icc 1 N, logProfile g (n / N) * splineNumerator (r * c N * (n / N)) -
          ∫ x in (0 : ℝ)..1, logProfile g x * splineNumerator (r * c N * x)|
        ≤ c N ^ 2 * (((Lg : ℝ) * Real.exp (2 * A) * (Real.sinh 1 ^ 2 + 1) ^ 4 +
          Bg * (r * c N * (4 * (Real.sinh 1 ^ 2 + 1) ^ 3))) / N) :=
            mul_le_mul_of_nonneg_left hb (sq_nonneg _)
      _ = _ := by ring
  have ht := hdiff.add havg
  simp only [add_zero] at ht
  exact ht.congr fun N => by ring

/-- The quadratic averaging bound holds simultaneously at all positive harmonics
once the base frequency is large enough. -/
theorem exists_uniform_sq_mul_logProfile_average_bound {g : ℝ → ℝ} {A : ℝ}
    (hg : ContDiff ℝ 2 g) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0) (hA : 0 ≤ A) :
    ∃ T : ℝ, 0 < T ∧ ∀ c : ℝ, T ≤ c → ∀ k : ℕ,
      c ^ 2 * |(∫ x in (0 : ℝ)..1, logProfile g x *
        splineNumerator (Real.pi * (k + 1) * c / 4 * x)) -
        splineNumeratorMean * ∫ y, Real.exp y * g y| ≤
      (4 / Real.pi) ^ 2 * (((k : ℝ) + 1) ^ 2)⁻¹ := by
  have ht := (tendsto_sq_mul_logProfile_average hg hsupp hA).eventually
    (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))
  obtain ⟨R, hR⟩ := eventually_atTop.mp ht
  refine ⟨1 + |R| * (4 / Real.pi), by positivity, fun c hc k => ?_⟩
  have hpi := Real.pi_pos
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hc
  set lam := Real.pi * (k + 1) * c / 4 with hlam
  have hlam0 : 0 < lam := by positivity
  have hlR : R ≤ lam := by
    have hp : 0 < Real.pi / 4 := by positivity
    have hm := mul_le_mul_of_nonneg_left hc hp.le
    have he : Real.pi / 4 * (1 + |R| * (4 / Real.pi)) = Real.pi / 4 + |R| := by
      field_simp
    rw [he] at hm
    have hm' : Real.pi / 4 * c ≤ lam := by
      dsimp only [lam]
      have hkc : c ≤ ((k : ℝ) + 1) * c :=
        le_mul_of_one_le_left hc0.le (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
      nlinarith only [mul_le_mul_of_nonneg_left hkc hp.le]
    linarith only [le_abs_self R, hm, hm', hpi]
  have hsmall := hR lam hlR
  simp only [Real.dist_eq, sub_zero, abs_mul,
    abs_of_nonneg (sq_nonneg lam)] at hsmall
  have hid : c ^ 2 = (4 / Real.pi) ^ 2 * (((k : ℝ) + 1) ^ 2)⁻¹ * lam ^ 2 := by
    rw [hlam]
    field_simp
  rw [hid, mul_assoc]
  calc (4 / Real.pi) ^ 2 * (((k : ℝ) + 1) ^ 2)⁻¹ *
        (lam ^ 2 * |(∫ x in (0 : ℝ)..1, logProfile g x * splineNumerator (lam * x)) -
          splineNumeratorMean * ∫ y, Real.exp y * g y|)
      ≤ (4 / Real.pi) ^ 2 * (((k : ℝ) + 1) ^ 2)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hsmall.le (by positivity)
    _ = _ := mul_one _


/-- The logarithmic window average at a positive harmonic of the atom grid. -/
def modulatedWindowAverage (g : ℝ → ℝ) (c : ℝ) (N k : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, logProfile g (n / N) *
    splineNumerator (Real.pi * (k + 1) * c / 4 * (n / N))

/-- Every inverse-power harmonic coefficient beyond exponent one is summable. -/
theorem summable_splineTailCoefficient {p : ℕ} (hp : 1 < p) :
    Summable (splineTailCoefficient p) := by
  have hs := (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr hp)
  have hs' : Summable fun k : ℕ => (((k : ℝ) + 1) ^ p)⁻¹ :=
    hs.congr fun k => by push_cast; rfl
  exact hs'.mul_left (1 / 64 * (4 / Real.pi) ^ p)

private theorem abs_modulatedWindowAverage_le {g : ℝ → ℝ} {Bg : ℝ}
    (hBg : ∀ y, |g y| ≤ Bg) (c : ℝ) {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    |modulatedWindowAverage g c N k| ≤ Bg * (Real.sinh 1 ^ 2 + 1) ^ 4 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hBg 0)
  rw [modulatedWindowAverage, abs_mul, abs_of_pos (inv_pos.mpr hN0)]
  calc (N : ℝ)⁻¹ * |∑ n ∈ Finset.Icc 1 N, logProfile g (n / N) *
        splineNumerator (Real.pi * (k + 1) * c / 4 * (n / N))|
      ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, Bg * (Real.sinh 1 ^ 2 + 1) ^ 4 := by
        refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans ?_) (by positivity)
        refine Finset.sum_le_sum fun n _ => ?_
        rw [abs_mul, abs_of_nonneg (splineNumerator_nonneg _)]
        exact mul_le_mul (abs_logProfile_le hBg _) (splineNumerator_le _)
          (splineNumerator_nonneg _) hBg0
    _ = _ := by
      rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      field_simp

/-- Summing a modulated window against an absolutely summable harmonic power
commutes with its high-frequency limit. -/
theorem tendsto_tsum_modulatedWindowAverage {g : ℝ → ℝ} {A : ℝ}
    (hg : ContDiff ℝ 2 g) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0) (hA : 0 ≤ A)
    {c : ℕ → ℝ} (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) {p : ℕ} (hp : 1 < p) :
    Tendsto (fun N : ℕ => ∑' k : ℕ, splineTailCoefficient p k *
      modulatedWindowAverage g (c N) N k) atTop
      (𝓝 (∑' k : ℕ, splineTailCoefficient p k *
        (splineNumeratorMean * ∫ y, Real.exp y * g y))) := by
  obtain ⟨Bg, -, hBg, -⟩ := exists_bound_lipschitz hg hsupp
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hBg 0)
  have hcoeff (k : ℕ) : 0 ≤ splineTailCoefficient p k := by
    unfold splineTailCoefficient
    have := Real.pi_pos
    positivity
  have hbound := (summable_splineTailCoefficient hp).mul_right
    (Bg * (Real.sinh 1 ^ 2 + 1) ^ 4)
  apply tendsto_tsum_of_dominated_convergence hbound
  · intro k
    have hr : 0 < Real.pi * ((k : ℝ) + 1) / 4 := by positivity
    have hl := hcinf.const_mul_atTop hr
    have hlN : Tendsto (fun N : ℕ => (Real.pi * ((k : ℝ) + 1) / 4 * c N) / N)
        atTop (𝓝 0) := by
      have ht := hcN.const_mul (Real.pi * ((k : ℝ) + 1) / 4)
      simp only [mul_zero] at ht
      exact ht.congr fun N => by ring
    have ht := (tendsto_modulated hg hsupp hA hl hlN).const_mul
      (splineTailCoefficient p k)
    simpa only [modulatedWindowAverage, div_mul_eq_mul_div] using ht
  · filter_upwards [eventually_ge_atTop 1] with N hN
    intro k
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hcoeff k)]
    exact mul_le_mul_of_nonneg_left (abs_modulatedWindowAverage_le hBg (c N) hN k) (hcoeff k)

/-- A single summable harmonic majorant controls the scaled averaging error. -/
theorem eventually_abs_scaled_modulated_le {g : ℝ → ℝ} {A : ℝ}
    (hg : ContDiff ℝ 2 g) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0) (hA : 0 ≤ A)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (hc3N : Tendsto (fun N : ℕ => c N ^ 3 / N) atTop (𝓝 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      c N ^ 2 * |modulatedWindowAverage g (c N) N k -
        splineNumeratorMean * ∫ y, Real.exp y * g y| ≤ C * ((k : ℝ) + 1) := by
  obtain ⟨Bg, -, hBg, -⟩ := exists_bound_lipschitz hg hsupp
  obtain ⟨Lg, hLg⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hsupp) hg (by norm_num)
  obtain ⟨T, -, hT⟩ := exists_uniform_sq_mul_logProfile_average_bound hg hsupp hA
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hBg 0)
  let C1 := (Lg : ℝ) * Real.exp (2 * A) * (Real.sinh 1 ^ 2 + 1) ^ 4
  let C2 := Bg * (Real.pi / 4) * (4 * (Real.sinh 1 ^ 2 + 1) ^ 3)
  let C3 := (4 / Real.pi) ^ 2
  have hC1 : 0 ≤ C1 := by positivity
  have hC2 : 0 ≤ C2 := by positivity
  have hC3 : 0 ≤ C3 := by positivity
  refine ⟨C1 + C2 + C3, by positivity, ?_⟩
  filter_upwards [hcinf.eventually (eventually_ge_atTop T),
    hc3N.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop 1] with N hcT hc3 hN
  intro k
  have hc0 : 0 < c N := by linarith [hc1 N]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hk : 1 ≤ (k : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hc2 : c N ^ 2 / N ≤ 1 :=
    (div_le_div_of_nonneg_right (pow_le_pow_right₀ (hc1 N) (by norm_num : 2 ≤ 3))
      hN0.le).trans hc3.le
  let lam := Real.pi * (k + 1) * c N / 4
  have hlam0 : 0 ≤ lam := by positivity
  have hR := abs_riemann_modulated_sub_le hg hsupp hA hBg hLg hlam0 hN
  have hAv := hT (c N) hcT k
  have hi : (((k : ℝ) + 1) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hk)
  have hRbound : c N ^ 2 *
      (((Lg : ℝ) * Real.exp (2 * A) * (Real.sinh 1 ^ 2 + 1) ^ 4 +
        Bg * (lam * (4 * (Real.sinh 1 ^ 2 + 1) ^ 3))) / N) ≤ C1 + C2 * (k + 1) := by
    calc _ = C1 * (c N ^ 2 / N) + C2 * ((k : ℝ) + 1) * (c N ^ 3 / N) := by
            dsimp only [C1, C2, lam]
            ring
      _ ≤ C1 * 1 + C2 * ((k : ℝ) + 1) * 1 := by gcongr
      _ = _ := by ring
  have htri := abs_sub_le (modulatedWindowAverage g (c N) N k)
    (∫ x in (0 : ℝ)..1, logProfile g x * splineNumerator (lam * x))
    (splineNumeratorMean * ∫ y, Real.exp y * g y)
  calc c N ^ 2 * |modulatedWindowAverage g (c N) N k -
        splineNumeratorMean * ∫ y, Real.exp y * g y|
      ≤ c N ^ 2 * |modulatedWindowAverage g (c N) N k -
          ∫ x in (0 : ℝ)..1, logProfile g x * splineNumerator (lam * x)| +
        c N ^ 2 * |(∫ x in (0 : ℝ)..1, logProfile g x * splineNumerator (lam * x)) -
          splineNumeratorMean * ∫ y, Real.exp y * g y| := by
          simpa only [mul_add] using mul_le_mul_of_nonneg_left htri (sq_nonneg _)
    _ ≤ C1 + C2 * ((k : ℝ) + 1) + C3 * (((k : ℝ) + 1) ^ 2)⁻¹ :=
      add_le_add ((mul_le_mul_of_nonneg_left hR (sq_nonneg _)).trans hRbound) hAv
    _ ≤ (C1 + C2 + C3) * ((k : ℝ) + 1) := by
      have h1 := mul_le_mul_of_nonneg_left hk hC1
      have h3 := mul_le_mul_of_nonneg_left (hi.trans hk) hC3
      nlinarith only [h1, h3]

/-- The summed inverse-eighth-power numerator has no quadratic correction. -/
theorem tendsto_tsum_scaled_modulatedWindowAverage {g : ℝ → ℝ} {A : ℝ}
    (hg : ContDiff ℝ 2 g) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0) (hA : 0 ≤ A)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (hc3N : Tendsto (fun N : ℕ => c N ^ 3 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑' k : ℕ, splineTailCoefficient 8 k *
      (c N ^ 2 * (modulatedWindowAverage g (c N) N k -
        splineNumeratorMean * ∫ y, Real.exp y * g y))) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := eventually_abs_scaled_modulated_le hg hsupp hA hc1 hcinf hc3N
  let D := 1 / 64 * (4 / Real.pi) ^ 8 * C
  have hs := (summable_nat_add_iff 1).mpr
    (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 7))
  have hs' : Summable fun k : ℕ => (((k : ℝ) + 1) ^ 7)⁻¹ :=
    hs.congr fun k => by push_cast; rfl
  let F : ℕ → ℕ → ℝ := fun N k => splineTailCoefficient 8 k *
    (c N ^ 2 * (modulatedWindowAverage g (c N) N k -
      splineNumeratorMean * ∫ y, Real.exp y * g y))
  have hlim (k : ℕ) : Tendsto (fun N => F N k) atTop (𝓝 0) := by
    have hr : 0 < Real.pi * ((k : ℝ) + 1) / 4 := by positivity
    have ht := (tendsto_sq_mul_modulated_average hg hsupp hA hc1 hcinf hc3N hr).const_mul
      (splineTailCoefficient 8 k)
    simp only [mul_zero] at ht
    simpa only [F, modulatedWindowAverage, div_mul_eq_mul_div] using ht
  have hdom : ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, ‖F N k‖ ≤ D * (((k : ℝ) + 1) ^ 7)⁻¹ := by
    filter_upwards [hbound] with N hN
    intro k
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    have hcoeff : 0 ≤ splineTailCoefficient 8 k := by
      unfold splineTailCoefficient
      positivity
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hcoeff, abs_mul,
      abs_of_nonneg (sq_nonneg _)]
    calc splineTailCoefficient 8 k * (c N ^ 2 *
          |modulatedWindowAverage g (c N) N k - splineNumeratorMean * ∫ y, Real.exp y * g y|)
        ≤ splineTailCoefficient 8 k * (C * ((k : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (hN k) hcoeff
      _ = D * (((k : ℝ) + 1) ^ 7)⁻¹ := by
          dsimp only [splineTailCoefficient, D]
          field_simp
  have ht := tendsto_tsum_of_dominated_convergence (hs'.mul_left D)
    (g := fun _ : ℕ => (0 : ℝ)) hlim hdom
  simpa only [tsum_zero, F] using ht

/-- Squared window weighted by the inverse power read by a grid harmonic. -/
def harmonicWindowWeight (p : ℕ) (h : ℝ → ℝ) (y : ℝ) : ℝ :=
  h y ^ 2 * Real.exp (-((p : ℝ) * y))

theorem contDiff_harmonicWindowWeight (p : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h) :
    ContDiff ℝ 2 (harmonicWindowWeight p h) :=
  (hh.pow 2).mul (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id).neg)

theorem harmonicWindowWeight_eq_zero (p : ℕ) {h : ℝ → ℝ} {A : ℝ}
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {y : ℝ} (hy : y ∉ Set.Icc (-A) 0) :
    harmonicWindowWeight p h y = 0 := by
  rw [harmonicWindowWeight, hsupp y hy]
  ring

theorem logProfile_harmonicWindowWeight {x : ℝ} (hx : 0 < x) (p : ℕ) (h : ℝ → ℝ) :
    logProfile (harmonicWindowWeight p h) x = h (Real.log x) ^ 2 * (x ^ p)⁻¹ := by
  rw [logProfile, if_pos hx, harmonicWindowWeight, Real.exp_neg,
    Real.exp_nat_mul, Real.exp_log hx]

/-- The exact finite average of the two-term rational remainder. -/
theorem horizonHarmonic_second_remainder {h : ℝ → ℝ} {A Bh : ℝ}
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hB : ∀ y, |h y| ≤ Bh)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    let F := (N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, h (Real.log n - Real.log N) ^ 2 *
      (c ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c * (n / N))))
    let R := c ^ 2 * (F - splineTailCoefficient 8 k *
      modulatedWindowAverage (harmonicWindowWeight 8 h) c N k) +
      4 * splineTailCoefficient 10 k * modulatedWindowAverage (harmonicWindowWeight 10 h) c N k
    0 ≤ R ∧ R ≤ 10 * splineTailCoefficient 12 k * (Real.sinh 1 ^ 2 + 1) ^ 4 *
      (Bh ^ 2 * Real.exp (12 * A)) * (c ^ 2)⁻¹ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hB0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  let Rn : ℕ → ℝ := fun n => c ^ 2 * (h (Real.log n - Real.log N) ^ 2 *
      (c ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c * (n / N)))) -
      splineTailCoefficient 8 k * (logProfile (harmonicWindowWeight 8 h) (n / N) *
        splineNumerator (Real.pi * (k + 1) * c / 4 * (n / N)))) +
    4 * splineTailCoefficient 10 k * (logProfile (harmonicWindowWeight 10 h) (n / N) *
      splineNumerator (Real.pi * (k + 1) * c / 4 * (n / N)))
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      0 ≤ Rn n ∧ Rn n ≤ 10 * splineTailCoefficient 12 k *
        (Real.sinh 1 ^ 2 + 1) ^ 4 * (Bh ^ 2 * Real.exp (12 * A)) * (c ^ 2)⁻¹ := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hx : (0 : ℝ) < n / N := div_pos hn0 hN0
    have hl : Real.log ((n : ℝ) / N) = Real.log n - Real.log N :=
      Real.log_div hn0.ne' hN0.ne'
    have hr := harmonic_second_remainder hc hx k (sq_nonneg (h (Real.log ((n : ℝ) / N))))
    dsimp only at hr
    dsimp only [Rn]
    rw [logProfile_harmonicWindowWeight hx, logProfile_harmonicWindowWeight hx, ← hl]
    refine ⟨hr.1, hr.2.trans ?_⟩
    have h12 := sq_mul_inv_pow_le hsupp hx 12
    have hh2 : h (Real.log ((n : ℝ) / N)) ^ 2 ≤ Bh ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hB _) 2
    have hmass : h (Real.log ((n : ℝ) / N)) ^ 2 * (((n : ℝ) / N) ^ 12)⁻¹ ≤
        Bh ^ 2 * Real.exp (12 * A) :=
      h12.trans (by norm_num only [Nat.cast_ofNat]; gcongr)
    have hcoeff : 0 ≤ 10 * splineTailCoefficient 12 k * (Real.sinh 1 ^ 2 + 1) ^ 4 * (c ^ 2)⁻¹ := by
      unfold splineTailCoefficient
      positivity
    nlinarith only [mul_le_mul_of_nonneg_left hmass hcoeff]
  dsimp only
  have heq : c ^ 2 * ((N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, h (Real.log n - Real.log N) ^ 2 *
      (c ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c * (n / N)))) -
      splineTailCoefficient 8 k * modulatedWindowAverage (harmonicWindowWeight 8 h) c N k) +
      4 * splineTailCoefficient 10 k * modulatedWindowAverage (harmonicWindowWeight 10 h) c N k =
      (N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, Rn n := by
    simp only [modulatedWindowAverage, Rn, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    ring
  rw [heq]
  refine ⟨mul_nonneg (by positivity) (Finset.sum_nonneg fun n hn => (hterm n hn).1), ?_⟩
  calc (N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, Rn n ≤ (N : ℝ)⁻¹ *
        ∑ _n ∈ Finset.Icc 1 N, 10 * splineTailCoefficient 12 k *
          (Real.sinh 1 ^ 2 + 1) ^ 4 * (Bh ^ 2 * Real.exp (12 * A)) * (c ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n hn => (hterm n hn).2) (by positivity)
    _ = _ := by
      rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      field_simp

/-- The rational remainder vanishes after summing all harmonics and scaling
by the first inverse-square correction. -/
theorem tendsto_tsum_harmonic_second_remainder {h : ℝ → ℝ} {A : ℝ}
    (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop) :
    Tendsto (fun N : ℕ => ∑' k : ℕ, (
      c N ^ 2 * ((N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, h (Real.log n - Real.log N) ^ 2 *
        (c N ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c N * (n / N)))) -
        splineTailCoefficient 8 k * modulatedWindowAverage (harmonicWindowWeight 8 h) (c N) N k) +
      4 * splineTailCoefficient 10 k * modulatedWindowAverage (harmonicWindowWeight 10 h) (c N) N k))
      atTop (𝓝 0) := by
  obtain ⟨Bh, -, hB, -⟩ := exists_bound_lipschitz hh hsupp
  let D := 10 * (Real.sinh 1 ^ 2 + 1) ^ 4 * (Bh ^ 2 * Real.exp (12 * A))
  have hD : 0 ≤ D := by positivity
  let R : ℕ → ℕ → ℝ := fun N k => c N ^ 2 * ((N : ℝ)⁻¹ *
    ∑ n ∈ Finset.Icc 1 N, h (Real.log n - Real.log N) ^ 2 *
      (c N ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c N * (n / N)))) -
      splineTailCoefficient 8 k * modulatedWindowAverage (harmonicWindowWeight 8 h) (c N) N k) +
    4 * splineTailCoefficient 10 k * modulatedWindowAverage (harmonicWindowWeight 10 h) (c N) N k
  have hb (N : ℕ) (hN : 1 ≤ N) (k : ℕ) :
      0 ≤ R N k ∧ R N k ≤ D * splineTailCoefficient 12 k * (c N ^ 2)⁻¹ := by
    have hr := horizonHarmonic_second_remainder hsupp hB (c := c N) (by linarith [hc1 N]) hN k
    dsimp only at hr
    refine ⟨hr.1, hr.2.trans_eq ?_⟩
    dsimp only [D]
    ring
  have hcinv : Tendsto (fun N : ℕ => (c N ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp hcinf)
  have hlim (k : ℕ) : Tendsto (fun N => R N k) atTop (𝓝 0) := by
    have ht := hcinv.const_mul (D * splineTailCoefficient 12 k)
    simp only [mul_zero] at ht
    refine squeeze_zero' ?_ ?_ ht
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact (hb N hN k).1
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact (hb N hN k).2
  have hdom : ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, ‖R N k‖ ≤ D * splineTailCoefficient 12 k := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (hb N hN k).1]
    refine (hb N hN k).2.trans ?_
    have hcoeff : 0 ≤ splineTailCoefficient 12 k := by unfold splineTailCoefficient; positivity
    have hc2 : (c N ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (hc1 N))
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hc2 (mul_nonneg hD hcoeff)
  have ht := tendsto_tsum_of_dominated_convergence
    ((summable_splineTailCoefficient (by norm_num : 1 < 12)).mul_left D)
    (g := fun _ : ℕ => (0 : ℝ)) hlim hdom
  simpa only [tsum_zero, R] using ht


private theorem summable_tailCoefficient_mul_modulated {g : ℝ → ℝ} {Bg : ℝ}
    (hBg : ∀ y, |g y| ≤ Bg) {p : ℕ} (hp : 1 < p) (c : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    Summable fun k : ℕ => splineTailCoefficient p k * modulatedWindowAverage g c N k := by
  refine Summable.of_norm_bounded
    ((summable_splineTailCoefficient hp).mul_right (Bg * (Real.sinh 1 ^ 2 + 1) ^ 4)) fun k => ?_
  have hcoeff : 0 ≤ splineTailCoefficient p k := by
    unfold splineTailCoefficient
    positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hcoeff]
  exact mul_le_mul_of_nonneg_left (abs_modulatedWindowAverage_le hBg c hN k) hcoeff

private theorem summable_horizonHarmonic (h : ℝ → ℝ) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 1 ≤ N) :
    Summable fun k : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
      h (Real.log n - Real.log N) ^ 2 *
        (c ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c * (n / N)))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm (n : ℕ) (hn : 0 < n) : Summable fun k : ℕ =>
      h (Real.log n - Real.log N) ^ 2 *
        (c ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c * (n / N)))) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    exact (((hasAlias_tilted (c * (n / N)) (by positivity)).summable).mul_left _).mul_left _
  have hsum (s : Finset ℕ) (hs : ∀ n ∈ s, 0 < n) : Summable fun k : ℕ =>
      ∑ n ∈ s, h (Real.log n - Real.log N) ^ 2 *
        (c ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c * (n / N)))) := by
    classical
    revert hs
    refine Finset.induction_on s (fun _ => by simp) ?_
    intro n s hn ih hs
    have h1 := hterm n (hs n (Finset.mem_insert_self n s))
    have h2 := ih (fun m hm => hs m (Finset.mem_insert_of_mem hm))
    simpa only [Finset.sum_insert hn] using h1.add h2
  exact (hsum (Finset.Icc 1 N) (fun n hn => (Finset.mem_Icc.mp hn).1)).mul_left _

/-- The first correction to horizon aliasing is the negative inverse-tenth-power
moment. The averaging and discretization errors are smaller than `c⁻²`. -/
theorem tendsto_twoTerm_horizonAlias {h : ℝ → ℝ} {A : ℝ}
    (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hA : 0 ≤ A)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (hc3N : Tendsto (fun N : ℕ => c N ^ 3 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => c N ^ 2 * (c N ^ 8 * horizonAlias tiltedUnitSpline h (c N) N -
      2 * ∑' k : ℕ, splineTailCoefficient 8 k *
        (splineNumeratorMean * ∫ y, Real.exp y * harmonicWindowWeight 8 h y))) atTop
      (𝓝 (-8 * ∑' k : ℕ, splineTailCoefficient 10 k *
        (splineNumeratorMean * ∫ y, Real.exp y * harmonicWindowWeight 10 h y))) := by
  let m8 := splineNumeratorMean * ∫ y, Real.exp y * harmonicWindowWeight 8 h y
  let m10 := splineNumeratorMean * ∫ y, Real.exp y * harmonicWindowWeight 10 h y
  let F : ℕ → ℕ → ℝ := fun N k => (N : ℝ)⁻¹ *
    ∑ n ∈ Finset.Icc 1 N, h (Real.log n - Real.log N) ^ 2 *
      (c N ^ 8 * shellSpectrum tiltedUnitSpline ((k + 1) * (c N * (n / N))))
  let A8 : ℕ → ℕ → ℝ := fun N k => splineTailCoefficient 8 k *
    modulatedWindowAverage (harmonicWindowWeight 8 h) (c N) N k
  let A10 : ℕ → ℕ → ℝ := fun N k => splineTailCoefficient 10 k *
    modulatedWindowAverage (harmonicWindowWeight 10 h) (c N) N k
  let R : ℕ → ℕ → ℝ := fun N k => c N ^ 2 * (F N k - A8 N k) + 4 * A10 N k
  let E : ℕ → ℕ → ℝ := fun N k => splineTailCoefficient 8 k *
    (c N ^ 2 * (modulatedWindowAverage (harmonicWindowWeight 8 h) (c N) N k - m8))
  have hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => by have := hc1 N; positivity) (fun N => ?_) hc3N
    have hp := pow_le_pow_right₀ (hc1 N) (by norm_num : 1 ≤ 3)
    rw [pow_one] at hp
    exact div_le_div_of_nonneg_right hp (Nat.cast_nonneg N)
  have hR : Tendsto (fun N => ∑' k, R N k) atTop (𝓝 0) := by
    simpa only [R, F, A8, A10, mul_assoc] using
      tendsto_tsum_harmonic_second_remainder hh hsupp hc1 hcinf
  have hE : Tendsto (fun N => ∑' k, E N k) atTop (𝓝 0) :=
    tendsto_tsum_scaled_modulatedWindowAverage (contDiff_harmonicWindowWeight 8 hh)
      (fun y hy => harmonicWindowWeight_eq_zero 8 hsupp hy) hA hc1 hcinf hc3N
  have hA10 : Tendsto (fun N => ∑' k, A10 N k) atTop
      (𝓝 (∑' k, splineTailCoefficient 10 k * m10)) :=
    tendsto_tsum_modulatedWindowAverage (contDiff_harmonicWindowWeight 10 hh)
      (fun y hy => harmonicWindowWeight_eq_zero 10 hsupp hy) hA hcinf hcN (by norm_num)
  have ht := ((hR.const_mul 2).add (hE.const_mul 2)).sub (hA10.const_mul 8)
  simp only [mul_zero, add_zero, zero_sub] at ht
  obtain ⟨B8, -, hB8, -⟩ := exists_bound_lipschitz (contDiff_harmonicWindowWeight 8 hh)
    (fun y hy => harmonicWindowWeight_eq_zero 8 hsupp hy)
  obtain ⟨B10, -, hB10, -⟩ := exists_bound_lipschitz (contDiff_harmonicWindowWeight 10 hh)
    (fun y hy => harmonicWindowWeight_eq_zero 10 hsupp hy)
  rw [neg_mul]
  refine ht.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hc0 : 0 < c N := by linarith [hc1 N]
  have hf : Summable (F N) := summable_horizonHarmonic h hc0 hN
  have ha8 : Summable (A8 N) :=
    summable_tailCoefficient_mul_modulated hB8 (by norm_num) (c N) hN
  have ha10 : Summable (A10 N) :=
    summable_tailCoefficient_mul_modulated hB10 (by norm_num) (c N) hN
  have hm8 : Summable fun k => splineTailCoefficient 8 k * m8 :=
    (summable_splineTailCoefficient (by norm_num)).mul_right _
  have hr : Summable (R N) := by
    simpa only [R, mul_assoc] using ((hf.sub ha8).mul_left (c N ^ 2)).add (ha10.mul_left 4)
  have he : Summable (E N) := by
    have hs := (ha8.sub hm8).mul_left (c N ^ 2)
    refine hs.congr fun k => ?_
    dsimp only [A8, E]
    ring
  have heq (k : ℕ) : R N k + E N k - 4 * A10 N k =
      c N ^ 2 * (F N k - splineTailCoefficient 8 k * m8) := by
    dsimp only [R, E, A8]
    ring
  change 2 * (∑' k, R N k) + 2 * (∑' k, E N k) - 8 * (∑' k, A10 N k) = _
  calc 2 * (∑' k, R N k) + 2 * (∑' k, E N k) - 8 * (∑' k, A10 N k)
      = 2 * ∑' k, (R N k + E N k - 4 * A10 N k) := by
        rw [(hr.add he).tsum_sub (ha10.mul_left 4), hr.tsum_add he, tsum_mul_left]
        ring
    _ = 2 * ∑' k, c N ^ 2 * (F N k - splineTailCoefficient 8 k * m8) := by
        congr 1
        exact tsum_congr heq
    _ = c N ^ 2 * (c N ^ 8 * horizonAlias tiltedUnitSpline h (c N) N -
        2 * ∑' k, splineTailCoefficient 8 k * m8) := by
        rw [tsum_mul_left, hf.tsum_sub hm8, rpow_eight_mul_horizonAlias_eq h hc0 hN]
        change 2 * (c N ^ 2 * ((∑' k, F N k) - ∑' k, splineTailCoefficient 8 k * m8)) = _
        ring



/-- The coefficient of the negative inverse-square correction to the
normalized tilted-spline aliasing. -/
def tiltedNextAliasCoefficient : ℝ :=
  8 / (∫ u, tiltedUnitSpline u ^ 2) * splineNumeratorMean * ∑' k : ℕ, splineTailCoefficient 10 k

theorem tiltedNextAliasCoefficient_pos : 0 < tiltedNextAliasCoefficient := by
  have hs : 0 < ∑' k : ℕ, splineTailCoefficient 10 k :=
    (summable_splineTailCoefficient (by norm_num : 1 < 10)).tsum_pos
      (fun k => by unfold splineTailCoefficient; positivity) 0 (by
        unfold splineTailCoefficient
        norm_num only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one]
        positivity)
  have hM := integral_tiltedUnitSpline_sq_pos
  have hmean := splineNumeratorMean_pos
  unfold tiltedNextAliasCoefficient
  positivity

/-- The linear-variable harmonic mass is the exponential moment of the
synthesized Weil window. -/
theorem integral_exp_mul_harmonicWindowWeight (p : ℕ) (h : ℝ → ℝ) :
    (∫ y, Real.exp y * harmonicWindowWeight p h y) =
      ∫ y, Real.exp (-((p : ℝ) * y)) * halfWeight h y ^ 2 := by
  congr 1
  funext y
  rw [harmonicWindowWeight, halfWeight, mul_pow, ← Real.exp_nat_mul,
    show (2 : ℕ) * (y / 2) = y by push_cast; ring]
  ring

/-- The leading harmonic mass is the known Jordan density of the bulk. -/
theorem leadingAliasMoment_eq (h : ℝ → ℝ) :
    2 * ∑' k : ℕ, splineTailCoefficient 8 k *
      (splineNumeratorMean * ∫ y, Real.exp y * harmonicWindowWeight 8 h y) =
      7 * (∫ u, tiltedUnitSpline u ^ 2) * tiltedJordanOne *
        ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2 := by
  unfold splineTailCoefficient
  rw [aliasLimit_eq, integral_exp_mul_harmonicWindowWeight]
  norm_num only [Nat.cast_ofNat]

/-- The next harmonic mass is the inverse-tenth-power exponential moment. -/
theorem nextAliasMoment_eq (h : ℝ → ℝ) :
    8 * ∑' k : ℕ, splineTailCoefficient 10 k *
      (splineNumeratorMean * ∫ y, Real.exp y * harmonicWindowWeight 10 h y) =
      (∫ u, tiltedUnitSpline u ^ 2) * tiltedNextAliasCoefficient *
        ∫ y, Real.exp (-(10 * y)) * halfWeight h y ^ 2 := by
  rw [tsum_mul_right, integral_exp_mul_harmonicWindowWeight]
  norm_num only [Nat.cast_ofNat]
  unfold tiltedNextAliasCoefficient
  have hM := integral_tiltedUnitSpline_sq_pos.ne'
  field_simp

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
