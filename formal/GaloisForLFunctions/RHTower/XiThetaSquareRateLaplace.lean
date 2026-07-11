import GaloisForLFunctions.RHTower.XiThetaSquareRateCausalSource

open Complex Real Set Filter Topology MeasureTheory FourierTransform
open scoped Convolution ComplexConjugate

noncomputable section

namespace RHTower

def causalLaplaceWeighted (x : ℝ) (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  Complex.exp (-(Real.pi * x * y : ℝ)) * f y

def causalLaplaceIntegral (x : ℝ) (f : ℝ → ℂ) : ℂ :=
  ∫ y : ℝ, causalLaplaceWeighted x f y

theorem causalLaplaceWeighted_integrable
    {x : ℝ} (hx : 0 ≤ x) {f : ℝ → ℂ} (hf : Integrable f)
    (hcausal : ∀ y < 0, f y = 0) :
    Integrable (causalLaplaceWeighted x f) := by
  have hmeas : AEStronglyMeasurable (causalLaplaceWeighted x f) := by
    exact (by fun_prop : Continuous (fun y : ℝ => Complex.exp (-(Real.pi * x * y : ℝ))))
      |>.aestronglyMeasurable.mul hf.aestronglyMeasurable
  apply hf.norm.mono' hmeas
  filter_upwards [] with y
  by_cases hy : y < 0
  · rw [causalLaplaceWeighted, hcausal y hy, mul_zero]
  · rw [causalLaplaceWeighted, norm_mul, Complex.norm_exp]
    have hexp : Real.exp (-(Real.pi * x * y)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr (mul_nonneg (mul_nonneg Real.pi_pos.le hx) (le_of_not_gt hy))
    simpa using mul_le_mul_of_nonneg_right hexp (norm_nonneg (f y))

theorem causalLaplaceWeighted_convolution
    (x : ℝ) (k f : ℝ → ℂ) :
    causalLaplaceWeighted x (k ⋆[ContinuousLinearMap.mul ℂ ℂ] f) =
      causalLaplaceWeighted x k ⋆[ContinuousLinearMap.mul ℂ ℂ]
        causalLaplaceWeighted x f := by
  funext y
  rw [causalLaplaceWeighted, MeasureTheory.convolution_def,
    MeasureTheory.convolution_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  change Complex.exp (-(Real.pi * x * y : ℝ)) * (k t * f (y - t)) =
    (Complex.exp (-(Real.pi * x * t : ℝ)) * k t) *
      (Complex.exp (-(Real.pi * x * (y - t) : ℝ)) * f (y - t))
  calc
    Complex.exp (-(Real.pi * x * y : ℝ)) * (k t * f (y - t)) =
        (Complex.exp (-(Real.pi * x * t : ℝ)) *
          Complex.exp (-(Real.pi * x * (y - t) : ℝ))) *
            (k t * f (y - t)) := by
      rw [← Complex.exp_add]
      congr 2
      push_cast
      ring
    _ = (Complex.exp (-(Real.pi * x * t : ℝ)) * k t) *
        (Complex.exp (-(Real.pi * x * (y - t) : ℝ)) * f (y - t)) := by ring

theorem causalLaplaceIntegral_convolution
    {x : ℝ} (hx : 0 ≤ x) {k f : ℝ → ℂ}
    (hk : Integrable k) (hf : Integrable f)
    (hkcausal : ∀ y < 0, k y = 0) (hfcausal : ∀ y < 0, f y = 0) :
    causalLaplaceIntegral x (k ⋆[ContinuousLinearMap.mul ℂ ℂ] f) =
      causalLaplaceIntegral x k * causalLaplaceIntegral x f := by
  rw [causalLaplaceIntegral, causalLaplaceWeighted_convolution]
  rw [integral_convolution (ContinuousLinearMap.mul ℂ ℂ)
    (causalLaplaceWeighted_integrable hx hk hkcausal)
    (causalLaplaceWeighted_integrable hx hf hfcausal)]
  rfl

theorem causalLaplaceIntegral_causalFourierExponential
    {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    causalLaplaceIntegral x (causalFourierExponential a) = (a + x : ℂ)⁻¹ := by
  unfold causalLaplaceIntegral causalLaplaceWeighted causalFourierExponential
  have heq : (fun y : ℝ => Complex.exp (-(Real.pi * x * y : ℝ)) *
      (Set.Ioi (0 : ℝ)).indicator
        (fun y : ℝ => (Real.pi : ℂ) * Complex.exp (-(Real.pi * a : ℝ) * y)) y) =
      (Set.Ioi (0 : ℝ)).indicator (fun y : ℝ =>
        (Real.pi : ℂ) * Complex.exp ((-(Real.pi * (a + x) : ℝ) : ℂ) * y)) := by
    funext y
    by_cases hy : y ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      calc
        Complex.exp (-(Real.pi * x * y : ℝ)) *
            ((Real.pi : ℂ) * Complex.exp (-(Real.pi * a : ℝ) * y)) =
            (Real.pi : ℂ) * (Complex.exp (-(Real.pi * x * y : ℝ)) *
              Complex.exp (-(Real.pi * a : ℝ) * y)) := by ring
        _ = (Real.pi : ℂ) * Complex.exp
            ((-(Real.pi * x * y : ℝ) : ℂ) + (-(Real.pi * a : ℝ) : ℂ) * y) := by
          rw [Complex.exp_add]
        _ = (Real.pi : ℂ) * Complex.exp ((-(Real.pi * (a + x) : ℝ) : ℂ) * y) := by
          congr 2
          push_cast
          ring
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
  rw [heq, integral_indicator measurableSet_Ioi, integral_const_mul,
    integral_exp_mul_complex_Ioi (a := (-(Real.pi * (a + x) : ℝ) : ℂ)) (by
      norm_num
      positivity) 0]
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hax : (a : ℂ) + (x : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add, ofReal_ne_zero]
    exact ne_of_gt (add_pos_of_pos_of_nonneg ha hx)
  push_cast
  simp only [mul_zero, Complex.exp_zero]
  field_simp [hpi, hax]

theorem causalLaplaceIntegral_causalBlaschkeStep
    {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) {f : ℝ → ℂ}
    (hf : Integrable f) (hfcausal : ∀ y < 0, f y = 0) :
    causalLaplaceIntegral x (causalBlaschkeStep a f) =
      (((a : ℂ) - x) / ((a : ℂ) + x)) * causalLaplaceIntegral x f := by
  let conv : ℝ → ℂ :=
    causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f
  have hconvInt : Integrable conv :=
    (causalFourierExponential_integrable ha).integrable_convolution
      (ContinuousLinearMap.mul ℂ ℂ) hf
  have hconvCausal : ∀ y < 0, conv y = 0 := fun y hy =>
    convolution_eq_zero_of_neg (fun u hu => causalFourierExponential_eq_zero_of_neg a hu)
      hfcausal hy
  have hfW := causalLaplaceWeighted_integrable hx hf hfcausal
  have hconvW := causalLaplaceWeighted_integrable hx hconvInt hconvCausal
  unfold causalLaplaceIntegral
  have heq : causalLaplaceWeighted x (causalBlaschkeStep a f) =
      -causalLaplaceWeighted x f + (2 * a : ℂ) • causalLaplaceWeighted x conv := by
    funext y
    unfold causalLaplaceWeighted causalBlaschkeStep
    dsimp [conv]
    ring
  rw [heq]
  change (∫ y : ℝ, -causalLaplaceWeighted x f y +
    (2 * a : ℂ) * causalLaplaceWeighted x conv y) = _
  have hneg : Integrable (fun y : ℝ => -causalLaplaceWeighted x f y) := hfW.neg
  have hmul : Integrable (fun y : ℝ =>
      (2 * a : ℂ) * causalLaplaceWeighted x conv y) :=
    hconvW.const_mul (2 * a : ℂ)
  rw [integral_add hneg hmul, integral_neg, integral_const_mul]
  change -causalLaplaceIntegral x f + (2 * a : ℂ) * causalLaplaceIntegral x conv = _
  rw [show causalLaplaceIntegral x conv =
      causalLaplaceIntegral x (causalFourierExponential a) * causalLaplaceIntegral x f by
    exact causalLaplaceIntegral_convolution hx
      (causalFourierExponential_integrable ha) hf
      (fun y hy => causalFourierExponential_eq_zero_of_neg a hy) hfcausal,
    causalLaplaceIntegral_causalFourierExponential ha hx]
  have hax : (a : ℂ) + x ≠ 0 := by
    rw [← Complex.ofReal_add, ofReal_ne_zero]
    exact ne_of_gt (add_pos_of_pos_of_nonneg ha hx)
  unfold causalLaplaceIntegral
  field_simp [hax]
  ring

theorem causalLaplaceIntegral_const_mul (x : ℝ) (c : ℂ) (f : ℝ → ℂ) :
    causalLaplaceIntegral x (fun y => c * f y) = c * causalLaplaceIntegral x f := by
  unfold causalLaplaceIntegral causalLaplaceWeighted
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

def thetaSquareFiniteReaderValue (n N : ℕ) (x : ℝ) : ℂ :=
  -(thetaSquareBlaschkeNodeSlope n)⁻¹ *
    (((n : ℂ) ^ 2 + x)⁻¹) *
    thetaSquareFiniteSkippedProduct n N x

theorem causalLaplaceIntegral_thetaSquareFiniteCausalSource
    {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    ∀ N, causalLaplaceIntegral x (thetaSquareFiniteCausalSource n N) =
      thetaSquareFiniteReaderValue n N x := by
  intro N
  induction N with
  | zero =>
      rw [thetaSquareFiniteCausalSource, thetaSquareFiniteReaderValue,
        thetaSquareFiniteSkippedProduct, Finset.prod_range_zero, mul_one]
      rw [causalLaplaceIntegral_const_mul,
        causalLaplaceIntegral_causalFourierExponential
          (sq_pos_of_pos (by positivity : (0 : ℝ) < n)) hx]
      push_cast
      rfl
  | succ N ih =>
      rw [thetaSquareFiniteCausalSource]
      split_ifs with hN
      · rw [ih, thetaSquareFiniteReaderValue, thetaSquareFiniteReaderValue]
        simp only [thetaSquareFiniteSkippedProduct]
        rw [Finset.prod_range_succ]
        simp [hN]
      · rw [causalLaplaceIntegral_causalBlaschkeStep (sq_pos_of_pos (by positivity)) hx
          (thetaSquareFiniteCausalSource_integrable hn N)
          (thetaSquareFiniteCausalSource_eq_zero_of_neg N), ih]
        rw [thetaSquareFiniteReaderValue, thetaSquareFiniteReaderValue]
        simp only [thetaSquareFiniteSkippedProduct]
        rw [Finset.prod_range_succ]
        simp only [hN, ↓reduceIte]
        push_cast
        ring

def causalLaplaceWeightFun (x : ℝ) (y : ℝ) : ℂ :=
  (Real.pi : ℂ)⁻¹ * causalFourierExponential x y

theorem causalLaplaceWeightFun_memLp_two {x : ℝ} (hx : 0 < x) :
    MemLp (causalLaplaceWeightFun x) 2 volume := by
  unfold causalLaplaceWeightFun
  apply memLp_two_of_integrable_of_norm_le
    ((causalFourierExponential_integrable hx).const_mul (Real.pi : ℂ)⁻¹)
  intro y
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_causalFourierExponential_le hx.le y) (norm_nonneg _)

def causalLaplaceWeightL2 (x : ℝ) (hx : 0 < x) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (causalLaplaceWeightFun_memLp_two hx).toLp (causalLaplaceWeightFun x)

theorem causalLaplaceWeightL2_ae (x : ℝ) (hx : 0 < x) :
    (fun y : ℝ => causalLaplaceWeightL2 x hx y) =ᵐ[volume]
      causalLaplaceWeightFun x :=
  MemLp.coeFn_toLp (causalLaplaceWeightFun_memLp_two hx)

def causalLaplacePairing (x : ℝ) (hx : 0 < x)
    (g : Lp ℂ 2 (volume : Measure ℝ)) : ℂ :=
  inner ℂ (causalLaplaceWeightL2 x hx) g

lemma causalLaplaceWeightFun_of_pos {x y : ℝ} (hy : 0 < y) :
    causalLaplaceWeightFun x y = Complex.exp (-(Real.pi * x * y : ℝ)) := by
  unfold causalLaplaceWeightFun
  change (Real.pi : ℂ)⁻¹ * (Set.Ioi (0 : ℝ)).indicator
    (fun u : ℝ => (Real.pi : ℂ) * Complex.exp (-(Real.pi * x : ℝ) * u)) y = _
  rw [Set.indicator_of_mem (show y ∈ Set.Ioi (0 : ℝ) from hy)]
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi]
  congr 1
  push_cast
  ring

theorem causalLaplacePairing_eq_integral_of_lowerSupport
    {x : ℝ} (hx : 0 < x) (g : Lp ℂ 2 (volume : Measure ℝ))
    (hsupp : HasAELowerSupport (fun y : ℝ => g y) 0) :
    causalLaplacePairing x hx g = causalLaplaceIntegral x (fun y : ℝ => g y) := by
  rw [causalLaplacePairing, L2.inner_def, causalLaplaceIntegral]
  apply integral_congr_ae
  have hy0 : ∀ᵐ y : ℝ, y ≠ 0 := by simp [ae_iff, measure_singleton]
  filter_upwards [causalLaplaceWeightL2_ae x hx, hsupp, hy0] with y hw hs hy0
  rw [hw]
  by_cases hy : y < 0
  · have hgy := hs hy
    unfold causalLaplaceWeighted
    rw [hgy]
    simp [RCLike.inner_apply]
    exact hgy
  · have hypos : 0 < y := lt_of_le_of_ne (le_of_not_gt hy) (Ne.symm hy0)
    rw [causalLaplaceWeightFun_of_pos hypos]
    unfold causalLaplaceWeighted
    rw [RCLike.inner_apply, ← Complex.exp_conj]
    simp
    ring

theorem causalLaplaceIntegral_congr_ae (x : ℝ) {f g : ℝ → ℂ}
    (hfg : f =ᵐ[volume] g) :
    causalLaplaceIntegral x f = causalLaplaceIntegral x g := by
  unfold causalLaplaceIntegral causalLaplaceWeighted
  apply integral_congr_ae
  filter_upwards [hfg] with y hy
  rw [hy]

theorem causalLaplacePairing_thetaSquareFiniteCausalSourceL2
    {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) (N : ℕ) :
    causalLaplacePairing x hx (thetaSquareFiniteCausalSourceL2 n N hn) =
      thetaSquareFiniteReaderValue n N x := by
  rw [causalLaplacePairing_eq_integral_of_lowerSupport hx _
    (thetaSquareFiniteCausalSourceL2_hasAELowerSupport hn N)]
  rw [causalLaplaceIntegral_congr_ae x (thetaSquareFiniteCausalSourceL2_ae n N hn)]
  exact causalLaplaceIntegral_thetaSquareFiniteCausalSource hn hx.le N

theorem tendsto_causalLaplacePairing_thetaSquareFiniteCausalSourceL2
    {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N => causalLaplacePairing x hx
      (thetaSquareFiniteCausalSourceL2 n N hn)) atTop
      (𝓝 (causalLaplacePairing x hx (thetaHeatRateSourceReaderL2 n hn))) := by
  have hcont : Continuous (fun g : Lp ℂ 2 (volume : Measure ℝ) =>
      causalLaplacePairing x hx g) := by
    unfold causalLaplacePairing
    fun_prop
  exact hcont.continuousAt.tendsto.comp (tendsto_thetaSquareFiniteCausalSourceL2 hn)

theorem thetaSquareFiniteReaderValue_eq_blaschkeFinite
    {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) {x : ℝ} (hx : 0 < x)
    (hxnode : (x : ℂ) ≠ thetaSquare n) :
    thetaSquareFiniteReaderValue n N x =
      (thetaSquareBlaschkeNodeSlope n)⁻¹ * thetaSquareBlaschkeFinite N x /
        ((x : ℂ) - thetaSquare n) := by
  let z : ℂ := x
  have htheta : thetaSquare n = (n : ℂ) ^ 2 := by simp [thetaSquare]
  have hminus : z - (n : ℂ) ^ 2 ≠ 0 := by
    rw [← htheta, sub_ne_zero]
    exact hxnode
  have hplus : (n : ℂ) ^ 2 + z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp [z] at hre
    norm_num [pow_two] at hre
    nlinarith [hx]
  let S : ℂ := (thetaSquareBlaschkeNodeSlope n)⁻¹
  let P : ℂ := thetaSquareFiniteSkippedProduct n N z
  have hsplit := thetaSquareBlaschkeFinite_split_selected hn hnN z
  calc
    thetaSquareFiniteReaderValue n N x =
        (-S * ((n : ℂ) ^ 2 + z)⁻¹) * P := by rfl
    _ = S * ((((n : ℂ) ^ 2 - z) / ((n : ℂ) ^ 2 + z)) * P) /
        (z - (n : ℂ) ^ 2) := cancel_selected_blaschke_factor hminus hplus
    _ = S * thetaSquareBlaschkeFinite N z / (z - (n : ℂ) ^ 2) := by rw [hsplit]
    _ = (thetaSquareBlaschkeNodeSlope n)⁻¹ * thetaSquareBlaschkeFinite N z /
        (z - thetaSquare n) := by rw [htheta]

theorem tendsto_thetaSquareFiniteReaderValue
    {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x)
    (hxnode : (x : ℂ) ≠ thetaSquare n) :
    Tendsto (fun N => thetaSquareFiniteReaderValue n N x) atTop
      (𝓝 (thetaSquareBlaschkeReaderSymbol n x)) := by
  let z : ℂ := x
  have hznode : z - thetaSquare n ≠ 0 := sub_ne_zero.mpr hxnode
  have hB := tendsto_thetaSquareBlaschkeFinite (z := z) (by simpa [z] using hx)
  have hlim := (hB.const_mul (thetaSquareBlaschkeNodeSlope n)⁻¹).div_const
    (z - thetaSquare n)
  have hevent : (fun N =>
      (thetaSquareBlaschkeNodeSlope n)⁻¹ * thetaSquareBlaschkeFinite N z /
        (z - thetaSquare n)) =ᶠ[atTop]
      (fun N => thetaSquareFiniteReaderValue n N x) := by
    filter_upwards [eventually_ge_atTop n] with N hN
    exact (thetaSquareFiniteReaderValue_eq_blaschkeFinite hn hN hx hxnode).symm
  have hreader := hlim.congr' hevent
  have hvalue :
      (thetaSquareBlaschkeNodeSlope n)⁻¹ * thetaSquareBlaschkeSymbol z /
          (z - thetaSquare n) =
        thetaSquareBlaschkeReaderSymbol n x := by
    dsimp [z]
    rw [thetaSquareBlaschkeReaderSymbol,
      dslope_of_ne _ hxnode, slope_def_field,
      thetaSquareBlaschkeSymbol_zero, sub_zero]
    ring
  rw [hvalue] at hreader
  exact hreader

theorem causalLaplacePairing_thetaHeatRateSourceReaderL2_of_ne_node
    {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x)
    (hxnode : (x : ℂ) ≠ thetaSquare n) :
    causalLaplacePairing x hx (thetaHeatRateSourceReaderL2 n hn) =
      thetaSquareBlaschkeReaderSymbol n x := by
  have hleft := tendsto_causalLaplacePairing_thetaSquareFiniteCausalSourceL2 hn hx
  have hright := tendsto_thetaSquareFiniteReaderValue hn hx hxnode
  have heq : (fun N => causalLaplacePairing x hx
      (thetaSquareFiniteCausalSourceL2 n N hn)) =
      fun N => thetaSquareFiniteReaderValue n N x := by
    funext N
    exact causalLaplacePairing_thetaSquareFiniteCausalSourceL2 hn hx N
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

theorem causalLaplaceWeightL2_hasAELowerSupport
    {x : ℝ} (hx : 0 < x) :
    HasAELowerSupport (fun y : ℝ => causalLaplaceWeightL2 x hx y) 0 := by
  filter_upwards [causalLaplaceWeightL2_ae x hx] with y hy
  intro hyneg
  rw [hy]
  unfold causalLaplaceWeightFun causalFourierExponential
  rw [Set.indicator_of_notMem (by
    simpa only [Set.mem_Ioi, not_lt] using (le_of_lt hyneg)), mul_zero]

theorem inner_causalLaplaceWeightL2
    {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    inner ℂ (causalLaplaceWeightL2 x hx) (causalLaplaceWeightL2 a ha) =
      (Real.pi : ℂ)⁻¹ * ((a : ℂ) + x)⁻¹ := by
  change causalLaplacePairing x hx (causalLaplaceWeightL2 a ha) = _
  rw [causalLaplacePairing_eq_integral_of_lowerSupport hx _
    (causalLaplaceWeightL2_hasAELowerSupport ha)]
  rw [causalLaplaceIntegral_congr_ae x (causalLaplaceWeightL2_ae a ha)]
  change causalLaplaceIntegral x
      (fun y => (Real.pi : ℂ)⁻¹ * causalFourierExponential a y) = _
  rw [causalLaplaceIntegral_const_mul,
    causalLaplaceIntegral_causalFourierExponential ha hx.le]

theorem norm_causalLaplaceWeightL2_sub_sq
    {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    ‖causalLaplaceWeightL2 x hx - causalLaplaceWeightL2 a ha‖ ^ 2 =
      (2 * Real.pi * x)⁻¹ - 2 * (Real.pi * (x + a))⁻¹ +
        (2 * Real.pi * a)⁻¹ := by
  rw [norm_sub_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ),
    ← inner_self_eq_norm_sq (𝕜 := ℂ),
    inner_causalLaplaceWeightL2 hx hx,
    inner_causalLaplaceWeightL2 hx ha,
    inner_causalLaplaceWeightL2 ha ha]
  norm_num [Complex.inv_re, Complex.normSq_apply]
  field_simp
  ring

def causalLaplaceWeightPositive (x : Set.Ioi (0 : ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  causalLaplaceWeightL2 x.1 x.2

theorem continuous_causalLaplaceWeightPositive :
    Continuous causalLaplaceWeightPositive := by
  rw [continuous_iff_continuousAt]
  intro a
  rw [ContinuousAt]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  let R : Set.Ioi (0 : ℝ) → ℝ := fun x =>
    (2 * Real.pi * x.1)⁻¹ - 2 * (Real.pi * (x.1 + a.1))⁻¹ +
      (2 * Real.pi * a.1)⁻¹
  have hRcont : ContinuousAt R a := by
    dsimp [R]
    have hval : ContinuousAt (fun x : Set.Ioi (0 : ℝ) => x.1) a :=
      continuous_subtype_val.continuousAt
    apply ContinuousAt.add
    · apply ContinuousAt.sub
      · exact ((continuousAt_const.mul continuousAt_const).mul hval).inv₀
          (ne_of_gt (mul_pos (mul_pos (by norm_num) Real.pi_pos) a.2))
      · exact continuousAt_const.mul
          ((continuousAt_const.mul (hval.add continuousAt_const)).inv₀
            (ne_of_gt (mul_pos Real.pi_pos (add_pos a.2 a.2))))
    · exact continuousAt_const
  have hRzero : R a = 0 := by
    dsimp [R]
    field_simp
    ring
  have hR : Tendsto R (𝓝 a) (𝓝 0) := by
    change Tendsto R (𝓝 a) (𝓝 (R a)) at hRcont
    rw [hRzero] at hRcont
    exact hRcont
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hR
  have heq : (fun x : Set.Ioi (0 : ℝ) =>
      ‖causalLaplaceWeightPositive x - causalLaplaceWeightPositive a‖) =
      fun x => Real.sqrt (R x) := by
    funext x
    rw [← Real.sqrt_sq (norm_nonneg _)]
    congr 1
    exact norm_causalLaplaceWeightL2_sub_sq x.2 a.2
  rw [heq]
  simpa using hsqrt

def positiveApproach (a : Set.Ioi (0 : ℝ)) (N : ℕ) : Set.Ioi (0 : ℝ) :=
  ⟨a.1 + 1 / ((N : ℝ) + 1),
    by
      change (0 : ℝ) < a.1 + 1 / ((N : ℝ) + 1)
      exact add_pos a.2 (one_div_pos.mpr (by positivity))⟩

theorem tendsto_positiveApproach (a : Set.Ioi (0 : ℝ)) :
    Tendsto (positiveApproach a) atTop (𝓝 a) := by
  rw [tendsto_subtype_rng]
  unfold positiveApproach
  change Tendsto (fun N : ℕ => a.1 + 1 / ((N : ℝ) + 1)) atTop (𝓝 a.1)
  simpa using tendsto_const_nhds.add
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem causalLaplacePairing_thetaHeatRateSourceReaderL2_self
    {n : ℕ} (hn : 1 ≤ n) :
    causalLaplacePairing ((n : ℝ) ^ 2) (sq_pos_of_pos (by positivity))
        (thetaHeatRateSourceReaderL2 n hn) = 1 := by
  let a : Set.Ioi (0 : ℝ) := ⟨(n : ℝ) ^ 2, by
    change (0 : ℝ) < (n : ℝ) ^ 2
    positivity⟩
  let q : ℕ → Set.Ioi (0 : ℝ) := positiveApproach a
  let g := thetaHeatRateSourceReaderL2 n hn
  have hq : Tendsto q atTop (𝓝 a) := tendsto_positiveApproach a
  have hpairCont : Continuous (fun x : Set.Ioi (0 : ℝ) =>
      inner ℂ (causalLaplaceWeightPositive x) g) :=
    continuous_causalLaplaceWeightPositive.inner continuous_const
  have hleft := hpairCont.continuousAt.tendsto.comp hq
  change Tendsto (fun N => causalLaplacePairing (q N).1 (q N).2 g) atTop
    (𝓝 (causalLaplacePairing a.1 a.2 g)) at hleft
  have hqComplex : Tendsto (fun N => ((q N).1 : ℂ)) atTop
      (𝓝 (thetaSquare n)) := by
    have hreal := (tendsto_subtype_rng.mp hq)
    have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
    simpa [a, thetaSquare] using hcomplex
  have hnodeMem : thetaSquare n ∈ {z : ℂ | 0 < z.re} := by
    norm_num [thetaSquare, pow_two, Complex.mul_re]
    omega
  have hopen : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const continuous_re
  have hreaderAt : ContinuousAt (thetaSquareBlaschkeReaderSymbol n)
      (thetaSquare n) :=
    ((thetaSquareBlaschkeReaderSymbol_differentiableOn_rightHalfPlane hn)
      (x := thetaSquare n) hnodeMem).differentiableAt (hopen.mem_nhds hnodeMem) |>.continuousAt
  have hright := hreaderAt.tendsto.comp hqComplex
  have heq : (fun N => causalLaplacePairing (q N).1 (q N).2 g) =
      fun N => thetaSquareBlaschkeReaderSymbol n (q N).1 := by
    funext N
    apply causalLaplacePairing_thetaHeatRateSourceReaderL2_of_ne_node hn (q N).2
    dsimp [q, positiveApproach, a]
    rw [thetaSquare]
    push_cast
    norm_num
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
    have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    linarith
  rw [heq] at hleft
  have hvalue := tendsto_nhds_unique hleft hright
  change causalLaplacePairing ((n : ℝ) ^ 2) _
      (thetaHeatRateSourceReaderL2 n hn) = _ at hvalue
  rw [thetaSquareBlaschkeReaderSymbol_self hn] at hvalue
  exact hvalue

theorem causalLaplacePairing_thetaHeatRateSourceReaderL2_other
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ≠ n) :
    causalLaplacePairing ((m : ℝ) ^ 2) (sq_pos_of_pos (by positivity))
        (thetaHeatRateSourceReaderL2 n hn) = 0 := by
  have hxnode : ((((m : ℝ) ^ 2 : ℝ) : ℂ)) ≠ thetaSquare n := by
    simpa [thetaSquare] using (thetaSquare_ne_of_ne hmn)
  rw [causalLaplacePairing_thetaHeatRateSourceReaderL2_of_ne_node hn
    (sq_pos_of_pos (by positivity)) hxnode]
  simpa [thetaSquare] using (thetaSquareBlaschkeReaderSymbol_other hmn)

theorem causalLaplacePairing_thetaHeatRateSourceReaderL2_kronecker
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    causalLaplacePairing ((m : ℝ) ^ 2) (sq_pos_of_pos (by positivity))
        (thetaHeatRateSourceReaderL2 n hn) = if m = n then 1 else 0 := by
  by_cases hmn : m = n
  · subst m
    simpa using causalLaplacePairing_thetaHeatRateSourceReaderL2_self hn
  · rw [if_neg hmn]
    exact causalLaplacePairing_thetaHeatRateSourceReaderL2_other hn hm hmn

/-- The canonical causal reader has exact Laplace samples at the physical theta heat rates
`π m²`: the parameter `x = m²` in `causalLaplaceIntegral` supplies the weight `exp (-π m² y)`. -/
theorem causalLaplaceIntegral_thetaHeatRateSourceReaderL2_kronecker
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    causalLaplaceIntegral ((m : ℝ) ^ 2)
        (fun y : ℝ => thetaHeatRateSourceReaderL2 n hn y) =
      if m = n then 1 else 0 := by
  rw [← causalLaplacePairing_eq_integral_of_lowerSupport
    (sq_pos_of_pos (by positivity)) _
    (thetaHeatRateSourceReaderL2_hasAELowerSupport hn)]
  exact causalLaplacePairing_thetaHeatRateSourceReaderL2_kronecker hn hm

end RHTower
