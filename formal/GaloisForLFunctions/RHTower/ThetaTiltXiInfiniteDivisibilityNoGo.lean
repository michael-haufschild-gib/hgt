import GaloisForLFunctions.HTGeometry.LaplaceTransformConvolution
import GaloisForLFunctions.RHTower.ThetaCarrierPolarizationFisher
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFourierLaplace
import GaloisForLFunctions.HTGeometry.ThetaHasseKMSContinuousAssembly
import GaloisForLFunctions.HTGeometry.CharacteristicFunctionPositiveDefinite
import GaloisForLFunctions.RHTower.GlobalParityWall

/-!
# Central theta probability is not infinitely divisible

The characteristic function of the central theta probability is normalized `XiC`.  If that
probability were a convolution square, endpoint exponential moments of the theta law would pass to
its probability root.  The root characteristic function would then extend analytically to the
open strip `|im z| < 1`; the identity theorem would make its square equal to normalized `XiC`
throughout that strip.  Hardy's unconditional odd-order critical-line zero contradicts the even
local order of an analytic square.

Thus probability convolution roots cannot construct the dyadic analytic Xi tower.  Any successful
transform-side construction must leave the class of probability characteristic transforms.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- Complex Fourier--Laplace transform of a proposed probability convolution root. -/
noncomputable def thetaConvRootTransform (nu : Measure ℝ) (z : ℂ) : ℂ :=
  complexMGF id nu (z * Complex.I)

/-- Finite exponential moments of a convolution square pass to its probability root. -/
theorem integrable_exp_mul_of_convPow_two_root
    {mu nu : Measure ℝ} [IsProbabilityMeasure nu]
    (hconv : mu = convPow nu 2) {t : ℝ}
    (hmu : Integrable (fun x : ℝ => Real.exp (t * x)) mu) :
    Integrable (fun x : ℝ => Real.exp (t * x)) nu := by
  have hmuFin : laplace mu (-t) ≠ ∞ := by
    rw [laplace]
    rw [lintegral_ofReal_ne_top_iff_integrable]
    · convert hmu using 1
      funext x
      congr 1
      ring
    · fun_prop
    · exact Filter.Eventually.of_forall fun x => (Real.exp_pos _).le
  rw [hconv, laplace_convPow] at hmuFin
  have hnuFin : laplace nu (-t) ≠ ∞ := by
    intro htop
    rw [htop] at hmuFin
    simp at hmuFin
  rw [laplace] at hnuFin
  rw [lintegral_ofReal_ne_top_iff_integrable] at hnuFin
  · convert hnuFin using 1
    funext x
    congr 1
    ring
  · fun_prop
  · exact Filter.Eventually.of_forall fun x => (Real.exp_pos _).le

/-- The centered affine coordinate preserves the analytic order of completed Xi. -/
theorem analyticOrderAt_XiC_ofReal (t : ℝ) :
    analyticOrderAt XiC (t : ℂ) = analyticOrderAt xi (linePt t) := by
  let g : ℂ → ℂ := fun z => 1 / 2 + z * Complex.I
  have hgAnalytic : AnalyticAt ℂ g (t : ℂ) := by
    dsimp only [g]
    fun_prop
  have hgDeriv : deriv g (t : ℂ) ≠ 0 := by
    have hg' : HasDerivAt g Complex.I (t : ℂ) := by
      dsimp only [g]
      convert (hasDerivAt_const (x := (t : ℂ)) (c := (1 / 2 : ℂ))).add
        ((hasDerivAt_id (t : ℂ)).mul_const Complex.I) using 1
      all_goals try rfl
      all_goals ring
    rw [hg'.deriv]
    exact Complex.I_ne_zero
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := xi) hgAnalytic hgDeriv
  rw [show XiC = xi ∘ g by rfl, hcomp]
  congr 1
  simp [g, linePt]

/-- `XiC` has an odd-order zero on its real axis. -/
theorem exists_odd_order_zero_XiC_on_real :
    ∃ t : ℝ, XiC (t : ℂ) = 0 ∧ Odd (analyticOrderAt XiC (t : ℂ)).toNat := by
  obtain ⟨t, _ht, hzero, hodd⟩ := exists_odd_order_line_zero_gt 0
  refine ⟨t, ?_, ?_⟩
  · simpa [XiC, linePt] using hzero
  · rwa [analyticOrderAt_XiC_ofReal]

/-- Sign convention relating the theta characteristic function to mathlib's `charFun`. -/
theorem thetaTiltCharacteristic_zero_neg_eq_charFun (t : ℝ) :
    GaloisForLFunctions.HTGeometry.thetaTiltCharacteristic 0 (-t) =
      charFun (thetaTiltProb 0) t := by
  rw [GaloisForLFunctions.HTGeometry.thetaTiltCharacteristic, charFun_apply_real]
  apply integral_congr_ae
  filter_upwards with x
  congr 1
  push_cast
  ring

theorem thetaConvRootTransform_ofReal_eq_charFun (nu : Measure ℝ) (t : ℝ) :
    thetaConvRootTransform nu (t : ℂ) = charFun nu t := by
  rw [thetaConvRootTransform]
  simpa only [Complex.ofReal_mul] using complexMGF_id_mul_I (μ := nu) t

/-- On the real axis, a probability convolution root squares to normalized `XiC`. -/
theorem thetaConvRootTransform_sq_eq_XiC_div_on_real
    {nu : Measure ℝ} [IsProbabilityMeasure nu]
    (hconv : thetaTiltProb 0 = convPow nu 2) (t : ℝ) :
    thetaConvRootTransform nu (t : ℂ) ^ 2 = XiC (t : ℂ) / XiC 0 := by
  rw [thetaConvRootTransform_ofReal_eq_charFun]
  rw [← charFun_convPow_probability nu 2 t, ← hconv,
    ← thetaTiltCharacteristic_zero_neg_eq_charFun]
  rw [GaloisForLFunctions.HTGeometry.thetaTiltCharacteristic_eq_XiC
    (a := 0) (by norm_num) (-t)]
  norm_num
  rw [XiC_even]

/-- Endpoint exponential moments make the root transform analytic on the theta strip. -/
theorem analyticOnNhd_thetaConvRootTransform
    {nu : Measure ℝ}
    (hneg : Integrable (fun x : ℝ => Real.exp ((-1 : ℝ) * x)) nu)
    (hpos : Integrable (fun x : ℝ => Real.exp ((1 : ℝ) * x)) nu) :
    AnalyticOnNhd ℂ (thetaConvRootTransform nu) thetaCuspFourierLaplaceStrip := by
  have hsub : Set.Ioo (-1 : ℝ) 1 ⊆ interior (integrableExpSet id nu) := by
    apply interior_maximal
    · intro t ht
      exact integrable_exp_mul_of_le_of_le hneg hpos ht.1.le ht.2.le
    · exact isOpen_Ioo
  intro z hz
  apply (analyticAt_complexMGF (X := id) (μ := nu) ?_).comp
  · fun_prop
  · apply hsub
    rw [thetaCuspFourierLaplaceStrip] at hz
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      Set.mem_Ioo]
    constructor <;> linarith [hz.1, hz.2]

/-- The real-axis square identity propagates to the full connected theta strip. -/
theorem thetaConvRootTransform_sq_eq_XiC_div_on_strip
    {nu : Measure ℝ} [IsProbabilityMeasure nu]
    (hneg : Integrable (fun x : ℝ => Real.exp ((-1 : ℝ) * x)) nu)
    (hpos : Integrable (fun x : ℝ => Real.exp ((1 : ℝ) * x)) nu)
    (hconv : thetaTiltProb 0 = convPow nu 2) :
    Set.EqOn (fun z => thetaConvRootTransform nu z ^ 2)
      (fun z => XiC z / XiC 0) thetaCuspFourierLaplaceStrip := by
  let F : ℂ → ℂ := fun z => thetaConvRootTransform nu z ^ 2 - XiC z / XiC 0
  have hF : AnalyticOnNhd ℂ F thetaCuspFourierLaplaceStrip :=
    (analyticOnNhd_thetaConvRootTransform hneg hpos).pow 2 |>.sub
      ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
        (XiC_differentiable.div_const (XiC 0))).mono (Set.subset_univ _))
  have hreal (t : ℝ) : F (t : ℂ) = 0 := by
    dsimp only [F]
    rw [thetaConvRootTransform_sq_eq_XiC_div_on_real hconv t]
    ring
  let u : ℕ → ℂ := fun n => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hu_tend : Filter.Tendsto u Filter.atTop (nhds 0) := by
    have hrealT : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
        Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hcomp := Complex.continuous_ofReal.continuousAt.tendsto.comp hrealT
    simpa [u, Function.comp_def] using hcomp
  have hu_ne (n : ℕ) : u n ≠ 0 := by
    dsimp only [u]
    norm_cast
    positivity
  have hu_within : Filter.Tendsto u Filter.atTop (nhdsWithin 0 ({0} : Set ℂ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hu_tend, Filter.Eventually.of_forall (fun n => by simpa using hu_ne n)⟩
  have hu_zero : ∀ n : ℕ, F (u n) = 0 := by
    intro n
    exact hreal (1 / ((n : ℝ) + 1))
  have hfreq : ∃ᶠ z in nhdsWithin 0 ({0} : Set ℂ)ᶜ, F z = 0 :=
    hu_within.frequently (Filter.Eventually.of_forall hu_zero).frequently
  have h0mem : (0 : ℂ) ∈ thetaCuspFourierLaplaceStrip := by
    simp [thetaCuspFourierLaplaceStrip]
  have hzero : Set.EqOn F 0 thetaCuspFourierLaplaceStrip :=
    hF.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_thetaCuspFourierLaplaceStrip h0mem hfreq
  intro z hz
  have := hzero hz
  dsimp only [F] at this
  exact sub_eq_zero.mp this

/-- Central theta probability has no probability convolution square root. -/
theorem not_exists_probability_convPow_two_thetaTiltProb_zero :
    ¬ ∃ nu : Measure ℝ, IsProbabilityMeasure nu ∧
      thetaTiltProb 0 = convPow nu 2 := by
  rintro ⟨nu, hprob, hconv⟩
  letI : IsProbabilityMeasure nu := hprob
  have hmuNeg :
      Integrable (fun x : ℝ => Real.exp ((-1 : ℝ) * x)) (thetaTiltProb 0) := by
    simpa only [thetaCarrier_stat, thetaCarrier_base] using
      (integrable_exp_mul_thetaCarrier (a := -1) (by norm_num))
  have hmuPos :
      Integrable (fun x : ℝ => Real.exp ((1 : ℝ) * x)) (thetaTiltProb 0) := by
    simpa only [thetaCarrier_stat, thetaCarrier_base] using
      (integrable_exp_mul_thetaCarrier (a := 1) (by norm_num))
  have hneg := integrable_exp_mul_of_convPow_two_root hconv hmuNeg
  have hpos := integrable_exp_mul_of_convPow_two_root hconv hmuPos
  have hstrip := thetaConvRootTransform_sq_eq_XiC_div_on_strip hneg hpos hconv
  obtain ⟨t, _hzero, hodd⟩ := exists_odd_order_zero_XiC_on_real
  have ht : (t : ℂ) ∈ thetaCuspFourierLaplaceStrip := by
    simp [thetaCuspFourierLaplaceStrip]
  have hevent :
      (fun z => thetaConvRootTransform nu z ^ 2) =ᶠ[nhds (t : ℂ)]
        (fun z => XiC z / XiC 0) := by
    filter_upwards [isOpen_thetaCuspFourierLaplaceStrip.mem_nhds ht] with z hz
    exact hstrip hz
  have hord :
      analyticOrderAt (fun z => thetaConvRootTransform nu z ^ 2) (t : ℂ) =
        analyticOrderAt (fun z => XiC z / XiC 0) (t : ℂ) :=
    analyticOrderAt_congr hevent
  have hevenNorm :
      Even (analyticOrderAt (fun z => XiC z / XiC 0) (t : ℂ)).toNat := by
    rw [← hord,
      show (fun z => thetaConvRootTransform nu z ^ 2) =
        thetaConvRootTransform nu ^ 2 by rfl,
      analyticOrderAt_pow
        ((analyticOnNhd_thetaConvRootTransform hneg hpos) (t : ℂ) ht)]
    rw [show (2 • analyticOrderAt (thetaConvRootTransform nu) (t : ℂ)).toNat =
        2 * (analyticOrderAt (thetaConvRootTransform nu) (t : ℂ)).toNat by
      rw [nsmul_eq_mul, ENat.toNat_mul]
      norm_num]
    exact even_two.mul_right _
  have hnormOrder :
      analyticOrderAt (fun z => XiC z / XiC 0) (t : ℂ) =
        analyticOrderAt XiC (t : ℂ) := by
    rw [show (fun z => XiC z / XiC 0) =
        XiC * (fun _ : ℂ => (XiC 0)⁻¹) by
      funext z
      simp [div_eq_mul_inv]]
    rw [analyticOrderAt_mul (XiC_analytic (t : ℂ) (Set.mem_univ _)) analyticAt_const]
    rw [analyticAt_const.analyticOrderAt_eq_zero.mpr (inv_ne_zero XiC_zero_ne), add_zero]
  rw [hnormOrder] at hevenNorm
  exact (Nat.not_even_iff_odd.mpr hodd) hevenNorm

/-- Central theta probability is not infinitely divisible. -/
theorem not_infinitelyDivisible_thetaTiltProb_zero :
    ¬ InfinitelyDivisible (thetaTiltProb 0) := by
  intro hdiv
  apply not_exists_probability_convPow_two_thetaTiltProb_zero
  exact hdiv 2 (by norm_num)

end RHTower
