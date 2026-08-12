import GaloisForLFunctions.RHTower.SuzukiHlogHilbertFormDomain
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry
import GaloisForLFunctions.RHTower.SoninDilationContinuity
import GaloisForLFunctions.HTGeometry.WeightedDensityL2
import GaloisForLFunctions.HTGeometry.L2MultiplierContinuity

/-!
# Strong inward dilation in Suzuki's logarithmic form norm

Connes--Consani's Laurent-polynomial form-core proof compresses an arbitrary aperture vector
inward before mollification. Ordinary `L²` dilation continuity is insufficient: convergence is
required in the weighted Fourier norm `∫ (1 + log⁺|ξ|) |f̂(ξ)|² dξ`.

This module proves the missing weighted theorem unconditionally. Multiplication by the square
root of the logarithmic density identifies weighted `L²` with ordinary `L²`. Under that unitary,
frequency dilation is ordinary normalized dilation followed by a density-ratio multiplier. The
ratio is uniformly bounded near scale one and converges pointwise to one, so strong multiplier
continuity plus strong `L²` dilation continuity gives the result. An explicit representative
formula then recovers the source dilation, needed for aperture-support compression.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

theorem suzukiLogWeight_eq_one_add_posLog (x : ℝ) :
    suzukiLogWeight x = 1 + Real.posLog x := by
  simp [suzukiLogWeight, Real.posLog, max_comm, Real.log_abs]

theorem posLog_le_one_of_pos_le_two {r : ℝ} (hr0 : 0 < r) (hr2 : r ≤ 2) :
    Real.posLog r ≤ 1 := by
  rw [Real.posLog_apply, max_le_iff]
  exact ⟨zero_le_one, by
    have hlog := Real.log_le_sub_one_of_pos hr0
    linarith⟩

theorem suzukiLogWeight_scale_le_two {r : ℝ} (hr0 : 0 < r) (hr2 : r ≤ 2) (x : ℝ) :
    suzukiLogWeight (r * x) ≤ 2 * suzukiLogWeight x := by
  rw [suzukiLogWeight_eq_one_add_posLog, suzukiLogWeight_eq_one_add_posLog]
  have hmul := Real.posLog_mul (x := r) (y := x)
  have hrlog := posLog_le_one_of_pos_le_two hr0 hr2
  have hx := Real.posLog_nonneg (x := x)
  linarith

def suzukiHlogDilatedFn (r : ℝ) (f : SuzukiHlogFourierL2) : ℝ → ℂ :=
  fun x => (Real.sqrt r⁻¹ : ℂ) * f (r⁻¹ * x)

theorem suzukiHlogDilatedFn_aestronglyMeasurable
    {r : ℝ} (hr : 0 < r) (f : SuzukiHlogFourierL2) :
    AEStronglyMeasurable (suzukiHlogDilatedFn r f) suzukiHlogMeasure := by
  have hfvol : AEStronglyMeasurable (f : ℝ → ℂ) volume :=
    (Lp.aestronglyMeasurable f).mono_measure volume_le_suzukiHlogMeasure
  have hcomp : AEStronglyMeasurable (fun x : ℝ => f (r⁻¹ * x)) volume := by
    exact hfvol.comp_quasiMeasurePreserving
      (realMul_quasiMeasurePreserving r⁻¹ (inv_ne_zero hr.ne'))
  exact AEStronglyMeasurable.mono_ac
    suzukiHlogMeasure_absolutelyContinuous_volume
    (hcomp.const_mul (Real.sqrt r⁻¹ : ℂ))

theorem memLp_suzukiHlogDilatedFn
    {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) (f : SuzukiHlogFourierL2) :
    MemLp (suzukiHlogDilatedFn r f) 2 suzukiHlogMeasure := by
  apply (memLp_two_iff_integrable_sq_norm
    (suzukiHlogDilatedFn_aestronglyMeasurable hr f)).2
  unfold suzukiHlogMeasure
  rw [integrable_withDensity_iff_integrable_smul measurable_suzukiLogWeightNNReal]
  have hfint : Integrable (fun x : ℝ => ‖(f : ℝ → ℂ) x‖ ^ 2)
      suzukiHlogMeasure :=
    (MeasureTheory.Lp.memLp f).integrable_norm_pow (by norm_num)
  have hbase : Integrable
      (fun x : ℝ => suzukiLogWeight x * ‖(f : ℝ → ℂ) x‖ ^ 2) volume := by
    unfold suzukiHlogMeasure at hfint
    rw [integrable_withDensity_iff_integrable_smul
      measurable_suzukiLogWeightNNReal] at hfint
    refine hfint.congr ?_
    filter_upwards with x
    rw [NNReal.smul_def, smul_eq_mul, coe_suzukiLogWeightNNReal]
    rfl
  have hmajor : Integrable (fun x : ℝ =>
      (2 * r⁻¹) * (suzukiLogWeight (r⁻¹ * x) * ‖(f : ℝ → ℂ) (r⁻¹ * x)‖ ^ 2)) :=
    (hbase.comp_mul_left' (inv_ne_zero hr.ne')).const_mul (2 * r⁻¹)
  refine hmajor.mono' ?_ ?_
  · exact measurable_suzukiLogWeightNNReal.aestronglyMeasurable.smul
      (((suzukiHlogDilatedFn_aestronglyMeasurable hr f).mono_measure
        volume_le_suzukiHlogMeasure).norm.pow 2)
  · filter_upwards with x
    rw [NNReal.smul_def, smul_eq_mul, coe_suzukiLogWeightNNReal]
    have hw : suzukiLogWeight x ≤ 2 * suzukiLogWeight (r⁻¹ * x) := by
      have := suzukiLogWeight_scale_le_two hr hr2 (r⁻¹ * x)
      convert this using 1
      field_simp [hr.ne']
    have hinv : 0 ≤ r⁻¹ := (inv_pos.mpr hr).le
    have hn : 0 ≤ ‖(f : ℝ → ℂ) (r⁻¹ * x)‖ ^ 2 := sq_nonneg _
    have hsqrt : ‖(Real.sqrt r⁻¹ : ℂ)‖ ^ 2 = r⁻¹ := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hinv]
    change ‖suzukiLogWeight x * ‖suzukiHlogDilatedFn r f x‖ ^ 2‖ ≤
      (2 * r⁻¹) * (suzukiLogWeight (r⁻¹ * x) * ‖f (r⁻¹ * x)‖ ^ 2)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (suzukiLogWeight_nonneg x) (sq_nonneg _)),
      ]
    rw [suzukiHlogDilatedFn, norm_mul, mul_pow, hsqrt]
    exact (mul_le_mul_of_nonneg_right hw (mul_nonneg hinv hn)).trans_eq (by ring)

theorem suzukiLogWeight_pos (x : ℝ) : 0 < suzukiLogWeight x :=
  lt_of_lt_of_le zero_lt_one (one_le_suzukiLogWeight x)

theorem continuous_suzukiLogWeight : Continuous suzukiLogWeight := by
  rw [show suzukiLogWeight = fun x => 1 + Real.posLog x by
    funext x; exact suzukiLogWeight_eq_one_add_posLog x]
  fun_prop

def suzukiHlogDensityUnitary : SuzukiHlogFourierL2 ≃ₗᵢ[ℂ] SoninL2 :=
  weightedDensityUnitary suzukiLogWeight measurable_suzukiLogWeight suzukiLogWeight_pos

def suzukiHlogInwardScale (n : ℕ) : ℝ := 1 + ((n + 1 : ℕ) : ℝ)⁻¹

theorem suzukiHlogInwardScale_pos (n : ℕ) : 0 < suzukiHlogInwardScale n := by
  unfold suzukiHlogInwardScale
  positivity

theorem suzukiHlogInwardScale_le_two (n : ℕ) : suzukiHlogInwardScale n ≤ 2 := by
  unfold suzukiHlogInwardScale
  have h : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_add_left 1 n
  have hinv : (((n + 1 : ℕ) : ℝ))⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).2 h
  linarith

theorem tendsto_suzukiHlogInwardScale : Tendsto suzukiHlogInwardScale atTop (nhds 1) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
  norm_num at h
  convert h using 1
  funext n
  simp [suzukiHlogInwardScale, Nat.cast_add, Nat.cast_one]

theorem tendsto_suzukiHlogInwardScale_inv : Tendsto (fun n => (suzukiHlogInwardScale n)⁻¹) atTop (nhds 1) := by
  simpa using tendsto_suzukiHlogInwardScale.inv₀ (by norm_num)

def suzukiHlogDilationDensityRatio (n : ℕ) (x : ℝ) : ℂ :=
  (Real.sqrt (suzukiLogWeight x /
    suzukiLogWeight ((suzukiHlogInwardScale n)⁻¹ * x)) : ℝ)

theorem suzukiHlogDilationDensityRatio_measurable (n : ℕ) : Measurable (suzukiHlogDilationDensityRatio n) := by
  unfold suzukiHlogDilationDensityRatio
  exact Complex.measurable_ofReal.comp
    (Real.continuous_sqrt.measurable.comp (measurable_suzukiLogWeight.div
      (measurable_suzukiLogWeight.comp (measurable_const.mul measurable_id))))

theorem suzukiHlogDilationDensityRatio_bound (n : ℕ) (x : ℝ) :
    ‖suzukiHlogDilationDensityRatio n x‖ ≤ Real.sqrt 2 := by
  have hw := suzukiLogWeight_scale_le_two (suzukiHlogInwardScale_pos n) (suzukiHlogInwardScale_le_two n)
    ((suzukiHlogInwardScale n)⁻¹ * x)
  have harg : suzukiHlogInwardScale n * ((suzukiHlogInwardScale n)⁻¹ * x) = x := by
    field_simp [(suzukiHlogInwardScale_pos n).ne']
  rw [harg] at hw
  have hden := suzukiLogWeight_pos ((suzukiHlogInwardScale n)⁻¹ * x)
  have hdiv : suzukiLogWeight x /
      suzukiLogWeight ((suzukiHlogInwardScale n)⁻¹ * x) ≤ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hdiv0 : 0 ≤ suzukiLogWeight x /
      suzukiLogWeight ((suzukiHlogInwardScale n)⁻¹ * x) := div_nonneg
        (suzukiLogWeight_nonneg x) hden.le
  rw [suzukiHlogDilationDensityRatio, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt hdiv

theorem suzukiHlogDilationDensityRatio_tendsto_one (x : ℝ) :
    Tendsto (fun n => suzukiHlogDilationDensityRatio n x) atTop (nhds 1) := by
  have harg : Tendsto (fun n => (suzukiHlogInwardScale n)⁻¹ * x) atTop (nhds x) := by
    simpa using tendsto_suzukiHlogInwardScale_inv.mul_const x
  have hw : Tendsto (fun n => suzukiLogWeight ((suzukiHlogInwardScale n)⁻¹ * x))
      atTop (nhds (suzukiLogWeight x)) :=
    continuous_suzukiLogWeight.continuousAt.tendsto.comp harg
  have hratio : Tendsto (fun n => suzukiLogWeight x /
      suzukiLogWeight ((suzukiHlogInwardScale n)⁻¹ * x)) atTop (nhds 1) := by
    have hnum : Tendsto (fun _ : ℕ => suzukiLogWeight x) atTop
        (nhds (suzukiLogWeight x)) := tendsto_const_nhds
    have h := hnum.div hw (suzukiLogWeight_pos x).ne'
    have heq : ((fun _ : ℕ => suzukiLogWeight x) /
        fun n => suzukiLogWeight ((suzukiHlogInwardScale n)⁻¹ * x)) =
        fun n => suzukiLogWeight x /
          suzukiLogWeight ((suzukiHlogInwardScale n)⁻¹ * x) := by
      funext n
      rfl
    rw [heq] at h
    simpa only [div_self (suzukiLogWeight_pos x).ne'] using h
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hratio
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hsqrt
  change Tendsto (fun n => ((Real.sqrt (suzukiLogWeight x /
      suzukiLogWeight ((suzukiHlogInwardScale n)⁻¹ * x)) : ℝ) : ℂ)) atTop
    (nhds ((Real.sqrt (1 : ℝ) : ℝ) : ℂ)) at hcomplex
  simpa [suzukiHlogDilationDensityRatio] using hcomplex

def suzukiHlogDilationDensityRatioMul (n : ℕ) : SoninL2 →L[ℂ] SoninL2 :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
    (suzukiHlogDilationDensityRatio_measurable n) (Real.sqrt_nonneg 2) (suzukiHlogDilationDensityRatio_bound n)

theorem suzukiHlogDilationDensityRatioMul_fixed_tendsto (f : SoninL2) :
    Tendsto (fun n => suzukiHlogDilationDensityRatioMul n f) atTop (nhds f) := by
  have h := tendsto_lpBoundedMulCLM_apply
    (μ := (volume : Measure ℝ))
    (fun n => suzukiHlogDilationDensityRatio_measurable n) measurable_const (Real.sqrt_nonneg 2)
    (fun n x => suzukiHlogDilationDensityRatio_bound n x)
    (fun x => by simpa using (Real.one_le_sqrt.mpr (by norm_num : (1:ℝ) ≤ 2)))
    suzukiHlogDilationDensityRatio_tendsto_one f
  have hone : lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
      (measurable_const : Measurable (fun _ : ℝ => (1 : ℂ)))
      (Real.sqrt_nonneg 2)
      (fun _ => by simpa using (Real.one_le_sqrt.mpr (by norm_num : (1:ℝ) ≤ 2))) =
      ContinuousLinearMap.id ℂ SoninL2 := by
    apply lpBoundedMulCLM_eq_id
    filter_upwards with x
    rfl
  rw [hone] at h
  change Tendsto (fun n => suzukiHlogDilationDensityRatioMul n f) atTop (nhds f)
  exact h

theorem tendsto_plainDilate_suzukiHlogInwardScale (f : SoninL2) :
    Tendsto (fun n => rayDilate (suzukiHlogInwardScale n)⁻¹ f) atTop (nhds f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact (tendsto_norm_rayDilate_sub_self f).comp tendsto_suzukiHlogInwardScale_inv

theorem suzukiHlogDilationDensityRatioMul_dilate_tendsto (f : SoninL2) :
    Tendsto (fun n => suzukiHlogDilationDensityRatioMul n (rayDilate (suzukiHlogInwardScale n)⁻¹ f))
      atTop (nhds f) := by
  have hconst : Tendsto (fun _ : ℕ => f) atTop (nhds f) := tendsto_const_nhds
  have hD' := (tendsto_plainDilate_suzukiHlogInwardScale f).sub hconst
  have hD : Tendsto (fun n => rayDilate (suzukiHlogInwardScale n)⁻¹ f - f)
      atTop (nhds 0) := by simpa using hD'
  have hfirst : Tendsto (fun n => suzukiHlogDilationDensityRatioMul n
      (rayDilate (suzukiHlogInwardScale n)⁻¹ f - f)) atTop (nhds 0) := by
    apply squeeze_zero_norm
    · intro n
      exact le_trans ((suzukiHlogDilationDensityRatioMul n).le_opNorm _) (mul_le_mul_of_nonneg_right
        (norm_lpBoundedMulCLM_le (p := 2) (μ := (volume : Measure ℝ))
          (suzukiHlogDilationDensityRatio_measurable n) (Real.sqrt_nonneg 2) (suzukiHlogDilationDensityRatio_bound n))
        (norm_nonneg _))
    · have hc : Tendsto (fun _ : ℕ => Real.sqrt 2) atTop
          (nhds (Real.sqrt 2)) := tendsto_const_nhds
      simpa using hc.mul hD.norm
  have hdecomp : (fun n => suzukiHlogDilationDensityRatioMul n (rayDilate (suzukiHlogInwardScale n)⁻¹ f)) =
      fun n => suzukiHlogDilationDensityRatioMul n (rayDilate (suzukiHlogInwardScale n)⁻¹ f - f) +
        suzukiHlogDilationDensityRatioMul n f := by
    funext n
    rw [map_sub, sub_add_cancel]
  rw [hdecomp]
  simpa only [zero_add] using hfirst.add (suzukiHlogDilationDensityRatioMul_fixed_tendsto f)

def suzukiHlogInwardDilate (n : ℕ) (f : SuzukiHlogFourierL2) : SuzukiHlogFourierL2 :=
  suzukiHlogDensityUnitary.symm (suzukiHlogDilationDensityRatioMul n
    (rayDilate (suzukiHlogInwardScale n)⁻¹ (suzukiHlogDensityUnitary f)))

theorem suzukiHlogInwardDilate_tendsto (f : SuzukiHlogFourierL2) :
    Tendsto (fun n => suzukiHlogInwardDilate n f) atTop (nhds f) := by
  have h := (suzukiHlogDensityUnitary.symm.continuous.tendsto
    (suzukiHlogDensityUnitary f)).comp (suzukiHlogDilationDensityRatioMul_dilate_tendsto (suzukiHlogDensityUnitary f))
  have h' : Tendsto (suzukiHlogDensityUnitary.symm ∘ fun n => suzukiHlogDilationDensityRatioMul n
      (rayDilate (suzukiHlogInwardScale n)⁻¹ (suzukiHlogDensityUnitary f))) atTop (nhds f) := by
    simpa only [LinearIsometryEquiv.symm_apply_apply] using h
  apply h'.congr'
  filter_upwards with n
  rfl

def suzukiHlogDirectInwardDilate (n : ℕ) (f : SuzukiHlogFourierL2) :
    SuzukiHlogFourierL2 :=
  (memLp_suzukiHlogDilatedFn (suzukiHlogInwardScale_pos n) (suzukiHlogInwardScale_le_two n) f).toLp
    (suzukiHlogDilatedFn (suzukiHlogInwardScale n) f)

theorem suzukiHlogDirectInwardDilate_ae (n : ℕ) (f : SuzukiHlogFourierL2) :
    (suzukiHlogDirectInwardDilate n f : ℝ → ℂ) =ᵐ[suzukiHlogMeasure]
      suzukiHlogDilatedFn (suzukiHlogInwardScale n) f :=
  (memLp_suzukiHlogDilatedFn (suzukiHlogInwardScale_pos n) (suzukiHlogInwardScale_le_two n) f).coeFn_toLp

theorem suzukiHlogDirectInwardDilate_eq_weightedDilate
    (n : ℕ) (f : SuzukiHlogFourierL2) :
    suzukiHlogDirectInwardDilate n f = suzukiHlogInwardDilate n f := by
  apply suzukiHlogDensityUnitary.injective
  apply Lp.ext
  have hdirect :
      (suzukiHlogDirectInwardDilate n f : ℝ → ℂ) =ᵐ[volume]
        suzukiHlogDilatedFn (suzukiHlogInwardScale n) f :=
    (suzukiHlogDirectInwardDilate_ae n f).filter_mono
      (ae_mono volume_le_suzukiHlogMeasure)
  have hmulDirect := densityMul_ae suzukiLogWeight measurable_suzukiLogWeight
    suzukiLogWeight_pos (suzukiHlogDirectInwardDilate n f)
  have hmulF := densityMul_ae suzukiLogWeight measurable_suzukiLogWeight
    suzukiLogWeight_pos f
  have hmulFcomp := hmulF.comp_tendsto
    (realMul_quasiMeasurePreserving (suzukiHlogInwardScale n)⁻¹
      (inv_ne_zero (suzukiHlogInwardScale_pos n).ne')).tendsto_ae
  have hdil := rayDilate_ae (inv_pos.mpr (suzukiHlogInwardScale_pos n)) (suzukiHlogDensityUnitary f)
  have hratio := lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
    (suzukiHlogDilationDensityRatio_measurable n) (Real.sqrt_nonneg 2) (suzukiHlogDilationDensityRatio_bound n)
    (rayDilate (suzukiHlogInwardScale n)⁻¹ (suzukiHlogDensityUnitary f))
  have hweighted : suzukiHlogDensityUnitary (suzukiHlogInwardDilate n f) =
      suzukiHlogDilationDensityRatioMul n (rayDilate (suzukiHlogInwardScale n)⁻¹ (suzukiHlogDensityUnitary f)) := by
    exact suzukiHlogDensityUnitary.apply_symm_apply _
  filter_upwards [hmulDirect, hdirect, hmulFcomp, hdil, hratio] with x hmd hdir hmf hd hr
  rw [hweighted]
  change (densityMul suzukiLogWeight measurable_suzukiLogWeight suzukiLogWeight_pos
    (suzukiHlogDirectInwardDilate n f) : ℝ → ℂ) x = _
  have hleft :
      (densityMul suzukiLogWeight measurable_suzukiLogWeight suzukiLogWeight_pos
        (suzukiHlogDirectInwardDilate n f) : ℝ → ℂ) x =
        sqrtWeight suzukiLogWeight x * suzukiHlogDilatedFn (suzukiHlogInwardScale n) f x := by
    exact hmd.trans (congrArg (fun z : ℂ => sqrtWeight suzukiLogWeight x * z) hdir)
  rw [hleft]
  change sqrtWeight suzukiLogWeight x * suzukiHlogDilatedFn (suzukiHlogInwardScale n) f x =
    (suzukiHlogDilationDensityRatioMul n (rayDilate (suzukiHlogInwardScale n)⁻¹ (suzukiHlogDensityUnitary f)) : ℝ → ℂ) x
  change ((suzukiHlogDilationDensityRatioMul n
    (rayDilate (suzukiHlogInwardScale n)⁻¹ (suzukiHlogDensityUnitary f)) : SoninL2) : ℝ → ℂ) x =
      suzukiHlogDilationDensityRatio n x *
        (rayDilate (suzukiHlogInwardScale n)⁻¹ (suzukiHlogDensityUnitary f) : ℝ → ℂ) x at hr
  rw [hr, hd]
  have hmf' : (suzukiHlogDensityUnitary f : ℝ → ℂ) ((suzukiHlogInwardScale n)⁻¹ * x) =
      sqrtWeight suzukiLogWeight ((suzukiHlogInwardScale n)⁻¹ * x) *
        f ((suzukiHlogInwardScale n)⁻¹ * x) := by
    change (densityMul suzukiLogWeight measurable_suzukiLogWeight suzukiLogWeight_pos f :
      ℝ → ℂ) ((suzukiHlogInwardScale n)⁻¹ * x) = _
    change (densityMul suzukiLogWeight measurable_suzukiLogWeight suzukiLogWeight_pos f :
      ℝ → ℂ) ((suzukiHlogInwardScale n)⁻¹ * x) =
        sqrtWeight suzukiLogWeight ((suzukiHlogInwardScale n)⁻¹ * x) *
          f ((suzukiHlogInwardScale n)⁻¹ * x) at hmf
    exact hmf
  rw [hmf']
  unfold suzukiHlogDilatedFn suzukiHlogDilationDensityRatio sqrtWeight
  push_cast
  have hden : 0 ≤ suzukiLogWeight ((suzukiHlogInwardScale n)⁻¹ * x) :=
    suzukiLogWeight_nonneg _
  have hnum : 0 ≤ suzukiLogWeight x := suzukiLogWeight_nonneg _
  rw [Real.sqrt_div hnum]
  have hdenne : Real.sqrt (suzukiLogWeight ((suzukiHlogInwardScale n)⁻¹ * x)) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (suzukiLogWeight_pos _)
  push_cast
  have hdenneC : ((Real.sqrt (suzukiLogWeight ((suzukiHlogInwardScale n)⁻¹ * x)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hdenne
  have hdenneC' : ((Real.sqrt (suzukiLogWeight (x / suzukiHlogInwardScale n)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (suzukiLogWeight_pos _))
  field_simp [hdenneC, hdenneC']

theorem suzukiHlogDirectInwardDilate_tendsto (f : SuzukiHlogFourierL2) :
    Tendsto (fun n => suzukiHlogDirectInwardDilate n f) atTop (nhds f) := by
  simpa only [suzukiHlogDirectInwardDilate_eq_weightedDilate] using
    suzukiHlogInwardDilate_tendsto f

end RHTower
