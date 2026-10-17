import GaloisForLFunctions.BiScaleUncertainty.BroadSpectralCostRealization
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! # Quantitative energy decay for actual stretched compact sources -/

open Set Filter Topology MeasureTheory
open scoped CompactlySupported BoundedContinuousFunction
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-- A fixed source supplies one constant valid for every positive dilation. -/
theorem exists_sourceRescale_linear_energy_bound {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ δ : ℝ, 0 < δ →
      0 ≤ normalizedArchEnergy (sourceRescale f δ) ∧
        normalizedArchEnergy (sourceRescale f δ) ≤ δ * K := by
  obtain ⟨M, hM, hbound⟩ := exists_autocorr_increment_linear_bound hf hfc
  let K : ℝ := M * archWeightFirstMoment / autocorr f 0
  have hK : 0 ≤ K := div_nonneg (mul_nonneg hM archWeightFirstMoment_nonneg) hR.le
  refine ⟨K, hK, ?_⟩
  intro δ hδ
  have hreg := contDiff_sourceRescale hf δ
  have hcomp := hasCompactSupport_sourceRescale hfc hδ
  have hmass : autocorr (sourceRescale f δ) 0 = δ⁻¹ * autocorr f 0 := by
    simpa only [mul_zero] using autocorr_sourceRescale f hδ 0
  have hpos : 0 < autocorr (sourceRescale f δ) 0 := by rw [hmass]; positivity
  have hraw : biScaleLevyEnergy (sourceRescale f δ) ≤ M * archWeightFirstMoment := by
    unfold biScaleLevyEnergy archWeightFirstMoment
    rw [← integral_const_mul]
    refine setIntegral_mono_on (integrableOn_biScaleLevyIntegrand hreg hcomp)
      (integrableOn_mul_archLevySinhWeight.const_mul M) measurableSet_Ioi (fun x hx => ?_)
    rw [hmass, autocorr_sourceRescale f hδ]
    have hb := hbound (δ * x)
    rw [abs_of_pos (mul_pos hδ hx)] at hb
    have hmul := mul_le_mul_of_nonneg_left hb (inv_pos.mpr hδ).le
    have heq : δ⁻¹ * (M * (δ * x)) = M * x := by field_simp [hδ.ne']
    rw [heq] at hmul
    have hi : δ⁻¹ * autocorr f 0 - δ⁻¹ * autocorr f (δ * x) ≤ M * x := by
      simpa only [mul_sub] using hmul
    calc
      _ ≤ (M * x) * archLevySinhWeight x :=
        mul_le_mul_of_nonneg_right hi (archLevySinhWeight_pos hx).le
      _ = _ := by ring
  constructor
  · exact div_nonneg (biScaleLevyEnergy_nonneg hcomp hreg.continuous) hpos.le
  · unfold normalizedArchEnergy
    rw [hmass]
    calc
      _ ≤ (M * archWeightFirstMoment) / (δ⁻¹ * autocorr f 0) :=
        div_le_div_of_nonneg_right hraw (by positivity)
      _ = δ * K := by unfold K; field_simp [hδ.ne', hR.ne']

def nyquistWideBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

theorem nyquistWideBump_zero : nyquistWideBump 0 = 1 := by
  apply nyquistWideBump.one_of_mem_closedBall
  norm_num [nyquistWideBump, Metric.mem_closedBall]

theorem nyquistWideBump_mass_pos : 0 < autocorr (nyquistWideBump : ℝ → ℝ) 0 := by
  unfold autocorr
  simp only [add_zero]
  exact (nyquistWideBump.continuous.mul nyquistWideBump.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
      nyquistWideBump.hasCompactSupport.mul_right
      (fun x => mul_self_nonneg (nyquistWideBump x)) (x := 0)
      (by rw [nyquistWideBump_zero]; norm_num)

def nyquistWideScale (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

theorem nyquistWideScale_pos (j : ℕ) : 0 < nyquistWideScale j := by
  unfold nyquistWideScale
  positivity

theorem tendsto_nyquistWideScale : Tendsto nyquistWideScale atTop (𝓝 0) := by
  unfold nyquistWideScale
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- This actual source family is fixed independently of all weight parameters. -/
def nyquistWideSource (j : ℕ) : C_c(ℝ, ℝ) :=
  ⟨⟨sourceRescale (nyquistWideBump : ℝ → ℝ) (nyquistWideScale j),
      (contDiff_sourceRescale (nyquistWideBump.contDiff (n := 2)) (nyquistWideScale j)).continuous⟩,
    hasCompactSupport_sourceRescale nyquistWideBump.hasCompactSupport (nyquistWideScale_pos j)⟩

theorem contDiff_nyquistWideSource (j : ℕ) (r : ℕ∞) :
    ContDiff ℝ (r : WithTop ℕ∞) (nyquistWideSource j : ℝ → ℝ) :=
  contDiff_sourceRescale (nyquistWideBump.contDiff (n := r)) (nyquistWideScale j)

theorem nyquistWideSource_nonneg (j : ℕ) (x : ℝ) : 0 ≤ nyquistWideSource j x :=
  nyquistWideBump.nonneg

theorem nyquistWideSource_mass (j : ℕ) :
    autocorr (nyquistWideSource j) 0 =
      (nyquistWideScale j)⁻¹ * autocorr (nyquistWideBump : ℝ → ℝ) 0 := by
  change autocorr (sourceRescale (nyquistWideBump : ℝ → ℝ) (nyquistWideScale j)) 0 = _
  simpa only [mul_zero] using
    autocorr_sourceRescale (nyquistWideBump : ℝ → ℝ) (nyquistWideScale_pos j) 0

theorem nyquistWideSource_mass_pos (j : ℕ) : 0 < autocorr (nyquistWideSource j) 0 := by
  rw [nyquistWideSource_mass]
  exact mul_pos (inv_pos.mpr (nyquistWideScale_pos j)) nyquistWideBump_mass_pos

def nyquistWideCorrelation (j : ℕ) (x : ℝ) : ℝ :=
  autocorr (nyquistWideSource j) x / autocorr (nyquistWideSource j) 0

theorem nyquistWideCorrelation_nonneg (j : ℕ) (x : ℝ) : 0 ≤ nyquistWideCorrelation j x := by
  apply div_nonneg _ (nyquistWideSource_mass_pos j).le
  exact integral_nonneg (fun u => mul_nonneg
    (nyquistWideSource_nonneg j u) (nyquistWideSource_nonneg j (u + x)))

theorem abs_nyquistWideCorrelation_le_one (j : ℕ) (x : ℝ) :
    |nyquistWideCorrelation j x| ≤ 1 := by
  rw [nyquistWideCorrelation, abs_div, abs_of_pos (nyquistWideSource_mass_pos j)]
  exact (div_le_one (nyquistWideSource_mass_pos j)).mpr
    (abs_autocorr_le_zero (nyquistWideSource j).hasCompactSupport (nyquistWideSource j).continuous x)

theorem continuous_nyquistWideCorrelation (j : ℕ) : Continuous (nyquistWideCorrelation j) :=
  (continuous_autocorr (contDiff_nyquistWideSource j 2)
    (nyquistWideSource j).hasCompactSupport).div_const _

theorem hasCompactSupport_nyquistWideCorrelation (j : ℕ) :
    HasCompactSupport (nyquistWideCorrelation j) := by
  change HasCompactSupport (fun x => autocorr (nyquistWideSource j) x /
    autocorr (nyquistWideSource j) 0)
  have hh := (hasCompactSupport_autocorr (nyquistWideSource j).hasCompactSupport).mul_right
    (f' := fun _ => (autocorr (nyquistWideSource j) 0)⁻¹)
  change HasCompactSupport (fun x =>
    autocorr (nyquistWideSource j) x * (autocorr (nyquistWideSource j) 0)⁻¹) at hh
  simpa only [div_eq_mul_inv] using hh

theorem nyquistWideCorrelation_eq (j : ℕ) (x : ℝ) :
    nyquistWideCorrelation j x =
      autocorr (nyquistWideBump : ℝ → ℝ) (nyquistWideScale j * x) /
        autocorr (nyquistWideBump : ℝ → ℝ) 0 := by
  change autocorr (sourceRescale (nyquistWideBump : ℝ → ℝ) (nyquistWideScale j)) x /
    autocorr (sourceRescale (nyquistWideBump : ℝ → ℝ) (nyquistWideScale j)) 0 = _
  rw [autocorr_sourceRescale _ (nyquistWideScale_pos j) x,
    autocorr_sourceRescale _ (nyquistWideScale_pos j) 0, mul_zero]
  field_simp [(nyquistWideScale_pos j).ne', nyquistWideBump_mass_pos.ne']

theorem tendsto_nyquistWideCorrelation (x : ℝ) :
    Tendsto (fun j => nyquistWideCorrelation j x) atTop (𝓝 1) := by
  have hx : Tendsto (fun j => nyquistWideScale j * x) atTop (𝓝 0) := by
    simpa only [zero_mul] using tendsto_nyquistWideScale.mul_const x
  have hc := (continuous_autocorr (nyquistWideBump.contDiff (n := 2))
    nyquistWideBump.hasCompactSupport).div_const (autocorr (nyquistWideBump : ℝ → ℝ) 0)
  have ht := (hc.tendsto 0).comp hx
  simpa only [Function.comp_def, div_self nyquistWideBump_mass_pos.ne', nyquistWideCorrelation_eq]
    using ht

theorem exists_nyquistWideSource_energy_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j : ℕ,
      0 ≤ normalizedArchEnergy (nyquistWideSource j) ∧
        normalizedArchEnergy (nyquistWideSource j) ≤ K / ((j : ℝ) + 1) := by
  obtain ⟨K, hK, hbound⟩ := exists_sourceRescale_linear_energy_bound
    (nyquistWideBump.contDiff (n := 2)) nyquistWideBump.hasCompactSupport nyquistWideBump_mass_pos
  refine ⟨K, hK, ?_⟩
  intro j
  have hj := hbound (nyquistWideScale j) (nyquistWideScale_pos j)
  constructor
  · exact hj.1
  · calc
      _ ≤ nyquistWideScale j * K := hj.2
      _ = _ := by unfold nyquistWideScale; ring

theorem tendsto_nyquistWideSource_energy :
    Tendsto (fun j => normalizedArchEnergy (nyquistWideSource j)) atTop (𝓝 0) := by
  obtain ⟨K, _, hK⟩ := exists_nyquistWideSource_energy_bound
  apply squeeze_zero (fun j => (hK j).1) (fun j => (hK j).2)
  simpa only [nyquistWideScale, mul_one_div, mul_zero] using tendsto_nyquistWideScale.const_mul K

theorem exists_nyquistWideCorrelation_plateau :
    ∃ r : ℝ, 0 < r ∧ ∀ j : ℕ, ∀ x : ℝ, 0 ≤ x → x ≤ r * ((j : ℝ) + 1) →
      1 / 2 ≤ nyquistWideCorrelation j x := by
  obtain ⟨M, hM, hb⟩ := exists_autocorr_increment_linear_bound
    (nyquistWideBump.contDiff (n := 2)) nyquistWideBump.hasCompactSupport
  let R : ℝ := autocorr (nyquistWideBump : ℝ → ℝ) 0
  have hR : 0 < R := nyquistWideBump_mass_pos
  let r : ℝ := R / (2 * (M + 1))
  have hr : 0 < r := by unfold r; positivity
  have heq : 2 * (M + 1) * r = R := by unfold r; field_simp
  have hMr : M * r ≤ R / 2 := by nlinarith
  refine ⟨r, hr, ?_⟩
  intro j x hx hxr
  have ht0 : 0 ≤ nyquistWideScale j * x := mul_nonneg (nyquistWideScale_pos j).le hx
  have htr : nyquistWideScale j * x ≤ r := by
    have hh := mul_le_mul_of_nonneg_left hxr (nyquistWideScale_pos j).le
    have hh' : nyquistWideScale j * (r * ((j : ℝ) + 1)) = r := by
      unfold nyquistWideScale
      field_simp
    rwa [hh'] at hh
  have hd := hb (nyquistWideScale j * x)
  rw [abs_of_nonneg ht0] at hd
  have hd' := hd.trans ((mul_le_mul_of_nonneg_left htr hM).trans hMr)
  rw [nyquistWideCorrelation_eq]
  apply (le_div_iff₀ nyquistWideBump_mass_pos).mpr
  change R - autocorr (nyquistWideBump : ℝ → ℝ) (nyquistWideScale j * x) ≤ R / 2 at hd'
  linarith

def nyquistWideCorrelationMap (j : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (nyquistWideCorrelation j)
    (continuous_nyquistWideCorrelation j) 1
    (fun x => by simpa only [Real.norm_eq_abs] using abs_nyquistWideCorrelation_le_one j x)

theorem nyquistWideCorrelationMap_apply (j : ℕ) (x : ℝ) :
    nyquistWideCorrelationMap j x = nyquistWideCorrelation j x := rfl

theorem norm_nyquistWideCorrelationMap_le_one (j : ℕ) : ‖nyquistWideCorrelationMap j‖ ≤ 1 :=
  (BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    (fun x => by simpa only [Real.norm_eq_abs, nyquistWideCorrelationMap_apply] using
      abs_nyquistWideCorrelation_le_one j x)

end
end GaloisForLFunctions.BiScaleUncertainty
