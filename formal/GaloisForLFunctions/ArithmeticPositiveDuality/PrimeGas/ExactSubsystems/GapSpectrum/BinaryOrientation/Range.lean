import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.Thermometry
import GaloisForLFunctions.RHTower.RiemannXiZerosInfinite

/-! # Full range of the two-copy gap thermometer -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation

open Set Filter Topology

private theorem real_partition (h : Ioi (0:ℝ)) :
    labelPartition h = (riemannZeta ((labelTemperature h).val:ℂ)).re :=
  congrArg Complex.re (thermalWeight_partition (labelTemperature h))

private theorem gap_ratio (h : Ioi (0:ℝ)) :
    gapKolmogorovDistance h = labelPartition (pairedExcess h)/(labelPartition h)^2/2 := by
  rw [gapKolmogorov_exact,collision_vacuum_product]
  apply congrArg (fun x : ℝ => x/2)
  apply (div_eq_div_iff (mul_pos (labelPartition_pos h) (binaryPartition_pos h)).ne'
    (pow_pos (labelPartition_pos h) 2).ne').mpr
  calc
    1*labelPartition h^2 = labelPartition h*(binaryPartition h*labelPartition (pairedExcess h)) := by rw [binaryPartition_times_paired,one_mul,pow_two]
    _ = _ := by ring

private theorem partition_continuous : Continuous labelPartition := by
  rw [show labelPartition = _ from funext real_partition]
  apply continuous_iff_continuousAt.mpr
  intro h
  have hc : Continuous (fun k : Ioi (0:ℝ) => ((labelTemperature k).val:ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_const.add continuous_subtype_val)
  have hn : ((labelTemperature h).val:ℂ) ≠ 1 :=
    fun he => (labelTemperature h).property.ne' (by exact_mod_cast he)
  exact (Complex.continuous_re.tendsto _).comp
    ((differentiableAt_riemannZeta hn).continuousAt.tendsto.comp (hc.tendsto h))

theorem gap_distance_continuous : Continuous gapKolmogorovDistance := by
  have hc : Continuous pairedExcess :=
    (continuous_const.add (continuous_const.mul continuous_subtype_val)).subtype_mk _
  rw [show gapKolmogorovDistance = _ from funext gap_ratio]
  exact ((partition_continuous.comp hc).div (partition_continuous.pow 2)
    (fun h => (pow_pos (labelPartition_pos h) 2).ne')).div_const 2

/-- When the gas cools to its vacuum the uniform gap distance tends to one half. -/
theorem gap_distance_cold : Tendsto gapKolmogorovDistance atTop (𝓝 (1/2:ℝ)) := by
  have hv : Tendsto (Subtype.val : Ioi (0:ℝ) → ℝ) atTop atTop := by
    apply tendsto_atTop.mpr
    intro x
    let a : Ioi (0:ℝ) := ⟨max x 1,by
      change (0:ℝ) < max x 1
      exact zero_lt_one.trans_le (le_max_right x 1)⟩
    exact (eventually_ge_atTop a).mono (fun h hh => (le_max_left x 1).trans hh)
  have h₁ : Tendsto (fun h : Ioi (0:ℝ) => (labelTemperature h).val) atTop atTop :=
    tendsto_atTop_mono (fun h => by change h.val ≤ 1+h.val; linarith) hv
  have h₂ : Tendsto (fun h : Ioi (0:ℝ) => (labelTemperature (pairedExcess h)).val) atTop atTop := by
    refine tendsto_atTop_mono ?_ h₁
    intro h
    change 1+h.val ≤ 1+(1+2*h.val)
    linarith only [show 0 < h.val from h.property]
  have hz := Complex.continuous_re.continuousAt.tendsto.comp _root_.RHTower.tendsto_riemannZeta_atTop
  have H := ((hz.comp h₂).div ((hz.comp h₁).pow 2) (by simp)).div_const 2
  simp only [Complex.one_re,one_pow,div_one] at H
  exact H.congr (fun h => by simp only [gap_ratio,real_partition,Pi.div_apply,Function.comp_apply])

private theorem gap_distance_critical : Tendsto gapKolmogorovDistance criticalApproach (𝓝 0) := by
  have hv : Tendsto (Subtype.val : Ioi (0:ℝ) → ℝ) criticalApproach (𝓝[>] 0) := tendsto_comap
  have H := gapKolmogorov_exact_quadratic_limit.mul ((hv.mono_right nhdsWithin_le_nhds).pow 2)
  simp only [zero_pow (by norm_num : 2 ≠ 0),mul_zero] at H
  exact H.congr (fun h => div_mul_cancel₀ _ (pow_ne_zero 2 h.property.ne'))

private theorem gap_reading_range (h : Ioi (0:ℝ)) : gapKolmogorovDistance h ∈ Ioo (0:ℝ) (1/2) := by
  refine ⟨?_,?_⟩
  · rw [gapKolmogorov_exact,collision_vacuum_product]
    exact div_pos (one_div_pos.mpr (mul_pos (labelPartition_pos h) (binaryPartition_pos h))) zero_lt_two
  · let k : Ioi (0:ℝ) := ⟨h.val+1,by
      change (0:ℝ) < h.val+1
      linarith only [show 0 < h.val from h.property]⟩
    have hk : h < k := by change h.val < h.val+1; linarith
    exact (gap_distance_strictMono hk).trans_le
      (gap_distance_strictMono.monotone.ge_of_tendsto gap_distance_cold k)

/-- Each reading strictly between zero and one half occurs at exactly one inverse temperature. -/
theorem gap_distance_existsUnique (u : Ioo (0:ℝ) (1/2)) :
    ∃! h : Ioi (0:ℝ), gapKolmogorovDistance h = u.val := by
  letI : NeBot criticalApproach := criticalApproach_neBot
  letI : PreconnectedSpace (Ioi (0:ℝ)) :=
    (isPreconnected_iff_preconnectedSpace (s := Ioi (0:ℝ))).mp isPreconnected_Ioi
  obtain ⟨x,hx⟩ := (gap_distance_critical.eventually_lt_const u.property.1).exists
  obtain ⟨y,hy⟩ := (gap_distance_cold.eventually_const_lt u.property.2).exists
  obtain ⟨h,hh⟩ := intermediate_value_univ x y gap_distance_continuous
    (show u.val ∈ Icc _ _ from ⟨hx.le,hy.le⟩)
  exact ⟨h,hh,fun k hk => gap_distance_strictMono.injective (hk.trans hh.symm)⟩

def gapCalibration : Ioi (0:ℝ) ≃o Ioo (0:ℝ) (1/2) :=
  StrictMono.orderIsoOfSurjective (fun h => ⟨gapKolmogorovDistance h,gap_reading_range h⟩)
    gap_distance_strictMono (fun u => by
      obtain ⟨h,hh,_⟩ := gap_distance_existsUnique u
      exact ⟨h,Subtype.ext hh⟩)

theorem gapCalibration_apply (h : Ioi (0:ℝ)) :
    (gapCalibration h).val = gapKolmogorovDistance h := rfl

#print axioms gap_distance_continuous
#print axioms gap_distance_cold
#print axioms gap_distance_existsUnique
#print axioms gapCalibration
#print axioms gapCalibration_apply

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation
