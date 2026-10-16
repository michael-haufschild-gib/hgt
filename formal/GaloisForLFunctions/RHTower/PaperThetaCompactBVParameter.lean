import GaloisForLFunctions.RHTower.PaperThetaBVParameterDifferentiation
import GaloisForLFunctions.RHTower.PaperThetaConfluentAdmission

/-! # The original compact BV parameter derivative

The singular quantile change preserves the entire variation of the literal
difference-quotient remainder. Both endpoint traces are zero. Thus the
whole-line BV parameter derivative is also the strong derivative in the
paper's original closed-interval BV norm, with the interior charge retained.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile

theorem continuousWithinAt_cutQuantileParameterJet_zero
    (n : ℕ) (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    ContinuousWithinAt (cutQuantileParameterJet n z c) (Ici 0) 0 := by
  have hc := (absolutelyContinuousOnInterval_leftClosedParameterJet n z c).continuousOn
    0 (by simp only [uIcc_of_le c.property.1.le, mem_Icc]; exact ⟨le_rfl, c.property.1.le⟩)
  have hl : ContinuousWithinAt (leftClosedParameterJet n z) (Ici 0) 0 := by
    simpa only [ContinuousWithinAt, uIcc_of_le c.property.1.le,
      nhdsWithin_Icc_eq_nhdsGE c.property.1] using hc
  change Tendsto _ _ _
  rw [cutQuantileParameterJet_left n z c c.property.1]
  apply hl.congr'
  have he : ∀ᶠ t : ℝ in 𝓝 0, t < c.val := Iio_mem_nhds c.property.1
  filter_upwards [he.filter_mono nhdsWithin_le_nhds] with t ht
  exact (cutQuantileParameterJet_left n z c ht).symm

theorem continuousWithinAt_cutQuantileParameterJet_one
    (n : ℕ) (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    ContinuousWithinAt (cutQuantileParameterJet n z c) (Iic 1) 1 := by
  have hc := (absolutelyContinuousOnInterval_closedParameterJet_right n z c).continuousOn
    1 (by simp only [uIcc_of_le c.property.2.le, mem_Icc]; exact ⟨c.property.2.le, le_rfl⟩)
  have hr : ContinuousWithinAt (closedParameterJet n z) (Iic 1) 1 := by
    simpa only [ContinuousWithinAt, uIcc_of_le c.property.2.le,
      nhdsWithin_Icc_eq_nhdsLE c.property.2] using hc
  change Tendsto _ _ _
  rw [cutQuantileParameterJet_right n z c c.property.2.le]
  apply hr.congr'
  have he : ∀ᶠ t : ℝ in 𝓝 1, c.val < t := Ioi_mem_nhds c.property.2
  filter_upwards [he.filter_mono nhdsWithin_le_nhds] with t ht
  exact (cutQuantileParameterJet_right n z c ht.le).symm

def cutQuantileSlopeRemainder (c : Ioo (0 : ℝ) 1) (z h : ℂ) (t : ℝ) : ℂ :=
  h⁻¹ * (cutQuantileParameterJet 0 (z+h) c t - cutQuantileParameterJet 0 z c t) -
    cutQuantileParameterJet 1 z c t

theorem cutQuantileSlopeRemainder_interior (c t : Ioo (0 : ℝ) 1) (z h : ℂ) :
    cutQuantileSlopeRemainder c z h t.val =
      cutParameterSlopeRemainder (thetaSource.quantileFun c.val) z h
        (thetaSource.quantileFun t.val) := by
  simp only [cutQuantileSlopeRemainder, cutQuantileParameterJet_interior,
    cutParameterSlopeRemainder, cutParameterJet, iteratedDeriv_zero]

theorem cutQuantileSlopeRemainder_endpoints (c : Ioo (0 : ℝ) 1) (z h : ℂ) :
    cutQuantileSlopeRemainder c z h 0 = 0 ∧ cutQuantileSlopeRemainder c z h 1 = 0 := by
  simp only [cutQuantileSlopeRemainder,
    (cutQuantileParameterJet_endpoints 0 (z+h) c).1,
    (cutQuantileParameterJet_endpoints 0 z c).1,
    (cutQuantileParameterJet_endpoints 1 z c).1,
    (cutQuantileParameterJet_endpoints 0 (z+h) c).2,
    (cutQuantileParameterJet_endpoints 0 z c).2,
    (cutQuantileParameterJet_endpoints 1 z c).2,
    sub_self, mul_zero, parameterEndpointTrace, if_false, if_true,
    Nat.one_ne_zero, and_self]

/-- Exact variation transport includes both endpoint traces and the interior charge. -/
theorem eVariationOn_cutQuantileSlopeRemainder (c : Ioo (0 : ℝ) 1) (z h : ℂ) :
    eVariationOn (cutQuantileSlopeRemainder c z h) (Icc (0 : ℝ) 1) =
      eVariationOn (cutParameterSlopeRemainder (thetaSource.quantileFun c.val) z h) univ := by
  have h0 : ContinuousWithinAt (cutQuantileSlopeRemainder c z h) (Ici 0) 0 :=
    (continuousWithinAt_const.mul
      ((continuousWithinAt_cutQuantileParameterJet_zero 0 (z+h) c).sub
        (continuousWithinAt_cutQuantileParameterJet_zero 0 z c))).sub
      (continuousWithinAt_cutQuantileParameterJet_zero 1 z c)
  have h1 : ContinuousWithinAt (cutQuantileSlopeRemainder c z h) (Iic 1) 1 :=
    (continuousWithinAt_const.mul
      ((continuousWithinAt_cutQuantileParameterJet_one 0 (z+h) c).sub
        (continuousWithinAt_cutQuantileParameterJet_one 0 z c))).sub
      (continuousWithinAt_cutQuantileParameterJet_one 1 z c)
  have hne : (𝓝[Ioi (0 : ℝ) ∩ Iio 1] (1 : ℝ)).NeBot := by
    rw [Ioi_inter_Iio, nhdsWithin_Ioo_eq_nhdsLT (by norm_num : (0:ℝ)<1)]
    infer_instance
  have hr := eVariationOn.eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt hne
    (h1.mono (show Ioi (0:ℝ) ∩ Iic 1 ⊆ Iic 1 from inter_subset_right))
  rw [Ioi_inter_Iio, Ioi_inter_Iic] at hr
  rw [← eVariationOn.eVariationOn_Ioc_eq_Icc_of_continuousWithinAt h0, ← hr]
  rw [eVariationOn.congr (g := fun t =>
    cutParameterSlopeRemainder (thetaSource.quantileFun c.val) z h (thetaSource.quantileFun t))
      (fun t ht => cutQuantileSlopeRemainder_interior c ⟨t, ht⟩ z h)]
  change eVariationOn
    (cutParameterSlopeRemainder (thetaSource.quantileFun c.val) z h ∘ thetaSource.quantileFun)
      (Ioo 0 1) = _
  rw [eVariationOn.comp_eq_of_monotoneOn _ _ thetaSource.strictMonoOn_quantileFun.monotoneOn]
  congr 1
  apply eq_univ_of_forall
  intro x
  exact ⟨thetaSource.cdfFun x, thetaSource.cdfFun_mem_Ioo x, thetaSource.quantile_cdfFun x⟩

/-- Strong differentiation in the original closed-interval BV norm for every complex parameter. -/
theorem tendsto_cutQuantileSlopeRemainder_BV (c : Ioo (0 : ℝ) 1) (z : ℂ) :
    Tendsto (fun h : ℂ => ENNReal.ofReal ‖cutQuantileSlopeRemainder c z h 0‖ +
      eVariationOn (cutQuantileSlopeRemainder c z h) (Icc (0:ℝ) 1))
      (𝓝[≠] 0) (𝓝 0) := by
  simp only [(cutQuantileSlopeRemainder_endpoints c z _).1, norm_zero,
    ENNReal.ofReal_zero, zero_add, eVariationOn_cutQuantileSlopeRemainder]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_cutParameterSlopeRemainder_globalBV (thetaSource.quantileFun c.val) z)
    (Eventually.of_forall fun _ => bot_le)
    (Eventually.of_forall fun _ => le_add_of_nonneg_left bot_le)

end RHTower.PaperThetaEndpoint
