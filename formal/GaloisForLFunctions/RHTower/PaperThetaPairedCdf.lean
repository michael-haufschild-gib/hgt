import GaloisForLFunctions.RHTower.PaperThetaCdfLowerTail
import GaloisForLFunctions.RHTower.PaperThetaPrimitivePair
import GaloisForLFunctions.RHTower.PaperThetaDivisorReflection
import GaloisForLFunctions.RHTower.PaperThetaEntireEnergy

/-! # Integrable paired endpoint error under the actual CDF

Second-order primitive cancellation survives the singular CDF change of
variables. The right-half estimate holds for every complex parameter.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

open HedenmalmThetaSource GaloisForLFunctions.HTGeometry

def pairedTailDensity (z : ℂ) (x : ℝ) : ℂ :=
  (thetaSource.normalized x : ℂ) * (flatQuotient z x + flatQuotient (-z) x + 2) /
    ((1-thetaSource.cdfFun x : ℝ) : ℂ)

theorem continuous_pairedTailDensity (z : ℂ) : Continuous (pairedTailDensity z) := by
  apply ((Complex.continuous_ofReal.comp continuous_normalized_theta).mul
    (((continuous_flatQuotient z).add (continuous_flatQuotient (-z))).add continuous_const)).div
      (Complex.continuous_ofReal.comp (continuous_const.sub thetaSource.continuous_cdfFun))
  intro x
  change ((1-thetaSource.cdfFun x : ℝ) : ℂ) ≠ 0
  exact_mod_cast (sub_pos.mpr (thetaSource.cdfFun_mem_Ioo x).2).ne'

/-- The singular CDF weight still leaves an exponentially integrable paired error. -/
theorem pairedTailDensity_decay (z : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      ‖pairedTailDensity z x‖ ≤ C*Real.exp (-2*x) := by
  obtain ⟨C, hC, hb⟩ := flatQuotient_pair_decay z
  let H := thetaEnvelopeUpper / (thetaEnvelopeLower * Real.exp (-2*Real.pi*Real.exp 2))
  have hH : 0 ≤ H := (div_pos thetaEnvelopeUpper_pos
    (mul_pos thetaEnvelopeLower_pos (Real.exp_pos _))).le
  refine ⟨H*C, mul_nonneg hH hC, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), hb] with x hx hpair
  have ht := sub_pos.mpr (thetaSource.cdfFun_mem_Ioo x).2
  rw [pairedTailDensity, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (thetaSource.normalized_pos x), Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ht]
  calc
    _ = (thetaSource.normalized x / (1-thetaSource.cdfFun x)) *
        ‖flatQuotient z x+flatQuotient (-z) x+2‖ := by ring
    _ ≤ (H*Real.exp (2*x))*(C*Real.exp (-4*x)) :=
      mul_le_mul (cdfHazard_le_exp ⟨x, hx⟩) hpair (norm_nonneg _) (by positivity)
    _ = (H*C)*Real.exp (-2*x) := by
      rw [mul_mul_mul_comm, ← Real.exp_add, show 2*x + -4*x = -2*x by ring]

/-- All tail integrability is paid by the native source estimates. -/
theorem integrableOn_pairedTailDensity (z : ℂ) :
    IntegrableOn (pairedTailDensity z) (Ici (0 : ℝ)) := by
  obtain ⟨C, _, hb⟩ := pairedTailDensity_decay z
  obtain ⟨A, hA⟩ := eventually_atTop.mp hb
  have ht : IntegrableOn (pairedTailDensity z) (Ioi A) := by
    apply ((exp_neg_integrableOn_Ioi A (show (0 : ℝ) < 2 by norm_num)).const_mul C).mono'
      (continuous_pairedTailDensity z).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hA x (show A < x from hx).le
  apply ((continuous_pairedTailDensity z).integrableOn_Icc.union ht).mono_set
  intro x hx
  by_cases hxA : x ≤ A
  · exact Or.inl ⟨hx, hxA⟩
  · exact Or.inr (lt_of_not_ge hxA)

/-- CDF transport pays the actual right-end Dini weight, for every parameter. -/
theorem integrable_upper_pair_div_tail (z : ℂ) :
    Integrable ((Ici (thetaSource.cdfFun 0)).indicator (fun t : ℝ =>
      (flatModePullback z t + flatModePullback (-z) t + 2) / ((1-t : ℝ) : ℂ)))
        unitIntervalMeasure := by
  have hm : Measurable (fun t : ℝ =>
      (flatModePullback z t + flatModePullback (-z) t + 2) / ((1-t : ℝ) : ℂ)) :=
    (((measurable_pullback_all z).add (measurable_pullback_all (-z))).add measurable_const).div
      (Complex.continuous_ofReal.measurable.comp (measurable_const.sub measurable_id))
  apply (integrable_unitInterval_iff_cdf (hm.indicator measurableSet_Ici).aestronglyMeasurable).mpr
  have he : (fun x => thetaSource.normalized x •
      (Ici (thetaSource.cdfFun 0)).indicator (fun t : ℝ =>
        (flatModePullback z t + flatModePullback (-z) t + 2) / ((1-t : ℝ) : ℂ))
          (thetaSource.cdfFun x)) = (Ici (0 : ℝ)).indicator (pairedTailDensity z) := by
    funext x
    by_cases hx : 0 ≤ x
    · have hF : thetaSource.cdfFun 0 ≤ thetaSource.cdfFun x := thetaSource.strictMono_cdfFun.monotone hx
      rw [indicator_of_mem (show thetaSource.cdfFun x ∈ Ici (thetaSource.cdfFun 0) from hF),
        indicator_of_mem (show x ∈ Ici (0 : ℝ) from hx), flatModePullback_eq_flatQuotient,
        flatModePullback_eq_flatQuotient, thetaSource.quantile_cdfFun, Complex.real_smul,
        pairedTailDensity]
      ring
    · have hF : thetaSource.cdfFun x ∉ Ici (thetaSource.cdfFun 0) :=
        not_le.mpr (thetaSource.strictMono_cdfFun (lt_of_not_ge hx))
      rw [indicator_of_notMem hF, indicator_of_notMem (show x ∉ Ici (0 : ℝ) from hx), smul_zero]
  rw [he]
  exact (integrableOn_pairedTailDensity z).integrable_indicator measurableSet_Ici

end RHTower.PaperThetaEndpoint
