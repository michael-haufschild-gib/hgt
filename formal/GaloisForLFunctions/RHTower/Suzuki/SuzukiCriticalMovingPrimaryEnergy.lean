import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalL2Energy

/-!
# Critical primary energy with a varying L² source

Strong L² convergence makes every correlation converge. The pointwise critical
kernel limit and Fatou's lemma then preserve the limiting compensated energy
when both the source and the positive shift vary. Infinite limiting energy
forces divergence without a prescribed rate of source approximation.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal RealInnerProductSpace
open GaloisForLFunctions.BiScaleUncertainty.SobolevShear
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm

namespace RHTower
noncomputable section

/-- Every fixed-lag correlation depends continuously on its real L² source. -/
theorem continuous_autocorr_L2_source (t : ℝ) :
    Continuous (fun q : Velocity => autocorr q t) := by
  have h := Continuous.inner (𝕜 := ℝ) (continuous_id : Continuous (fun q : Velocity => q))
    (physicalTranslation t).continuous
  exact h.congr fun q => (autocorr_eq_inner_physicalTranslation q t).symm

/-- Fatou retains the critical energy when the shift and the L² source vary together. -/
theorem suzukiCriticalLimitingEnergy_le_liminf_of_L2_tendsto {q : ℕ → Velocity} {r : Velocity} {w : ℕ → ℝ}
    (hq : Tendsto q atTop (𝓝 r)) (hw : Tendsto w atTop (𝓝[>] 0)) :
    suzukiCriticalLimitingCompensatedEnergy (fun t => autocorr r 0-autocorr r t) ≤
      liminf (fun n => suzukiCriticalCompensatedEnergy
        (fun t => autocorr (q n) 0-autocorr (q n) t) (w n)) atTop := by
  have hF : ∀ n, AEMeasurable (fun t : ℝ => ENNReal.ofReal
      ((autocorr (q n) 0-autocorr (q n) t) *
        (suzukiCriticalPrimaryDensity (w n) t / w n))) (volume.restrict (Ioi 0)) := by
    intro n
    exact ((measurable_const.sub (continuous_autocorr_of_memLp (Lp.memLp (q n))).measurable).mul
      ((measurable_suzukiCriticalPrimaryDensity (w n)).div measurable_const)).ennreal_ofReal.aemeasurable
  have hpt : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun n => ENNReal.ofReal ((autocorr (q n) 0-autocorr (q n) t) *
        (suzukiCriticalPrimaryDensity (w n) t / w n))) atTop
        (𝓝 (ENNReal.ofReal ((autocorr r 0-autocorr r t) *
          (2*Real.exp (-(5/2 : ℝ)*t)/(1-Real.exp (-2*t)))))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hD := (((continuous_autocorr_L2_source 0).tendsto r).comp hq).sub
      (((continuous_autocorr_L2_source t).tendsto r).comp hq)
    have hB := (tendsto_suzukiCriticalPrimaryDensity_div ht).comp hw
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hD.mul hB)
  calc
    _ = ∫⁻ t in Ioi 0, liminf (fun n => ENNReal.ofReal
        ((autocorr (q n) 0-autocorr (q n) t) *
          (suzukiCriticalPrimaryDensity (w n) t / w n))) atTop := by
      apply lintegral_congr_ae
      exact hpt.mono fun t ht => ht.liminf_eq.symm
    _ ≤ _ := lintegral_liminf_le' hF

/-- Infinite critical energy survives every strongly convergent sequence of sources and shifts. -/
theorem tendsto_suzukiCriticalCompensatedEnergy_top_of_L2_tendsto {q : ℕ → Velocity} {r : Velocity} {w : ℕ → ℝ}
    (hq : Tendsto q atTop (𝓝 r)) (hw : Tendsto w atTop (𝓝[>] 0))
    (henergy : suzukiCriticalLimitingCompensatedEnergy
      (fun t => autocorr r 0-autocorr r t) = ⊤) :
    Tendsto (fun n => suzukiCriticalCompensatedEnergy
      (fun t => autocorr (q n) 0-autocorr (q n) t) (w n)) atTop (𝓝 ⊤) := by
  have h := suzukiCriticalLimitingEnergy_le_liminf_of_L2_tendsto hq hw
  rw [henergy] at h
  exact tendsto_of_le_liminf_of_limsup_le h le_top

end
end RHTower

#print axioms RHTower.continuous_autocorr_L2_source
#print axioms RHTower.suzukiCriticalLimitingEnergy_le_liminf_of_L2_tendsto
#print axioms RHTower.tendsto_suzukiCriticalCompensatedEnergy_top_of_L2_tendsto
