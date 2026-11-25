import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost.CriticalLaplace
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints.SectorPressure

/-! # Laplace principle for the ordered energies at fixed occupation count -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost

open Set Filter Topology MeasureTheory Endpoints

theorem tiltedObservable_continuousOn {c d β : ℝ} {k : ℕ} {F : (Fin k → ℝ) → ℝ}
    (hF : ContinuousOn F (orderedBand c d k)) :
    ContinuousOn (tiltedObservable β F) (orderedBand c d k) := by
  have hs : Continuous (fun v : Fin k → ℝ => ∑ i, v i) :=
    continuous_finsetSum Finset.univ fun i _ => continuous_apply i
  exact hF.add (hs.continuousOn.const_mul (1-β))

/-- For every observable continuous on the ordered band, the conditional exponential reading is
governed by its tilted maximum minus the sector pressure. -/
theorem laplace_principle {c d : ℝ} (hc : 0 < c) (hcd : c < d) (β : ℝ) {k : ℕ} (hk : 0 < k)
    {F : (Fin k → ℝ) → ℝ} (hF : ContinuousOn F (orderedBand c d k)) :
    Tendsto (fun h : Ioi (0:ℝ) => h.val*Real.log (∫ v, Real.exp (F v/h.val) ∂(thermalLaw c d h β k : Measure _)))
      criticalApproach (𝓝 (peak c d (tiltedObservable β F)-pressure c d k β)) := by
  have H := (critical_laplace hc hcd (tiltedObservable_continuousOn (β := β) hF)).sub (pressure_limit hc hcd β hk)
  apply H.congr'
  filter_upwards [eventually_positive hc hcd β F] with h hp
  let S := added c d h
  let I := ∫ v, Real.exp (F v/h.val) ∂(thermalLaw c d h β k : Measure _)
  have he : I = partitionWith S β h F/coefficient S β k :=
    (eq_div_iff hp.1.ne').mpr ((mul_comm _ _).trans (partitionWith_eq c d β h F).symm)
  change h.val*Real.log (partitionWith S 1 h (tiltedObservable β F))-h.val*Real.log (coefficient S β k) =
    h.val*Real.log I
  rw [he,Real.log_div hp.2.ne' hp.1.ne',← partitionWith_tilt,mul_sub]

#print axioms tiltedObservable_continuousOn
#print axioms laplace_principle

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost
