import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Moments
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Vacuum

/-! # Joint scaling limit of the retained energy and its new prime band -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands

open Filter Topology Set MeasureTheory ProbabilityTheory _root_.RHTower _root_.RHTower.BAGTrace

/-- The finite packet converges at every complex probe to the transform of the Poisson sum. -/
theorem band_transform_limit {c d : ℝ} (hc : 0 < c) (hcd : c < d) (z : ℂ) :
    Tendsto (fun h => packetMoment (added c d h) h z) criticalApproach
      (𝓝 (complexMGF id (increment c d hc hcd : Measure ℝ) z)) := by
  have hlow := conditioned_transform_limit hc z
  have H := (conditioned_transform_limit (hc.trans hcd) z).div hlow (transform_ne_zero c z)
  rw [factor_transform hc hcd.le,mul_div_cancel_left₀ _ (transform_ne_zero c z)] at H
  rw [increment_mgf hc hcd]
  apply H.congr'
  filter_upwards [hlow.eventually_ne (transform_ne_zero c z)] with h hn
  change momentProbe d h 0 z/momentProbe c h 0 z = packetMoment (added c d h) h z
  rw [finite_factor hcd.le,mul_div_cancel_left₀ _ hn]

theorem band_weak_limit {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    Tendsto (fun h => packetLaw (added c d h) h) criticalApproach (𝓝 (increment c d hc hcd)) := by
  rw [tendsto_iff_seq_tendsto]
  intro u hu
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  rw [charFun_increment,← increment_mgf hc hcd]
  exact ((band_transform_limit hc hcd ((t:ℂ)*Complex.I)).congr
    (fun h => (packet_charFun (added c d h) h t).symm)).comp hu

/-- Both observables are measured on one finite orientation. Their joint limit has independent marginals. -/
theorem joint_weak_limit {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    Tendsto (jointEnergyLaw hcd.le) criticalApproach
      (𝓝 ((cutoffLaw c).prod (increment c d hc hcd))) := by
  have H := ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp
    ((conditioned_weak_limit hc).prodMk_nhds (band_weak_limit hc hcd))
  exact H.congr fun h => (joint_exact_product hcd.le h).symm

#print axioms band_transform_limit
#print axioms band_weak_limit
#print axioms joint_weak_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands
