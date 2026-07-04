/-
# q62 — GAP-A Half A: Brolin `f`-invariance from Julia-nullity, via the uniqueness engine

`f_*gapAMu = gapAMu` (Brolin invariance) reduced to the single input `volume(filledJulia c) = 0`.
Mechanism: off `K_c`, both `gapAMu` and the shifted compactness cluster represent `−G_c`
(`green_eq_neg_logPotential_..._on_basin`); with `K_c` Lebesgue-null these potentials agree a.e., so
`measure_eq_of_neg_logPotential_ae_eq` (Q62MeasureUniqueness) forces `gapAMu = shiftedLimitingBrolinMeasure`,
and the tree's pushforward identity `map_shiftedLimitingBrolinMeasure_quadratic_eq_gapAMu` closes it.
Combined with the unconditional atomlessness (Q62FrostmanDomination), this feeds Codex's
`BrolinScalingAt_of_map_quadratic_unconditional` — Half A's doubling law — modulo `volume(K_c)=0`.
-/
import GaloisForLFunctions.Bottcher.Q62MeasureUniqueness
import GaloisForLFunctions.Bottcher.Brolin
open MeasureTheory Complex Filter Metric Set
namespace Bottcher
noncomputable section

theorem map_quadratic_gapAMu_eq_of_volume_filledJulia_zero {c : ℂ}
    (hvol : volume (filledJulia c) = 0) :
    Measure.map (quadratic c) (gapAMu c) = gapAMu c := by
  haveI : IsProbabilityMeasure (gapAMu c) := (gapAMu_isProbOn_filledJulia c).1
  haveI : IsProbabilityMeasure (shiftedLimitingBrolinMeasure c) :=
    (shiftedLimitingBrolinMeasure_isProbOn_filledJulia c).1
  have hgapshift : gapAMu c = shiftedLimitingBrolinMeasure c := by
    refine measure_eq_of_neg_logPotential_ae_eq (A := max 2 ‖c‖) (B := max 2 ‖c‖) ?_ ?_ ?_
    · exact measure_mono_null (compl_subset_compl.mpr (filledJulia_subset_closedBall c))
        (gapAMu_isProbOn_filledJulia c).2
    · exact measure_mono_null (compl_subset_compl.mpr (filledJulia_subset_closedBall c))
        (shiftedLimitingBrolinMeasure_isProbOn_filledJulia c).2
    · have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ filledJulia c := by
        rw [ae_iff]; simpa using hvol
      filter_upwards [hae] with z hz
      show - logPotential (gapAMu c) z = - logPotential (shiftedLimitingBrolinMeasure c) z
      rw [← green_eq_neg_logPotential_gapAMu_on_basin hz,
          ← green_eq_neg_logPotential_shiftedLimitingBrolinMeasure_on_basin hz]
  rw [hgapshift, map_shiftedLimitingBrolinMeasure_quadratic_eq_gapAMu]
  exact hgapshift

end
end Bottcher
