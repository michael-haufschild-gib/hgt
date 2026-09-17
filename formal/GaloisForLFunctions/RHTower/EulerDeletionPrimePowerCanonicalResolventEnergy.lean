import GaloisForLFunctions.RHTower.EulerDeletionCanonicalClockResolvent
import GaloisForLFunctions.RHTower.EulerDeletionPrimePowerLayerSupport

/-!
# Prime-power canonical-resolvent energy for Euler deletion

The literal physical EDQ energy is exactly a sum over prime-power chronology
steps. Each retained fibre square is the difference of two finite beta
resolvents of the complete signed paired Möbius source, minus its local
innovation. This is the direct signed cancellation target for the remaining
cofinal energy bound.
-/

noncomputable section

open Finset

namespace RHTower.DeletionResidueMartingale

/-- Exact canonical-resolvent form of one genuine chronological fibre energy. -/
theorem historyLayer_predictableDrift_norm_sq_eq_canonicalBetaResolvent_fibre_energy
    (l N : ℕ) (hlN : l < N) :
    ‖historyLayer l (predictableDrift N)‖ ^ 2 =
      ∑ r ∈ range (clock (l + 1)),
        cellMeasure.real (historyFibre (l + 1) r) *
          (canonicalBetaResolvent N (l + 1) r -
            canonicalBetaResolvent N l (r % clock l) - signedInnovation l r) ^ 2 := by
  rw [historyLayer_predictableDrift_norm_sq_eq_reverse_tail_fibre_energy]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  have htail :
      (∑ i ∈ range N, if l < i then
        ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) *
          (weightedResidueQuotient (i + 1) (l + 1) r -
            weightedResidueQuotient (i + 1) l (r % clock l)) else 0) =
        (historyLayer l (predictableDrift N)) r := by
    simpa only [Nat.mod_eq_of_lt (Finset.mem_range.mp hr)] using
      (historyLayer_predictableDrift_apply_eq_reverse_tail_quotient_difference l N r).symm
  rw [htail,
    historyLayer_predictableDrift_apply_eq_canonicalBetaResolvent_sub_innovation l N r hlN]
  rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]

/-- Fully source-faithful prime-power EDQ energy. Every retained square contains its complete
finite signed Möbius resolvent difference; no positivity, averaging, or componentwise bound has
been introduced. -/
theorem predictableDrift_norm_sq_eq_primePower_canonicalBetaResolvent_energy (N : ℕ) :
    ‖predictableDrift N‖ ^ 2 =
      ‖(historySpace 0).starProjection (predictableDrift N)‖ ^ 2 +
        ∑ l ∈ (range N).filter (fun l => IsPrimePow (l + 1)),
          ∑ r ∈ range (clock (l + 1)),
            cellMeasure.real (historyFibre (l + 1) r) *
              (canonicalBetaResolvent N (l + 1) r -
                canonicalBetaResolvent N l (r % clock l) - signedInnovation l r) ^ 2 := by
  rw [predictableDrift_norm_sq_eq_historyLayer_sum,
    predictableDrift_historyLayer_energy_eq_primePower_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [historyLayer_predictableDrift_norm_sq_eq_canonicalBetaResolvent_fibre_energy l N
    (Finset.mem_range.mp (Finset.mem_of_mem_filter l hl))]

end RHTower.DeletionResidueMartingale
