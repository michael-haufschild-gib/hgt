import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFixedPropagatorGlobalRigidity
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMUniversalSkewPropagatorClassification

/-!
# HB arbitrary-skew fixed-propagator global rigidity

The universal-carrier classification reduces every complex-linear skew propagator to one target-
scaled symplectic rotation.  Therefore existence of any fixed skew propagator realizing every
unit-seed BM incidence is equivalent to RH.  Hardy's critical-line anchor excludes every nonzero
fixed skew propagator unconditionally.

This closes the arbitrary two-dimensional skew-carrier loophole.  Remaining HB producer must
construct a fixed propagator from literal augmented Einstein--Teukolsky dynamics; changing the
abstract skew map cannot bypass global compatibility.

`[NEW] [GLOBAL RIGIDITY] [NO-GO] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Existence of an arbitrary fixed skew propagator realizing all unit-seed BM incidences is
equivalent to RH. -/
theorem exists_hbUniversalPeierls_fixedSkewPropagator_unit_BM_incidence_iff_rh
    (n : ℕ) :
    (∃ Delta : HBUniversalPeierlsCarrier →ₗ[ℂ] HBUniversalPeierlsCarrier,
      (∀ f g : HBUniversalPeierlsCarrier,
        d4GaugeFixedTeukolskyPeierlsSourcePairing hbUniversalPeierlsPairing Delta f g =
          -d4GaugeFixedTeukolskyPeierlsSourcePairing hbUniversalPeierlsPairing Delta g f) ∧
      ∀ q : XiZeroCopy,
        d4GaugeFixedTeukolskyPeierlsSourcePairing hbUniversalPeierlsPairing Delta
            (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual
              hbUniversalPeierlsQuadraticResidual hbUniversalPeierlsPlusBranch)
            (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual
              hbUniversalPeierlsQuadraticResidual hbUniversalPeierlsMinusBranch) =
          d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q) ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨Delta, hskew, hincidence⟩
    let T := (Delta (1, 0)).2
    have hDelta : Delta = hbUniversalPeierlsPropagator T :=
      hbUniversalPeierls_skewPropagator_eq_targetScaledRotation Delta hskew
    apply (exists_hbUniversalPeierls_fixedPropagator_unit_BM_incidence_iff_rh n).mp
    refine ⟨T, ?_⟩
    intro q
    rw [← hDelta]
    exact hincidence q
  · intro hRH
    obtain ⟨T, hincidence⟩ :=
      (exists_hbUniversalPeierls_fixedPropagator_unit_BM_incidence_iff_rh n).mpr hRH
    exact ⟨hbUniversalPeierlsPropagator T,
      hbUniversalPeierlsSourcePairing_skew T, hincidence⟩

/-- No nonzero fixed skew propagator can realize all unit-seed BM incidences. -/
theorem not_exists_hbUniversalPeierls_nonzero_fixedSkewPropagator_unit_BM_incidence
    (n : ℕ) :
    ¬ ∃ Delta : HBUniversalPeierlsCarrier →ₗ[ℂ] HBUniversalPeierlsCarrier,
      Delta ≠ 0 ∧
      (∀ f g : HBUniversalPeierlsCarrier,
        d4GaugeFixedTeukolskyPeierlsSourcePairing hbUniversalPeierlsPairing Delta f g =
          -d4GaugeFixedTeukolskyPeierlsSourcePairing hbUniversalPeierlsPairing Delta g f) ∧
      ∀ q : XiZeroCopy,
        d4GaugeFixedTeukolskyPeierlsSourcePairing hbUniversalPeierlsPairing Delta
            (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual
              hbUniversalPeierlsQuadraticResidual hbUniversalPeierlsPlusBranch)
            (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual
              hbUniversalPeierlsQuadraticResidual hbUniversalPeierlsMinusBranch) =
          d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q := by
  rintro ⟨Delta, hDeltaNonzero, hskew, hincidence⟩
  let T := (Delta (1, 0)).2
  have hDelta : Delta = hbUniversalPeierlsPropagator T :=
    hbUniversalPeierls_skewPropagator_eq_targetScaledRotation Delta hskew
  have hscalarIncidence : ∀ q : XiZeroCopy,
      d4GaugeFixedTeukolskyPeierlsSourcePairing hbUniversalPeierlsPairing
          (hbUniversalPeierlsPropagator T)
          (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual
            hbUniversalPeierlsQuadraticResidual hbUniversalPeierlsPlusBranch)
          (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual
            hbUniversalPeierlsQuadraticResidual hbUniversalPeierlsMinusBranch) =
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q := by
    intro q
    rw [← hDelta]
    exact hincidence q
  have hTzero : T = 0 := by
    by_contra hT
    exact not_exists_hbUniversalPeierls_nonzero_fixedPropagator_unit_BM_incidence n
      ⟨T, hT, hscalarIncidence⟩
  apply hDeltaNonzero
  rw [hDelta, hTzero]
  apply LinearMap.ext
  intro f
  ext <;> simp [hbUniversalPeierlsPropagator]

end

end RHTower
