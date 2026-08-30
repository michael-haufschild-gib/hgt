import GaloisForLFunctions.RHTower.FrankensteinEulerMobiusSharedWardTraceBridge
import GaloisForLFunctions.RHTower.SoninCofinalMobiusGammaXiIncidence

/-!
# Euler--Möbius--Sonin critical-normal shared Ward bridge

The cofinal Sonin normal coordinate tends to the critical wall while the
literal completed trace remains at a fixed safe Euler target.  This is a
pre-divisor source merger, not an assertion at the critical target itself.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- **Three-source critical-normal Ward producer.** At the fixed safe Euler target `2`, one
literal source theorem retains strict Euler Ward order and Hedenmalm curvature, bilateral
strict-lower Möbius orientations, and a cofinal Sonin transport whose normal coordinate tends to
`1` from above.  The normal/tangential pair preserves target `2` identically, and all three
sources land in its same completed prime--Gamma trace before Xi-divisor selection.

This does not identify the singular target `1`, select an Xi divisor, or prove RH. -/
theorem eulerAffineMobiusSonin_criticalNormalSharedWard_producer
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c) :
    ∃ depth : ℕ → ℕ, StrictMono depth ∧
      Tendsto (fixedEulerCofinalSigma 2) atTop (𝓝[>] (1 : ℝ)) ∧
      (∀ n : ℕ,
        mobiusCriticalBoundaryParameter
          (fixedEulerCofinalSigma 2 n) (fixedEulerCofinalDamping n) = 2) ∧
      (0 < (deriv (eulerAffineFisherScore (2 : ℂ) 1) 0).re) ∧
      (deriv HedenmalmThetaSource.squarefreeMobiusCriticalRegularCurrent 1 =
        -deriv (logDeriv zetaResidueUnit) 1 +
          2 * deriv (eulerAffineFisherScore (2 : ℂ) 1) 0) ∧
      (∀ u : ℝ, -(1 / 2 : ℝ) < u →
        Tendsto
          (fun k : ℕ =>
            squarefreeMobiusCofinalReplicaGammaXiWardTransportV (k + 1) 2 u)
          atTop
          (𝓝 (eulerAffineGammaXiWardTransportV (2 : ℂ) 1
            (eulerAffineFisherScore (2 : ℂ) 1) (u : ℂ)))) ∧
      Tendsto (fun n =>
        soninCofinalMobiusGammaXiWardFixedEulerTransport
            a c d r hc hcd hr 2 (by norm_num) depth n -
          eulerAffineGammaXiWardTransportV (2 : ℂ) 1
            (eulerAffineFisherScore (2 : ℂ) 1) 0)
        atTop (𝓝 0) := by
  rcases eulerAffineMobius_sharedCompletedWardTrace_producer with
    ⟨horder, hcurvature, hbilateral⟩
  rcases exists_soninCofinalMobiusGammaXiWardFixedEulerTransport
      a c d r ha hc hcd hda hr harc 2 (by norm_num) with
    ⟨depth, hdepth, hsonin⟩
  refine ⟨depth, hdepth, tendsto_fixedEulerCofinalSigma_nhdsWithin (by norm_num),
    fixedEulerCofinal_boundaryParameter 2, horder, hcurvature, ?_, ?_⟩
  · intro u hu
    exact (hbilateral u hu).2
  · have hshared := (hbilateral 0 (by norm_num : -(1 / 2 : ℝ) < 0)).1
    rw [show eulerAffineGammaXiWardTransportV (2 : ℂ) 1
        (eulerAffineFisherScore (2 : ℂ) 1) 0 =
          continuedPrimeArchSourceRelativeTrace
            (xiWardCenteredCoordinate (2 : ℂ)) by
      simpa [mobiusCriticalBoundaryParameter] using hshared]
    exact hsonin

/-- **All-orientation critical-normal Ward producer.** The preceding common-source bridge is not
confined to its base coordinate.  Every safe retained Möbius orientation has a strictly cofinal
Sonin shell family whose normal coordinate tends to `1` from above while its normal/tangential
product preserves that exact oriented Euler target.  It converges to the same completed trace as
the bilateral Möbius family and the all-Euler Ward transport.

This still stops strictly before the singular target and before Xi-divisor selection. -/
theorem eulerAffineMobiusSonin_allSafeOrientations_criticalNormalSharedWard_producer
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c) :
    (0 < (deriv (eulerAffineFisherScore (2 : ℂ) 1) 0).re) ∧
      (deriv HedenmalmThetaSource.squarefreeMobiusCriticalRegularCurrent 1 =
        -deriv (logDeriv zetaResidueUnit) 1 +
          2 * deriv (eulerAffineFisherScore (2 : ℂ) 1) 0) ∧
      ∀ u : ℝ, ∀ hu : -(1 / 2 : ℝ) < u,
        ∃ depth : ℕ → ℕ, StrictMono depth ∧
          Tendsto (fixedEulerCofinalSigma (2 + u)) atTop (𝓝[>] (1 : ℝ)) ∧
          (∀ n : ℕ,
            mobiusCriticalBoundaryParameter
              (fixedEulerCofinalSigma (2 + u) n)
              (fixedEulerCofinalDamping n) = 2 + u) ∧
          Tendsto
            (fun k : ℕ =>
              squarefreeMobiusCofinalReplicaGammaXiWardTransportV (k + 1) 2 u)
            atTop
            (𝓝 (eulerAffineGammaXiWardTransportV (2 : ℂ) 1
              (eulerAffineFisherScore (2 : ℂ) 1) (u : ℂ))) ∧
          Tendsto (fun n =>
            soninCofinalMobiusGammaXiWardFixedEulerTransport
                a c d r hc hcd hr (2 + u) (by linarith [hu]) depth n -
              eulerAffineGammaXiWardTransportV (2 : ℂ) 1
                (eulerAffineFisherScore (2 : ℂ) 1) (u : ℂ))
            atTop (𝓝 0) := by
  rcases eulerAffineMobius_sharedCompletedWardTrace_producer with
    ⟨horder, hcurvature, hbilateral⟩
  refine ⟨horder, hcurvature, ?_⟩
  intro u hu
  have hs : 1 < 2 + u := by linarith
  rcases exists_soninCofinalMobiusGammaXiWardFixedEulerTransport
      a c d r ha hc hcd hda hr harc (2 + u) hs with
    ⟨depth, hdepth, hsonin⟩
  have hshared := (hbilateral u hu).1
  have hparameter :
      (mobiusCriticalBoundaryParameter 2 u : ℂ) = ((2 + u : ℝ) : ℂ) := by
    norm_num [mobiusCriticalBoundaryParameter]
  refine ⟨depth, hdepth, tendsto_fixedEulerCofinalSigma_nhdsWithin hs,
    fixedEulerCofinal_boundaryParameter (2 + u), (hbilateral u hu).2, ?_⟩
  rw [show eulerAffineGammaXiWardTransportV (2 : ℂ) 1
      (eulerAffineFisherScore (2 : ℂ) 1) (u : ℂ) =
        continuedPrimeArchSourceRelativeTrace
          (xiWardCenteredCoordinate ((2 + u : ℝ) : ℂ)) by
    rw [hparameter] at hshared
    exact hshared]
  exact hsonin

end

end RHTower
