import GaloisForLFunctions.RHTower.EulerAffineHedenmalmWardCurvatureBridge
import GaloisForLFunctions.RHTower.MobiusTwoSidedCofinalReplicaGammaXiSource

/-!
# Euler--Möbius shared completed Ward trace

At the common safe affine coordinate, the literal all-Euler Fisher source supplies strict Ward
order and Hedenmalm pole-curvature incidence, while the bilateral strict-lower Möbius source
supplies both cofinal orientations. This module proves that they land in the *same* completed
prime--Gamma trace before any Xi-divisor selection.

It is a safe-chamber merger, not a critical-boundary theorem: no assertion here identifies the
two source constructions at the singular RH boundary.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- **Shared-gate source merger.** At the literal safe affine coordinate, strict all-Euler Ward
order and Hedenmalm curvature incidence share the same completed prime--Gamma trace with the
bilateral strict-lower Möbius source. Thus one pre-divisor construction retains `ORD`, while the
other retains both `ORIENT` and `COF`; their common trace gives coefficient-free safe `LAND`.
No Xi copy is selected and no critical-boundary statement is asserted. -/
theorem eulerAffineMobius_sharedCompletedWardTrace_producer :
    (0 < (deriv (eulerAffineFisherScore (2 : ℂ) 1) 0).re) ∧
      (deriv HedenmalmThetaSource.squarefreeMobiusCriticalRegularCurrent 1 =
        -deriv (logDeriv zetaResidueUnit) 1 +
          2 * deriv (eulerAffineFisherScore (2 : ℂ) 1) 0) ∧
      (∀ u : ℝ, -(1 / 2 : ℝ) < u →
        eulerAffineGammaXiWardTransportV (2 : ℂ) 1
            (eulerAffineFisherScore (2 : ℂ) 1) (u : ℂ) =
          continuedPrimeArchSourceRelativeTrace
            (xiWardCenteredCoordinate
              (mobiusCriticalBoundaryParameter 2 u : ℂ)) ∧
        Tendsto
          (fun k : ℕ =>
            squarefreeMobiusCofinalReplicaGammaXiWardTransportV (k + 1) 2 u)
          atTop
          (𝓝 (eulerAffineGammaXiWardTransportV (2 : ℂ) 1
            (eulerAffineFisherScore (2 : ℂ) 1) (u : ℂ)))) := by
  rcases eulerAffineHedenmalmWardOrderLanding_producer with
    ⟨horder, hcurvature, hlanding⟩
  refine ⟨horder, hcurvature, ?_⟩
  intro u hu
  have hshift : 1 < ((2 : ℂ) + (u : ℂ) * 1).re := by
    norm_num [Complex.add_re, Complex.mul_re]
    linarith
  have hEuler := hlanding (u : ℂ) hshift
  have hparameter :
      (mobiusCriticalBoundaryParameter 2 u : ℂ) =
        (2 : ℂ) + (u : ℂ) * 1 := by
    norm_num [mobiusCriticalBoundaryParameter]
  have hshared :
      eulerAffineGammaXiWardTransportV (2 : ℂ) 1
          (eulerAffineFisherScore (2 : ℂ) 1) (u : ℂ) =
        continuedPrimeArchSourceRelativeTrace
          (xiWardCenteredCoordinate
            (mobiusCriticalBoundaryParameter 2 u : ℂ)) := by
    rw [hparameter]
    exact hEuler
  refine ⟨hshared, ?_⟩
  rw [hshared]
  exact bilateral_tendsto_squarefreeMobiusCofinalReplicaGammaXiWardTransportV
    (sigma := 2) (u := u) (by norm_num) hu

end

end RHTower
