import GaloisForLFunctions.RHTower.ConstrainedProlateBesselBound
import GaloisForLFunctions.RHTower.ConstrainedProlateClockRawDefectUniversalityLaw

/-!
# Constrained-Prolate Bessel/clock universality

The actual signed-Prolate constraint coordinates automatically satisfy the two global analytic
hypotheses of the clock-universal CCM law: squared summability and the aperture Bessel bound.
Thus only finitely many coordinate limits remain before every depth has an eventual exact
eigenpair and all preceding normalized raw defects collapse.
-/

open Filter Set

namespace RHTower

noncomputable section

/-- **Constrained-Prolate Bessel/clock universality law.**  For every ladder envelope, the true
signed-Prolate constraint magnitudes need only satisfy their finitely many depth-coordinate
limits. Bessel geometry then supplies all infinite-dimensional hypotheses of the exact
eigenpair/raw-defect theorem. -/
theorem LadderEnvelope.constrainedProlateBessel_exactEigenpair_and_allRawDefects
    {D : ℝ → ℕ → ℝ}
    (h : LadderEnvelope D) (k : ℕ)
    (hl : ∀ j, j ≤ k + 1 →
      Tendsto (fun lam => ‖evenProlateConstraintCoord lam j‖) atTop
        (nhds (constrainedProlateHermiteCoordinate j))) :
    let ℓ : ℝ → ℕ → ℝ := fun lam j => ‖evenProlateConstraintCoord lam j‖
    (∀ᶠ lam in atTop,
      depthSecularRoot (D lam) (ℓ lam) k ∈ Ioo (D lam k) (D lam (k + 1)) ∧
      depthSecular (D lam) (ℓ lam) k (depthSecularRoot (D lam) (ℓ lam) k) = 0 ∧
      (∑' j : ℕ,
        ℓ lam j * secularVector (D lam) (ℓ lam)
          (depthSecularRoot (D lam) (ℓ lam) k) j) = 0 ∧
      secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) ≠ 0) ∧
    ∀ m, m ≤ k →
      Tendsto (fun lam =>
        (secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) m * ℓ lam 0
          - secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0 * ℓ lam m)
          / (secularVector (D lam) (ℓ lam) (depthSecularRoot (D lam) (ℓ lam) k) 0
              * ℓ lam 0)) atTop (nhds 0) := by
  dsimp only
  apply h.ccm_depth_exactEigenpair_and_allRawDefects k
  · exact Eventually.of_forall fun lam =>
      summable_evenProlateConstraintCoord_sq lam
  · exact evenProlate_bessel_eventually
  · exact hl

end

end RHTower
