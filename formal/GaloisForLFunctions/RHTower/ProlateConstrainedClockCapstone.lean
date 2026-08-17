import GaloisForLFunctions.RHTower.ProlateConstraintCoordinateLimit
import GaloisForLFunctions.RHTower.ConstrainedProlateBesselClockUniversalityLaw

/-!
# The constrained-prolate clock law with no coordinate hypothesis

The Bessel/clock universality law carries one remaining hypothesis: the finitely many coordinate
limits `‖ℓ_j(lam)‖ → a_j`.  On the Fourier-even renumbering `j ↦ 2j` those limits are theorems, so
the law holds with no analytic hypothesis about the prolate coordinates at all — only the clock
envelope of the leakage ladder remains.

The renumbering costs nothing: squared summability passes to a subfamily, and the aperture Bessel
bound is already proved for an arbitrary injective renumbering.
-/

open Filter Set

namespace RHTower

noncomputable section

theorem injective_two_mul : Function.Injective (fun j : ℕ => 2 * j) := by
  intro i j hij
  simpa using hij

/-- **The constrained-prolate clock law, with the coordinate limits discharged.**  Every clock
envelope yields, for the Fourier-even constraint coordinates, an eventual exact eigenpair at each
depth and the collapse of all preceding normalized raw defects — unconditionally. -/
theorem LadderEnvelope.constrainedProlateEven_exactEigenpair_and_allRawDefects
    {D : ℝ → ℕ → ℝ}
    (h : LadderEnvelope D) (k : ℕ) :
    let ℓ : ℝ → ℕ → ℝ := fun lam j => ‖evenProlateConstraintCoord lam (2 * j)‖
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
  · refine Eventually.of_forall fun lam => ?_
    exact (summable_evenProlateConstraintCoord_sq lam).comp_injective injective_two_mul
  · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with lam hlam
    exact tsum_evenProlateConstraintCoord_comp_sq_le hlam injective_two_mul
  · intro j _
    exact tendsto_norm_evenProlateConstraintCoord_atTop j

end

end RHTower
