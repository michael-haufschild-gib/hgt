import GaloisForLFunctions.RHTower.Suzuki.SuzukiOrientedPrunedPathChronology

/-!
# Boundary-excursion factorization of pruned Suzuki chronology

Ambient Suzuki seam translations commute.  This module identifies the exact and only location at
which strict-aperture compression can create ordered source history: a two-step path which leaves
the retained aperture through `P - 1` and returns.  The physical `2,3,7` certificate proves that
the resulting antisymmetrized boundary-excursion channel is nonzero.

This is a source-side factorization.  It does not construct a landing into Route P, does not
bound the completed prime current, and does not claim RH.
-/

open Complex Set ContinuousLinearMap
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- The ordered aperture-boundary excursion: start retained, translate by `δ`, pass through the
excluded seam complement, translate by `η`, and return retained. -/
def suzukiPrunedBoundaryExcursion
    (a : ℝ) (δ η : SuzukiSeamValuation) :
    SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert :=
  let P := lpCoordinateProjection (suzukiAdmissibleSeamVertices a)
  P ∘L (suzukiSeamShift δ : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert) ∘L
    (P - 1) ∘L (suzukiSeamShift η : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert) ∘L P

/-- In an idempotent compression of two commuting operators, every compressed commutator is the
antisymmetrized pair of excursions through the complementary defect `P - 1`. -/
private theorem compressed_commutator_eq_boundary_excursions
    {A : Type*} [Ring A] {P U V : A}
    (hP : P * P = P) (hUV : U * V = V * U) :
    (P * U * P) * (P * V * P) - (P * V * P) * (P * U * P) =
      P * U * (P - 1) * V * P - P * V * (P - 1) * U * P := by
  calc
    (P * U * P) * (P * V * P) - (P * V * P) * (P * U * P) =
        P * U * (P * P) * V * P - P * V * (P * P) * U * P := by
          noncomm_ring
    _ = P * U * P * V * P - P * V * P * U * P := by rw [hP]
    _ = (P * U * P * V * P - P * V * P * U * P) -
        (P * U * V * P - P * V * U * P) := by
          have hPUV : P * U * V * P = P * V * U * P := by
            calc
              P * U * V * P = P * (U * V) * P := by noncomm_ring
              _ = P * (V * U) * P := by rw [hUV]
              _ = P * V * U * P := by noncomm_ring
          rw [hPUV]
          noncomm_ring
    _ = P * U * (P - 1) * V * P - P * V * (P - 1) * U * P := by
          noncomm_ring

/-- Exact factorization of every oriented strict-aperture chronology defect.  It identifies the
commutator with the two possible excluded-intermediate-vertex excursions, before any scalar
Eulerian aggregation. -/
theorem suzukiPrunedCompression_commutator_eq_boundaryExcursion
    (a : ℝ) (δ η : SuzukiSeamValuation) :
    suzukiOrientedSupportPrunedShift a δ ∘L
        suzukiOrientedSupportPrunedShift a η -
      suzukiOrientedSupportPrunedShift a η ∘L
        suzukiOrientedSupportPrunedShift a δ =
      suzukiPrunedBoundaryExcursion a δ η -
        suzukiPrunedBoundaryExcursion a η δ := by
  let P : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert :=
    lpCoordinateProjection (suzukiAdmissibleSeamVertices a)
  let U : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert := suzukiSeamShift δ
  let V : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert := suzukiSeamShift η
  have hP : P * P = P := by
    exact lpCoordinateProjection_idempotent _
  have hUV : U * V = V * U := by
    exact suzukiSeamShift_comp_commute δ η
  change (P * U * P) * (P * V * P) - (P * V * P) * (P * U * P) =
    P * U * (P - 1) * V * P - P * V * (P - 1) * U * P
  exact compressed_commutator_eq_boundary_excursions hP hUV

/-- Strict-aperture oriented shifts commute exactly when their two boundary-excursion ports agree.
Thus boundary excursion is a complete obstruction to two-letter source chronology. -/
theorem suzukiPrunedCompression_commute_iff_boundaryExcursion_eq
    (a : ℝ) (δ η : SuzukiSeamValuation) :
    suzukiOrientedSupportPrunedShift a δ ∘L
        suzukiOrientedSupportPrunedShift a η =
      suzukiOrientedSupportPrunedShift a η ∘L
        suzukiOrientedSupportPrunedShift a δ ↔
      suzukiPrunedBoundaryExcursion a δ η =
        suzukiPrunedBoundaryExcursion a η δ := by
  constructor
  · intro hcomm
    apply sub_eq_zero.mp
    rw [← suzukiPrunedCompression_commutator_eq_boundaryExcursion]
    exact sub_eq_zero.mpr hcomm
  · intro hexcursion
    apply sub_eq_zero.mp
    rw [suzukiPrunedCompression_commutator_eq_boundaryExcursion]
    exact sub_eq_zero.mpr hexcursion

/-- The literal physical `2,3,7` aperture has a nonzero antisymmetrized boundary-excursion
channel.  Hence source chronology is carried by an actual excluded-vertex port, not a merely
formal possible defect. -/
theorem exists_suzukiPrunedBoundaryExcursion_skew_nonzero :
    ∃ (a : ℝ) (δ η : SuzukiSeamValuation), 0 < a ∧
      suzukiPrunedBoundaryExcursion a δ η -
        suzukiPrunedBoundaryExcursion a η δ ≠ 0 := by
  obtain ⟨a, δ, η, ha, hne⟩ :=
    exists_suzukiOrientedSupportPrunedShift_noncommuting
  refine ⟨a, δ, η, ha, ?_⟩
  intro hzero
  apply hne
  apply sub_eq_zero.mp
  rw [suzukiPrunedCompression_commutator_eq_boundaryExcursion]
  exact hzero

end GaloisForLFunctions.RHTower
