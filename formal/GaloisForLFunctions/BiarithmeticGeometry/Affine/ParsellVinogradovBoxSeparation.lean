import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovLinearCoordinates
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovCoveringBoxes
import GaloisForLFunctions.BiarithmeticGeometry.Affine.FiniteCoordinateLinearBounds

/-!
# Vertical separation of intersecting moment boxes

Degree-one projection places every moment-centered covering box inside a
physical shear slab. A common point bounds the difference of the two
vertical centers by the vertical scale times a linear function of the
directional separation. The estimate is independent of polynomial degree.
-/

open Matrix
open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
open GaloisForLFunctions.BiarithmeticGeometry.FiniteCoordinateNorms

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- The projected affine image has its physical vertical center and unchanged horizontal coordinates. -/
theorem degreeOneProjection_momentCenteredFrame (r k : ℕ) (ε : ℝ)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) (x : AffineAxisSpace r (k + 1)) :
    degreeOneProjection r k (horizontalMoment r (k + 1) 0 t +
      Matrix.toLin' (scaledAffineMatrix r (k + 1) ε δ t) x) =
        Fin.cons (t + ε * (x (degreeOneIndex r k 0) +
          ∑ i, δ i * x (degreeOneIndex r k i.succ)))
          (fun i => x (degreeOneIndex r k i.succ)) := by
  rw [map_add, degreeOneProjection_moment, degreeOneProjection_scaledAffine]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Pi.add_apply, Fin.cons_zero]
  · simp only [Pi.add_apply, Fin.cons_succ, Pi.zero_apply, zero_add]

/-- Every covering box contains its defining point of the moment manifold. -/
theorem momentCenter_mem_momentCoveringBox (r k : ℕ) (ε : ℝ)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) :
    horizontalMoment r k 0 t ∈ momentCoveringBox r k ε δ t := by
  change _ ∈ (fun x => horizontalMoment r k 0 t +
    Matrix.toLin' (scaledAffineMatrix r k ε δ t) x) '' centeredCube 0 2
  refine ⟨0, ?_, ?_⟩
  · rw [mem_centeredCube_iff]
    intro i
    norm_num
  · simp only [map_zero, add_zero]

/-- Degree-one projection bounds the horizontal coordinates and the vertical shear residual. -/
theorem mem_momentCoveringBox_projection (r k : ℕ) (ε : ℝ)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) (ξ : AffineAxisSpace r (k + 1))
    (hξ : ξ ∈ momentCoveringBox r (k + 1) ε δ t) :
    (∀ i : Fin (r + 1), |degreeOneProjection r k ξ i.succ| ≤ 2) ∧
      |degreeOneProjection r k ξ 0 - t -
        ε * ∑ i, δ i * degreeOneProjection r k ξ i.succ| ≤ 2 * |ε| := by
  change ξ ∈ (fun x => horizontalMoment r (k + 1) 0 t +
    Matrix.toLin' (scaledAffineMatrix r (k + 1) ε δ t) x) '' centeredCube 0 2 at hξ
  rcases hξ with ⟨x, hx, rfl⟩
  rw [degreeOneProjection_momentCenteredFrame]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [mem_centeredCube_iff] at hx
  simp only [Pi.zero_apply, sub_zero] at hx
  refine ⟨fun i => hx (degreeOneIndex r k i.succ), ?_⟩
  rw [show t + ε * (x (degreeOneIndex r k 0) + ∑ i, δ i * x (degreeOneIndex r k i.succ)) -
      t - ε * ∑ i, δ i * x (degreeOneIndex r k i.succ) = ε * x (degreeOneIndex r k 0) by ring,
    abs_mul]
  calc
    _ ≤ |ε| * 2 := mul_le_mul_of_nonneg_left (hx (degreeOneIndex r k 0)) (abs_nonneg ε)
    _ = _ := mul_comm _ _

/-- Intersecting radius-two moment boxes have vertical-center separation controlled by the direction difference. -/
theorem momentCoveringBox_intersection_separation (r k : ℕ) (ε : ℝ)
    (δ η : Fin (r + 1) → ℝ) (t s : ℝ)
    (h : (momentCoveringBox r (k + 1) ε δ t ∩ momentCoveringBox r (k + 1) ε η s).Nonempty) :
    |t - s| ≤ |ε| * (4 + 2 * ∑ i, |(δ - η) i|) := by
  rcases h with ⟨ξ, hδ, hη⟩
  obtain ⟨hu, hδ⟩ := mem_momentCoveringBox_projection r k ε δ t ξ hδ
  obtain ⟨_, hη⟩ := mem_momentCoveringBox_projection r k ε η s ξ hη
  simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using
    abs_shift_sub_le_of_two_strip_bounds δ η (fun i => degreeOneProjection r k ξ i.succ)
      ε t s (degreeOneProjection r k ξ 0) 2 hu hδ hη

/-- Euclidean directional separation gives an explicit bound independent of truncation degree. -/
theorem momentCoveringBox_intersection_euclidean_separation (r k : ℕ) (ε : ℝ)
    (δ η : Fin (r + 1) → ℝ) (t s : ℝ)
    (h : (momentCoveringBox r (k + 1) ε δ t ∩ momentCoveringBox r (k + 1) ε η s).Nonempty) :
    |t - s| ≤ |ε| * (4 + 2 * ((r + 1 : ℕ) : ℝ) * euclideanNorm (δ - η)) := by
  refine (momentCoveringBox_intersection_separation r k ε δ η t s h).trans ?_
  have hs := sum_abs_le_card_mul_euclideanNorm (δ - η)
  have hd : 4 + 2 * ∑ i, |(δ - η) i| ≤
      4 + 2 * ((r + 1 : ℕ) : ℝ) * euclideanNorm (δ - η) := by
    linarith only [hs]
  exact mul_le_mul_of_nonneg_left hd (abs_nonneg ε)

/-- At zero scale, two moment-centered boxes intersect exactly when their vertical centers coincide. -/
theorem momentCoveringBox_zero_intersection_iff (r k : ℕ)
    (δ η : Fin (r + 1) → ℝ) (t s : ℝ) :
    (momentCoveringBox r (k + 1) 0 δ t ∩ momentCoveringBox r (k + 1) 0 η s).Nonempty ↔ t = s := by
  constructor
  · intro h
    have hs := momentCoveringBox_intersection_separation r k 0 δ η t s h
    simp only [abs_zero, zero_mul, abs_nonpos_iff, sub_eq_zero] at hs
    exact hs
  · rintro rfl
    exact ⟨horizontalMoment r (k + 1) 0 t,
      momentCenter_mem_momentCoveringBox r (k + 1) 0 δ t,
      momentCenter_mem_momentCoveringBox r (k + 1) 0 η t⟩

#print axioms degreeOneProjection_momentCenteredFrame
#print axioms momentCenter_mem_momentCoveringBox
#print axioms mem_momentCoveringBox_projection
#print axioms momentCoveringBox_intersection_separation
#print axioms momentCoveringBox_intersection_euclidean_separation
#print axioms momentCoveringBox_zero_intersection_iff

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
