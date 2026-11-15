import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovCoveringRange
import GaloisForLFunctions.BiarithmeticGeometry.Affine.IntegerGridApproximation

/-!
# A finite corrected covering of the unit moment manifold

The inverse physical shear coordinate lies in `[-(r+1),1]`. Sampling its
scaled integer part gives a finite covering with unit-bounded frame
coordinates. The number of centers is bounded by a constant times the
inverse scale; enlarging the center range therefore preserves that exponent.
-/

open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
open GaloisForLFunctions.BiarithmeticGeometry.IntegerWindowCounts

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- Integer centers large enough to cover the inverse shear of the physical unit cube. -/
def dimensionCoveringGrid (r q : ℕ) (ε : ℝ) : Finset ℤ :=
  integerWindow 0 ((q + 1 : ℝ) * ((r + 1 : ℕ) : ℝ) / |ε| + 1)

/-- Every unit-cube moment has a sampled frame representation inside the unit coordinate cube. -/
theorem exists_dimensionGrid_unitFrame (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ u : Fin (r + 1) → ℝ) (z : ℝ)
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1) (hθ : ∀ i, 0 ≤ ε * δ i ∧ ε * δ i ≤ 1)
    (hz : 0 ≤ z ∧ z ≤ 1) :
    ∃ i ∈ dimensionCoveringGrid r q ε, ∃ x ∈ centeredCube (0 : AffineAxisSpace r k) 1,
      horizontalMoment r k 0 (ε * (i : ℝ) / (q + 1 : ℝ)) +
        Matrix.toLin' (scaledAffineMatrix r k ε δ (ε * (i : ℝ) / (q + 1 : ℝ))) x =
          horizontalMoment r k u z := by
  have ht := selected_center_mem_dimension_interval r ε δ u z hu hθ hz
  have hdim : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by norm_cast; omega
  have habs : |z - ε * ∑ i, δ i * u i| ≤ ((r + 1 : ℕ) : ℝ) :=
    abs_le.mpr ⟨ht.1, ht.2.trans hdim⟩
  obtain ⟨i, hi, w, hw0, hw1, he⟩ := exists_scaled_integer_cell_in_window q ε hε
    (z - ε * ∑ i, δ i * u i) ((r + 1 : ℕ) : ℝ) habs
  refine ⟨i, hi, horizontalMoment r k u w, ?_, ?_⟩
  · exact horizontalMoment_mem_unitCube r k u w
      (fun j => by rw [abs_of_nonneg (hu j).1]; exact (hu j).2)
      (by rw [abs_of_nonneg hw0]; exact hw1)
  · rw [scaledAffine_momentCenteredFrame_moment]
    congr 1
    linarith only [he]

/-- The explicit finite grid covers every moment of the full physical unit cube. -/
theorem exists_dimensionGrid_momentCoveringBox (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ u : Fin (r + 1) → ℝ) (z : ℝ)
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1) (hθ : ∀ i, 0 ≤ ε * δ i ∧ ε * δ i ≤ 1)
    (hz : 0 ≤ z ∧ z ≤ 1) :
    ∃ i ∈ dimensionCoveringGrid r q ε,
      horizontalMoment r k u z ∈
        momentCoveringBox r k ε δ (ε * (i : ℝ) / (q + 1 : ℝ)) := by
  obtain ⟨i, hi, x, hx, he⟩ := exists_dimensionGrid_unitFrame r k q ε hε δ u z hu hθ hz
  refine ⟨i, hi, x, ?_, he⟩
  rw [mem_centeredCube_iff] at hx ⊢
  exact fun a => (hx a).trans (by norm_num)

/-- The corrected finite grid has inverse-scale size, with an explicit additive rounding term. -/
theorem card_dimensionCoveringGrid_le (r q : ℕ) (ε : ℝ) :
    ((dimensionCoveringGrid r q ε).card : ℝ) ≤
      2 * (q + 1 : ℝ) * ((r + 1 : ℕ) : ℝ) / |ε| + 3 := by
  have hR : 0 ≤ (q + 1 : ℝ) * ((r + 1 : ℕ) : ℝ) / |ε| + 1 := by positivity
  exact (card_integerWindow_le 0 _ hR).trans_eq (by ring)

#print axioms exists_dimensionGrid_unitFrame
#print axioms exists_dimensionGrid_momentCoveringBox
#print axioms card_dimensionCoveringGrid_le

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
