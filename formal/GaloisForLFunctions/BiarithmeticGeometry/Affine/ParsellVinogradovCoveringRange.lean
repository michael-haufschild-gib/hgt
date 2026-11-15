import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovBoxSeparation

/-!
# A dimension-dependent center interval covers the unit moment manifold

The inverse physical shear sends the unit cube into vertical coordinates
between minus the horizontal dimension and one. Centering at that inverse
coordinate gives an exact frame representation with unit-bounded moment
coordinates. This supplies a continuous covering interval in every degree.
-/

open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- Every monomial is unit-bounded when its physical coordinates are unit-bounded. -/
theorem abs_canonicalMoment_le_one (r k : ℕ) (x : Fin (r + 2) → ℝ)
    (hx : ∀ i, |x i| ≤ 1) (a : AffineAxisIndex r k) :
    |canonicalMoment r k x a| ≤ 1 := by
  rw [canonicalMoment_product, Finset.abs_prod]
  simp only [abs_pow]
  exact Finset.prod_le_one (fun i _ => pow_nonneg (abs_nonneg (x i)) _)
    (fun i _ => pow_le_one₀ (abs_nonneg (x i)) (hx i))

/-- The physical unit cube maps into the unit cube of moment coordinates. -/
theorem horizontalMoment_mem_unitCube (r k : ℕ) (u : Fin (r + 1) → ℝ) (z : ℝ)
    (hu : ∀ i, |u i| ≤ 1) (hz : |z| ≤ 1) :
    horizontalMoment r k u z ∈ centeredCube 0 1 := by
  rw [mem_centeredCube_iff]
  intro a
  simp only [Pi.zero_apply, sub_zero, horizontalMoment]
  apply abs_canonicalMoment_le_one
  intro i
  exact Fin.cases hz hu i

/-- The centered scaled frame transports physical moments by the corresponding affine shear. -/
theorem scaledAffine_momentCenteredFrame_moment (r k : ℕ) (ε : ℝ)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) (u : Fin (r + 1) → ℝ) (z : ℝ) :
    horizontalMoment r k 0 t +
      Matrix.toLin' (scaledAffineMatrix r k ε δ t) (horizontalMoment r k u z) =
        horizontalMoment r k u (t + ε * (z + ∑ i, δ i * u i)) := by
  rw [scaledAffineLinear_apply]
  simp only [Matrix.toLin'_apply,
    verticalDilationMatrix_moment, vectorAffineMatrix_moment]
  have hs : (∑ i, (ε • δ) i * u i) = ε * ∑ i, δ i * u i := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [hs, show ε * z + ε * ∑ i, δ i * u i + t =
    t + ε * (z + ∑ i, δ i * u i) by ring]
  abel_nf

/-- Centering at the inverse shear coordinate places the moment in a covering box. -/
theorem horizontalMoment_mem_selected_center (r k : ℕ) (ε : ℝ)
    (δ u : Fin (r + 1) → ℝ) (z : ℝ) (hu : ∀ i, |u i| ≤ 1) :
    horizontalMoment r k u z ∈
      momentCoveringBox r k ε δ (z - ε * ∑ i, δ i * u i) := by
  change _ ∈ (fun x => horizontalMoment r k 0 (z - ε * ∑ i, δ i * u i) +
    Matrix.toLin' (scaledAffineMatrix r k ε δ (z - ε * ∑ i, δ i * u i)) x) ''
      centeredCube 0 2
  refine ⟨horizontalMoment r k u 0, ?_, ?_⟩
  · have h := horizontalMoment_mem_unitCube r k u 0 hu (by norm_num)
    rw [mem_centeredCube_iff] at h ⊢
    exact fun a => (h a).trans (by norm_num)
  · dsimp only
    rw [scaledAffine_momentCenteredFrame_moment]
    congr 1
    ring

/-- A shear with physical coefficients in the unit interval has inverse vertical range `[-(r+1),1]`. -/
theorem selected_center_mem_dimension_interval (r : ℕ) (ε : ℝ)
    (δ u : Fin (r + 1) → ℝ) (z : ℝ)
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1) (hθ : ∀ i, 0 ≤ ε * δ i ∧ ε * δ i ≤ 1)
    (hz : 0 ≤ z ∧ z ≤ 1) :
    z - ε * ∑ i, δ i * u i ∈ Set.Icc (-((r + 1 : ℕ) : ℝ)) 1 := by
  have he : ε * ∑ i, δ i * u i = ∑ i, (ε * δ i) * u i := by
    simp only [Finset.mul_sum, mul_assoc]
  have hl : 0 ≤ ∑ i, (ε * δ i) * u i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hθ i).1 (hu i).1)
  have hh : (∑ i, (ε * δ i) * u i) ≤ ((r + 1 : ℕ) : ℝ) := by
    calc
      _ ≤ ∑ _ : Fin (r + 1), (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => mul_le_one₀ (hθ i).2 (hu i).1 (hu i).2)
      _ = _ := by simp
  rw [he]
  exact ⟨by linarith only [hz.1, hh], by linarith only [hz.2, hl]⟩

/-- The full physical unit cube admits moment boxes centered in the dimension-dependent interval. -/
theorem exists_dimension_interval_momentCoveringBox (r k : ℕ) (ε : ℝ)
    (δ u : Fin (r + 1) → ℝ) (z : ℝ)
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1) (hθ : ∀ i, 0 ≤ ε * δ i ∧ ε * δ i ≤ 1)
    (hz : 0 ≤ z ∧ z ≤ 1) :
    ∃ t ∈ Set.Icc (-((r + 1 : ℕ) : ℝ)) 1,
      horizontalMoment r k u z ∈ momentCoveringBox r k ε δ t := by
  refine ⟨z - ε * ∑ i, δ i * u i,
    selected_center_mem_dimension_interval r ε δ u z hu hθ hz, ?_⟩
  exact horizontalMoment_mem_selected_center r k ε δ u z
    (fun i => by rw [abs_of_nonneg (hu i).1]; exact (hu i).2)

#print axioms abs_canonicalMoment_le_one
#print axioms horizontalMoment_mem_unitCube
#print axioms scaledAffine_momentCenteredFrame_moment
#print axioms horizontalMoment_mem_selected_center
#print axioms selected_center_mem_dimension_interval
#print axioms exists_dimension_interval_momentCoveringBox

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
