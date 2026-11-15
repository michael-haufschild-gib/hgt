import GaloisForLFunctions.BiarithmeticGeometry.Affine.FiniteCoordinateNorms

/-!
# Coordinate bounds for physical shear slabs

The Euclidean norm bounds each scalar coordinate, hence also the sum of
absolute coordinates. Bounded horizontal coordinates control a linear
form and the separation of the centers of two shear slabs.
-/

open scoped BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.FiniteCoordinateNorms
noncomputable section

/-- Each scalar coordinate is bounded by the ordinary Euclidean norm. -/
theorem abs_coordinate_le_euclideanNorm {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    |v i| ≤ euclideanNorm v := by
  have hs : v i ^ 2 ≤ ∑ j, v j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  apply (sq_le_sq₀ (abs_nonneg (v i)) (euclideanNorm_nonneg v)).mp
  simpa only [sq_abs, euclideanNorm_sq] using hs

/-- The sum of absolute coordinates is at most the coordinate count times the Euclidean norm. -/
theorem sum_abs_le_card_mul_euclideanNorm {n : ℕ} (v : Fin n → ℝ) :
    (∑ i, |v i|) ≤ (n : ℝ) * euclideanNorm v := by
  calc
    _ ≤ ∑ _i : Fin n, euclideanNorm v :=
      Finset.sum_le_sum (fun i _ => abs_coordinate_le_euclideanNorm v i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- A coordinatewise radius bound controls every real linear form. -/
theorem abs_sum_mul_le_radius_sum_abs {n : ℕ} (v u : Fin n → ℝ) (R : ℝ)
    (hu : ∀ i, |u i| ≤ R) : |∑ i, v i * u i| ≤ R * ∑ i, |v i| := by
  calc
    _ ≤ ∑ i, |v i * u i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |v i| * R := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hu i) (abs_nonneg (v i))
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

/-- Two shear residual bounds force a bound on the difference of their vertical centers. -/
theorem abs_shift_sub_le_of_two_strip_bounds {n : ℕ} (δ η u : Fin n → ℝ)
    (ε t s z R : ℝ) (hu : ∀ i, |u i| ≤ R)
    (hδ : |z - t - ε * ∑ i, δ i * u i| ≤ R * |ε|)
    (hη : |z - s - ε * ∑ i, η i * u i| ≤ R * |ε|) :
    |t - s| ≤ |ε| * (2 * R + R * ∑ i, |(δ - η) i|) := by
  have hsub : (∑ i, (δ - η) i * u i) = (∑ i, δ i * u i) - ∑ i, η i * u i := by
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have he : t - s = ((z - s - ε * ∑ i, η i * u i) -
      (z - t - ε * ∑ i, δ i * u i)) - ε * ∑ i, (δ - η) i * u i := by
    rw [hsub]
    ring
  have hlin := abs_sum_mul_le_radius_sum_abs (δ - η) u R hu
  calc
    _ = |((z - s - ε * ∑ i, η i * u i) -
        (z - t - ε * ∑ i, δ i * u i)) - ε * ∑ i, (δ - η) i * u i| := congrArg abs he
    _ ≤ |(z - s - ε * ∑ i, η i * u i) - (z - t - ε * ∑ i, δ i * u i)| +
        |ε * ∑ i, (δ - η) i * u i| := abs_sub _ _
    _ ≤ (|z - s - ε * ∑ i, η i * u i| + |z - t - ε * ∑ i, δ i * u i|) +
        |ε| * |∑ i, (δ - η) i * u i| :=
      add_le_add (abs_sub _ _) (le_of_eq (abs_mul _ _))
    _ ≤ (R * |ε| + R * |ε|) + |ε| * (R * ∑ i, |(δ - η) i|) :=
      add_le_add (add_le_add hη hδ) (mul_le_mul_of_nonneg_left hlin (abs_nonneg ε))
    _ = _ := by ring

#print axioms abs_coordinate_le_euclideanNorm
#print axioms sum_abs_le_card_mul_euclideanNorm
#print axioms abs_sum_mul_le_radius_sum_abs
#print axioms abs_shift_sub_le_of_two_strip_bounds

end
end GaloisForLFunctions.BiarithmeticGeometry.FiniteCoordinateNorms
