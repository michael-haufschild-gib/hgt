import GaloisForLFunctions.HTGeometry.CoordinateEinsteinComplexLinearization
import GaloisForLFunctions.HTGeometry.CoordinateEinsteinComplexQuadratic

/-!
# Index collapse of the linearized Einstein coefficients over a diagonal background

When every matrix of the background two-jet is diagonal, the inverse metric is the diagonal of
reciprocals and every index sum in the linearized inverse and Christoffel variations collapses to
at most one surviving term.  The closed forms below express these variations directly through
the entries of an arbitrary perturbation jet, so that later component computations substitute a
specific jet only once, in a small expression, instead of unfolding the full contraction.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.CoordinateMetricTwoJet

variable {d : ℕ}

/-- A background two-jet whose metric, first and second derivative matrices are all diagonal,
with invertible metric entries. -/
structure IsDiagonalJet (J : CoordinateMetricTwoJet d ℂ) : Prop where
  metric_ne : ∀ i j, i ≠ j → J.metric i j = 0
  first_ne : ∀ k i j, i ≠ j → J.first k i j = 0
  second_ne : ∀ k l i j, i ≠ j → J.second k l i j = 0
  metric_diag_ne_zero : ∀ i, J.metric i i ≠ 0

namespace IsDiagonalJet

variable {J : CoordinateMetricTwoJet d ℂ} (h : IsDiagonalJet J)
include h

theorem metric_eq : J.metric = Matrix.diagonal (fun i => J.metric i i) := by
  ext i j
  rw [Matrix.diagonal_apply]
  split_ifs with hij
  · subst hij; rfl
  · exact h.metric_ne i j hij

theorem inv_eq : J.metric⁻¹ = Matrix.diagonal (fun i => (J.metric i i)⁻¹) := by
  have hm := h.metric_eq
  apply Matrix.inv_eq_left_inv
  conv_lhs => rw [hm]
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.one_apply, h.metric_diag_ne_zero]

theorem inv_apply (u m : Fin d) :
    J.metric⁻¹ u m = if u = m then (J.metric u u)⁻¹ else 0 := by
  rw [h.inv_eq, Matrix.diagonal_apply]

/-- Linearized inverse metric over a diagonal background. -/
theorem linearization_inverse_apply (K : CoordinateMetricTwoJet d ℂ) (u m : Fin d) :
    Linearization.inverse J K u m = -(K.metric u m / (J.metric u u * J.metric m m)) := by
  simp only [Linearization.inverse, h.inv_eq, Matrix.neg_apply, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  rw [div_eq_mul_inv, mul_inv]
  ring

/-- Linearized Christoffel symbols over a diagonal background: every index sum collapses. -/
theorem linearization_connection_eq (K : CoordinateMetricTwoJet d ℂ) (u i j : Fin d) :
    Linearization.connection J K u i j =
      (1 / 2 : ℂ) * (-(K.metric u j * J.first i j j / (J.metric u u * J.metric j j)) -
        K.metric u i * J.first j i i / (J.metric u u * J.metric i i) +
        (if i = j then ∑ m, K.metric u m * J.first m i i / (J.metric u u * J.metric m m) else 0) +
        (K.first i u j + K.first j u i - K.first u i j) / J.metric u u) := by
  unfold Linearization.connection
  have hS1 : (∑ m, Linearization.inverse J K u m * J.first i m j) =
      -(K.metric u j * J.first i j j / (J.metric u u * J.metric j j)) := by
    rw [Finset.sum_eq_single j]
    · rw [h.linearization_inverse_apply]; ring
    · intro m _ hm; rw [h.first_ne i m j hm, mul_zero]
    · intro habs; exact absurd (Finset.mem_univ j) habs
  have hS2 : (∑ m, Linearization.inverse J K u m * J.first j m i) =
      -(K.metric u i * J.first j i i / (J.metric u u * J.metric i i)) := by
    rw [Finset.sum_eq_single i]
    · rw [h.linearization_inverse_apply]; ring
    · intro m _ hm; rw [h.first_ne j m i hm, mul_zero]
    · intro habs; exact absurd (Finset.mem_univ i) habs
  have hS3 : (∑ m, Linearization.inverse J K u m * J.first m i j) =
      -(if i = j then ∑ m, K.metric u m * J.first m i i / (J.metric u u * J.metric m m) else 0) := by
    split_ifs with hij
    · subst hij
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [h.linearization_inverse_apply]; ring
    · rw [neg_zero]
      refine Finset.sum_eq_zero (fun m _ => ?_)
      rw [h.first_ne m i j hij, mul_zero]
  have hS4 : (∑ m, J.metric⁻¹ u m * (K.first i m j + K.first j m i - K.first m i j)) =
      (K.first i u j + K.first j u i - K.first u i j) / J.metric u u := by
    rw [Finset.sum_eq_single u]
    · rw [h.inv_apply, if_pos rfl]; ring
    · intro m _ hm; rw [h.inv_apply, if_neg (Ne.symm hm), zero_mul]
    · intro habs; exact absurd (Finset.mem_univ u) habs
  have hsplit : (∑ m, (Linearization.inverse J K u m * (J.first i m j + J.first j m i - J.first m i j) +
      J.metric⁻¹ u m * (K.first i m j + K.first j m i - K.first m i j))) =
      (∑ m, Linearization.inverse J K u m * J.first i m j) +
      (∑ m, Linearization.inverse J K u m * J.first j m i) -
      (∑ m, Linearization.inverse J K u m * J.first m i j) +
      ∑ m, J.metric⁻¹ u m * (K.first i m j + K.first j m i - K.first m i j) := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hsplit, hS1, hS2, hS3, hS4]
  ring

theorem first_eq (k : Fin d) : J.first k = Matrix.diagonal (fun i => J.first k i i) := by
  ext i j
  rw [Matrix.diagonal_apply]
  split_ifs with hij
  · subst hij; rfl
  · exact h.first_ne k i j hij

theorem inverseDerivative_apply (k u m : Fin d) :
    J.inverseDerivative k u m = if u = m then -(J.first k u u / (J.metric u u) ^ (2 : ℕ)) else 0 := by
  have hL := h.inv_eq
  have hF := h.first_eq k
  rw [inverseDerivative, hL, hF, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.neg_apply, Matrix.diagonal_apply]
  simp only [Matrix.diagonal_apply_eq]
  split_ifs with hum
  · subst hum
    rw [div_eq_mul_inv, pow_two, mul_inv]
    ring
  · simp

/-- Linearized spatial inverse derivative over a diagonal background. -/
theorem linearization_inverseSpatial_apply (K : CoordinateMetricTwoJet d ℂ) (k u m : Fin d) :
    Linearization.inverseSpatial J K k u m =
      K.metric u m * J.first k m m / (J.metric u u * J.metric m m ^ (2 : ℕ)) +
        J.first k u u * K.metric u m / (J.metric u u ^ (2 : ℕ) * J.metric m m) -
        K.first k u m / (J.metric u u * J.metric m m) := by
  have hL := h.inv_eq
  have hF := h.first_eq k
  have hinv := h.linearization_inverse_apply K
  have hu := h.metric_diag_ne_zero u
  have hm := h.metric_diag_ne_zero m
  rw [Linearization.inverseSpatial, Matrix.neg_apply, Matrix.add_apply, Matrix.add_apply, hL, hF]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply_eq, hinv]
  field_simp
  ring

/-- Linearized spatial Christoffel derivative over a diagonal background: every index sum
collapses to the surviving diagonal contributions. -/
theorem linearization_connectionSpatial_eq (K : CoordinateMetricTwoJet d ℂ) (k u i j : Fin d) :
    Linearization.connectionSpatial J K k u i j =
      (1 / 2 : ℂ) * ((Linearization.inverseSpatial J K k u j * J.first i j j +
          Linearization.inverseSpatial J K k u i * J.first j i i -
          (if i = j then ∑ m, Linearization.inverseSpatial J K k u m * J.first m i i else 0) +
          -(J.first k u u / (J.metric u u) ^ (2 : ℕ)) * (K.first i u j + K.first j u i - K.first u i j)) +
        (Linearization.inverse J K u j * J.second k i j j +
          Linearization.inverse J K u i * J.second k j i i -
          (if i = j then ∑ m, Linearization.inverse J K u m * J.second k m i i else 0) +
          (K.second k i u j + K.second k j u i - K.second k u i j) / J.metric u u)) := by
  unfold Linearization.connectionSpatial
  have hsecond_ne : ∀ a b c, a ≠ b → J.second k c a b = 0 := fun a b c hab => h.second_ne k c a b hab
  have hS1 : (∑ m, Linearization.inverseSpatial J K k u m * J.first i m j) =
      Linearization.inverseSpatial J K k u j * J.first i j j := by
    rw [Finset.sum_eq_single j]
    · intro m _ hm; rw [h.first_ne i m j hm, mul_zero]
    · intro habs; exact absurd (Finset.mem_univ j) habs
  have hS2 : (∑ m, Linearization.inverseSpatial J K k u m * J.first j m i) =
      Linearization.inverseSpatial J K k u i * J.first j i i := by
    rw [Finset.sum_eq_single i]
    · intro m _ hm; rw [h.first_ne j m i hm, mul_zero]
    · intro habs; exact absurd (Finset.mem_univ i) habs
  have hS3 : (∑ m, Linearization.inverseSpatial J K k u m * J.first m i j) =
      (if i = j then ∑ m, Linearization.inverseSpatial J K k u m * J.first m i i else 0) := by
    split_ifs with hij
    · subst hij; rfl
    · exact Finset.sum_eq_zero (fun m _ => by rw [h.first_ne m i j hij, mul_zero])
  have hS4 : (∑ m, J.inverseDerivative k u m * (K.first i m j + K.first j m i - K.first m i j)) =
      -(J.first k u u / (J.metric u u) ^ (2 : ℕ)) * (K.first i u j + K.first j u i - K.first u i j) := by
    rw [Finset.sum_eq_single u]
    · rw [h.inverseDerivative_apply, if_pos rfl]
    · intro m _ hm; rw [h.inverseDerivative_apply, if_neg (Ne.symm hm), zero_mul]
    · intro habs; exact absurd (Finset.mem_univ u) habs
  have hS5 : (∑ m, Linearization.inverse J K u m * J.second k i m j) =
      Linearization.inverse J K u j * J.second k i j j := by
    rw [Finset.sum_eq_single j]
    · intro m _ hm; rw [hsecond_ne m j i hm, mul_zero]
    · intro habs; exact absurd (Finset.mem_univ j) habs
  have hS6 : (∑ m, Linearization.inverse J K u m * J.second k j m i) =
      Linearization.inverse J K u i * J.second k j i i := by
    rw [Finset.sum_eq_single i]
    · intro m _ hm; rw [hsecond_ne m i j hm, mul_zero]
    · intro habs; exact absurd (Finset.mem_univ i) habs
  have hS7 : (∑ m, Linearization.inverse J K u m * J.second k m i j) =
      (if i = j then ∑ m, Linearization.inverse J K u m * J.second k m i i else 0) := by
    split_ifs with hij
    · subst hij; rfl
    · exact Finset.sum_eq_zero (fun m _ => by rw [hsecond_ne i j m hij, mul_zero])
  have hS8 : (∑ m, J.metric⁻¹ u m * (K.second k i m j + K.second k j m i - K.second k m i j)) =
      (K.second k i u j + K.second k j u i - K.second k u i j) / J.metric u u := by
    rw [Finset.sum_eq_single u]
    · rw [h.inv_apply, if_pos rfl]; ring
    · intro m _ hm; rw [h.inv_apply, if_neg (Ne.symm hm), zero_mul]
    · intro habs; exact absurd (Finset.mem_univ u) habs
  have hsplit : (∑ m, ((Linearization.inverseSpatial J K k u m *
      (J.first i m j + J.first j m i - J.first m i j) +
      J.inverseDerivative k u m * (K.first i m j + K.first j m i - K.first m i j)) +
      (Linearization.inverse J K u m * (J.second k i m j + J.second k j m i - J.second k m i j) +
      J.metric⁻¹ u m * (K.second k i m j + K.second k j m i - K.second k m i j)))) =
      ((∑ m, Linearization.inverseSpatial J K k u m * J.first i m j) +
        (∑ m, Linearization.inverseSpatial J K k u m * J.first j m i) -
        (∑ m, Linearization.inverseSpatial J K k u m * J.first m i j) +
        ∑ m, J.inverseDerivative k u m * (K.first i m j + K.first j m i - K.first m i j)) +
      ((∑ m, Linearization.inverse J K u m * J.second k i m j) +
        (∑ m, Linearization.inverse J K u m * J.second k j m i) -
        (∑ m, Linearization.inverse J K u m * J.second k m i j) +
        ∑ m, J.metric⁻¹ u m * (K.second k i m j + K.second k j m i - K.second k m i j)) := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hsplit, hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8]

end IsDiagonalJet

/-! ## Quadratic level -/

namespace IsDiagonalJet
variable {J : CoordinateMetricTwoJet d ℂ} (h : IsDiagonalJet J)
include h

/-- Quadratic inverse-metric variation over a diagonal background: one genuine matrix product
remains. -/
theorem quadratic_inverse_apply (K : CoordinateMetricTwoJet d ℂ) (u m : Fin d) :
    Quadratic.inverse J K u m =
      2 * ∑ p, K.metric u p * K.metric p m / (J.metric u u * J.metric p p * J.metric m m) := by
  have hL := h.inv_eq
  have hinv := h.linearization_inverse_apply K
  have hu := h.metric_diag_ne_zero u
  have hm := h.metric_diag_ne_zero m
  rw [Quadratic.inverse, Matrix.neg_apply, Matrix.add_apply, hL, Matrix.mul_diagonal,
    Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_apply, Matrix.mul_apply]
  simp only [hinv]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hp := h.metric_diag_ne_zero p
  field_simp
  ring

/-- Quadratic Christoffel variation over a diagonal background. -/
theorem quadratic_connection_eq (K : CoordinateMetricTwoJet d ℂ) (u i j : Fin d) :
    Quadratic.connection J K u i j =
      (1 / 2 : ℂ) * (Quadratic.inverse J K u j * J.first i j j +
        Quadratic.inverse J K u i * J.first j i i -
        (if i = j then ∑ m, Quadratic.inverse J K u m * J.first m i i else 0) +
        2 * ∑ m, Linearization.inverse J K u m * (K.first i m j + K.first j m i - K.first m i j)) := by
  unfold Quadratic.connection
  have hS1 : (∑ m, Quadratic.inverse J K u m * J.first i m j) =
      Quadratic.inverse J K u j * J.first i j j := by
    rw [Finset.sum_eq_single j]
    · intro m _ hm; rw [h.first_ne i m j hm, mul_zero]
    · intro habs; exact absurd (Finset.mem_univ j) habs
  have hS2 : (∑ m, Quadratic.inverse J K u m * J.first j m i) =
      Quadratic.inverse J K u i * J.first j i i := by
    rw [Finset.sum_eq_single i]
    · intro m _ hm; rw [h.first_ne j m i hm, mul_zero]
    · intro habs; exact absurd (Finset.mem_univ i) habs
  have hS3 : (∑ m, Quadratic.inverse J K u m * J.first m i j) =
      (if i = j then ∑ m, Quadratic.inverse J K u m * J.first m i i else 0) := by
    split_ifs with hij
    · subst hij; rfl
    · exact Finset.sum_eq_zero (fun m _ => by rw [h.first_ne m i j hij, mul_zero])
  have hsplit : (∑ m, ((Quadratic.inverse J K u m * (J.first i m j + J.first j m i - J.first m i j) +
      Linearization.inverse J K u m * (K.first i m j + K.first j m i - K.first m i j)) +
      Linearization.inverse J K u m * (K.first i m j + K.first j m i - K.first m i j))) =
      (∑ m, Quadratic.inverse J K u m * J.first i m j) +
      (∑ m, Quadratic.inverse J K u m * J.first j m i) -
      (∑ m, Quadratic.inverse J K u m * J.first m i j) +
      2 * ∑ m, Linearization.inverse J K u m * (K.first i m j + K.first j m i - K.first m i j) := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, two_mul]
    ring
  rw [hsplit, hS1, hS2, hS3]

end IsDiagonalJet

namespace IsDiagonalJet
variable {J : CoordinateMetricTwoJet d ℂ} (h : IsDiagonalJet J)
include h

/-- Quadratic spatial inverse variation over a diagonal background, with the linear inverse and
the quadratic inverse retained as atoms and every diagonal factor evaluated. -/
theorem quadratic_inverseSpatial_apply (K : CoordinateMetricTwoJet d ℂ) (k u m : Fin d) :
    Quadratic.inverseSpatial J K k u m =
      -((Quadratic.inverse J K u m * J.first k m m * (J.metric m m)⁻¹ +
          (∑ p, Linearization.inverse J K u p * K.first k p m) * (J.metric m m)⁻¹ +
          ∑ p, Linearization.inverse J K u p * J.first k p p * Linearization.inverse J K p m) +
        ((∑ p, Linearization.inverse J K u p * K.first k p m) * (J.metric m m)⁻¹ +
          ∑ p, (J.metric u u)⁻¹ * K.first k u p * Linearization.inverse J K p m) +
        (∑ p, (Linearization.inverse J K u p * J.first k p p + (J.metric u u)⁻¹ * K.first k u p) *
            Linearization.inverse J K p m +
          (J.metric u u)⁻¹ * J.first k u u * Quadratic.inverse J K u m)) := by
  have hL := h.inv_eq
  have hF := h.first_eq k
  rw [Quadratic.inverseSpatial, Matrix.neg_apply, Matrix.add_apply, Matrix.add_apply, hL, hF]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero,
    zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

end IsDiagonalJet

namespace IsDiagonalJet
variable {J : CoordinateMetricTwoJet d ℂ} (h : IsDiagonalJet J)
include h

/-- Quadratic spatial Christoffel variation over a diagonal background: the background-derivative
sums collapse, the two perturbation sums remain. -/
theorem quadratic_connectionSpatial_eq (K : CoordinateMetricTwoJet d ℂ) (k u i j : Fin d) :
    Quadratic.connectionSpatial J K k u i j =
      (1 / 2 : ℂ) * ((Quadratic.inverseSpatial J K k u j * J.first i j j +
          Quadratic.inverseSpatial J K k u i * J.first j i i -
          (if i = j then ∑ m, Quadratic.inverseSpatial J K k u m * J.first m i i else 0) +
          2 * ∑ m, Linearization.inverseSpatial J K k u m *
            (K.first i m j + K.first j m i - K.first m i j)) +
        (Quadratic.inverse J K u j * J.second k i j j +
          Quadratic.inverse J K u i * J.second k j i i -
          (if i = j then ∑ m, Quadratic.inverse J K u m * J.second k m i i else 0) +
          2 * ∑ m, Linearization.inverse J K u m *
            (K.second k i m j + K.second k j m i - K.second k m i j))) := by
  unfold Quadratic.connectionSpatial
  have hsecond_ne : ∀ a b c, a ≠ b → J.second k c a b = 0 := fun a b c hab => h.second_ne k c a b hab
  have hS1 : (∑ m, Quadratic.inverseSpatial J K k u m * J.first i m j) =
      Quadratic.inverseSpatial J K k u j * J.first i j j := by
    rw [Finset.sum_eq_single j]
    · intro m _ hm; rw [h.first_ne i m j hm, mul_zero]
    · intro habs; exact absurd (Finset.mem_univ j) habs
  have hS2 : (∑ m, Quadratic.inverseSpatial J K k u m * J.first j m i) =
      Quadratic.inverseSpatial J K k u i * J.first j i i := by
    rw [Finset.sum_eq_single i]
    · intro m _ hm; rw [h.first_ne j m i hm, mul_zero]
    · intro habs; exact absurd (Finset.mem_univ i) habs
  have hS3 : (∑ m, Quadratic.inverseSpatial J K k u m * J.first m i j) =
      (if i = j then ∑ m, Quadratic.inverseSpatial J K k u m * J.first m i i else 0) := by
    split_ifs with hij
    · subst hij; rfl
    · exact Finset.sum_eq_zero (fun m _ => by rw [h.first_ne m i j hij, mul_zero])
  have hS5 : (∑ m, Quadratic.inverse J K u m * J.second k i m j) =
      Quadratic.inverse J K u j * J.second k i j j := by
    rw [Finset.sum_eq_single j]
    · intro m _ hm; rw [hsecond_ne m j i hm, mul_zero]
    · intro habs; exact absurd (Finset.mem_univ j) habs
  have hS6 : (∑ m, Quadratic.inverse J K u m * J.second k j m i) =
      Quadratic.inverse J K u i * J.second k j i i := by
    rw [Finset.sum_eq_single i]
    · intro m _ hm; rw [hsecond_ne m i j hm, mul_zero]
    · intro habs; exact absurd (Finset.mem_univ i) habs
  have hS7 : (∑ m, Quadratic.inverse J K u m * J.second k m i j) =
      (if i = j then ∑ m, Quadratic.inverse J K u m * J.second k m i i else 0) := by
    split_ifs with hij
    · subst hij; rfl
    · exact Finset.sum_eq_zero (fun m _ => by rw [hsecond_ne i j m hij, mul_zero])
  have hsplit : (∑ m, (((Quadratic.inverseSpatial J K k u m *
      (J.first i m j + J.first j m i - J.first m i j) +
      Linearization.inverseSpatial J K k u m * (K.first i m j + K.first j m i - K.first m i j)) +
      Linearization.inverseSpatial J K k u m * (K.first i m j + K.first j m i - K.first m i j)) +
      (Quadratic.inverse J K u m * (J.second k i m j + J.second k j m i - J.second k m i j) +
      Linearization.inverse J K u m * (K.second k i m j + K.second k j m i - K.second k m i j)) +
      Linearization.inverse J K u m * (K.second k i m j + K.second k j m i - K.second k m i j))) =
      ((∑ m, Quadratic.inverseSpatial J K k u m * J.first i m j) +
        (∑ m, Quadratic.inverseSpatial J K k u m * J.first j m i) -
        (∑ m, Quadratic.inverseSpatial J K k u m * J.first m i j) +
        2 * ∑ m, Linearization.inverseSpatial J K k u m *
          (K.first i m j + K.first j m i - K.first m i j)) +
      ((∑ m, Quadratic.inverse J K u m * J.second k i m j) +
        (∑ m, Quadratic.inverse J K u m * J.second k j m i) -
        (∑ m, Quadratic.inverse J K u m * J.second k m i j) +
        2 * ∑ m, Linearization.inverse J K u m *
          (K.second k i m j + K.second k j m i - K.second k m i j)) := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, two_mul]
    ring
  rw [hsplit, hS1, hS2, hS3, hS5, hS6, hS7]

end IsDiagonalJet

namespace IsDiagonalJet
variable {J : CoordinateMetricTwoJet d ℂ} (h : IsDiagonalJet J)
include h

/-- Background Christoffel symbols of a diagonal jet. -/
theorem christoffel_eq (u k m : Fin d) :
    J.christoffel u k m = (1 / 2 : ℂ) * (J.metric u u)⁻¹ *
      ((if u = m then J.first k u u else 0) + (if u = k then J.first m u u else 0) -
        (if k = m then J.first u k k else 0)) := by
  unfold christoffel
  rw [Finset.sum_eq_single u]
  · rw [h.inv_apply, if_pos rfl]
    have h1 : J.first k u m = if u = m then J.first k u u else 0 := by
      split_ifs with hum
      · subst hum; rfl
      · exact h.first_ne k u m hum
    have h2 : J.first m u k = if u = k then J.first m u u else 0 := by
      split_ifs with huk
      · subst huk; rfl
      · exact h.first_ne m u k huk
    have h3 : J.first u k m = if k = m then J.first u k k else 0 := by
      split_ifs with hkm
      · subst hkm; rfl
      · exact h.first_ne u k m hkm
    rw [h1, h2, h3]
    ring
  · intro p _ hp
    rw [h.inv_apply, if_neg (Ne.symm hp), zero_mul]
  · intro habs; exact absurd (Finset.mem_univ u) habs

end IsDiagonalJet

namespace IsDiagonalJet
variable {J : CoordinateMetricTwoJet d ℂ} (h : IsDiagonalJet J)
include h

/-- A sum against the background Christoffel symbol in its last two indices. -/
theorem sum_mul_christoffel (f : Fin d → ℂ) (l i : Fin d) :
    (∑ m, f m * J.christoffel m l i) =
      (1 / 2 : ℂ) * (f i * (J.metric i i)⁻¹ * J.first l i i + f l * (J.metric l l)⁻¹ * J.first i l l -
        (if l = i then ∑ m, f m * (J.metric m m)⁻¹ * J.first m l l else 0)) := by
  simp only [h.christoffel_eq, mul_add, mul_sub, mul_ite, mul_zero, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  split_ifs with hli
  · subst hli
    simp only [Finset.mul_sum]
    ring_nf
  · ring

/-- A sum against the background Christoffel symbol in its first two indices. -/
theorem christoffel_mul_sum (f : Fin d → ℂ) (u k : Fin d) :
    (∑ m, J.christoffel u k m * f m) =
      (1 / 2 : ℂ) * (J.metric u u)⁻¹ * (J.first k u u * f u +
        (if u = k then ∑ m, J.first m u u * f m else 0) - J.first u k k * f k) := by
  simp only [h.christoffel_eq, mul_add, mul_sub, add_mul, sub_mul, mul_ite, ite_mul, mul_zero,
    zero_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
  split_ifs with huk
  · subst huk
    simp only [Finset.mul_sum]
    ring_nf
  · ring

end IsDiagonalJet

namespace IsDiagonalJet
variable {J : CoordinateMetricTwoJet d ℂ} (h : IsDiagonalJet J)
include h

/-- Quadratic Riemann variation over a diagonal background: every background-Christoffel sum
collapses; the two products of linear Christoffel variations remain as genuine sums. -/
theorem quadratic_curvature_eq (K : CoordinateMetricTwoJet d ℂ) (u i k l : Fin d) :
    Quadratic.curvature J K u i k l =
      Quadratic.connectionSpatial J K k u l i - Quadratic.connectionSpatial J K l u k i +
      (1 / 2 : ℂ) * (Quadratic.connection J K u k i * (J.metric i i)⁻¹ * J.first l i i +
        Quadratic.connection J K u k l * (J.metric l l)⁻¹ * J.first i l l -
        (if l = i then ∑ m, Quadratic.connection J K u k m * (J.metric m m)⁻¹ * J.first m l l
          else 0)) +
      2 * ∑ m, Linearization.connection J K u k m * Linearization.connection J K m l i +
      (1 / 2 : ℂ) * (J.metric u u)⁻¹ * (J.first k u u * Quadratic.connection J K u l i +
        (if u = k then ∑ m, J.first m u u * Quadratic.connection J K m l i else 0) -
        J.first u k k * Quadratic.connection J K k l i) -
      (1 / 2 : ℂ) * (Quadratic.connection J K u l i * (J.metric i i)⁻¹ * J.first k i i +
        Quadratic.connection J K u l k * (J.metric k k)⁻¹ * J.first i k k -
        (if k = i then ∑ m, Quadratic.connection J K u l m * (J.metric m m)⁻¹ * J.first m k k
          else 0)) -
      2 * ∑ m, Linearization.connection J K u l m * Linearization.connection J K m k i -
      (1 / 2 : ℂ) * (J.metric u u)⁻¹ * (J.first l u u * Quadratic.connection J K u k i +
        (if u = l then ∑ m, J.first m u u * Quadratic.connection J K m k i else 0) -
        J.first u l l * Quadratic.connection J K l k i) := by
  unfold Quadratic.curvature
  have hA := h.sum_mul_christoffel (fun m => Quadratic.connection J K u k m) l i
  have hB := h.christoffel_mul_sum (fun m => Quadratic.connection J K m l i) u k
  have hC := h.sum_mul_christoffel (fun m => Quadratic.connection J K u l m) k i
  have hD := h.christoffel_mul_sum (fun m => Quadratic.connection J K m k i) u l
  beta_reduce at hA hB hC hD
  have hsplit : (∑ m, ((Quadratic.connection J K u k m * J.christoffel m l i +
      Linearization.connection J K u k m * Linearization.connection J K m l i) +
      (Linearization.connection J K u k m * Linearization.connection J K m l i +
        J.christoffel u k m * Quadratic.connection J K m l i) -
      (Quadratic.connection J K u l m * J.christoffel m k i +
        Linearization.connection J K u l m * Linearization.connection J K m k i) -
      (Linearization.connection J K u l m * Linearization.connection J K m k i +
        J.christoffel u l m * Quadratic.connection J K m k i))) =
      (∑ m, Quadratic.connection J K u k m * J.christoffel m l i) +
      2 * (∑ m, Linearization.connection J K u k m * Linearization.connection J K m l i) +
      (∑ m, J.christoffel u k m * Quadratic.connection J K m l i) -
      (∑ m, Quadratic.connection J K u l m * J.christoffel m k i) -
      2 * (∑ m, Linearization.connection J K u l m * Linearization.connection J K m k i) -
      ∑ m, J.christoffel u l m * Quadratic.connection J K m k i := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, two_mul]
    ring
  rw [hsplit, hA, hB, hC, hD]
  ring

end IsDiagonalJet

namespace IsDiagonalJet
variable {J : CoordinateMetricTwoJet d ℂ} (h : IsDiagonalJet J)
include h

/-- Linearized Riemann variation over a diagonal background with every background-Christoffel
sum collapsed. -/
theorem linearization_curvature_eq (K : CoordinateMetricTwoJet d ℂ) (u i k l : Fin d) :
    Linearization.curvature J K u i k l =
      Linearization.connectionSpatial J K k u l i - Linearization.connectionSpatial J K l u k i +
      (1 / 2 : ℂ) * (Linearization.connection J K u k i * (J.metric i i)⁻¹ * J.first l i i +
        Linearization.connection J K u k l * (J.metric l l)⁻¹ * J.first i l l -
        (if l = i then ∑ m, Linearization.connection J K u k m * (J.metric m m)⁻¹ * J.first m l l
          else 0)) +
      (1 / 2 : ℂ) * (J.metric u u)⁻¹ * (J.first k u u * Linearization.connection J K u l i +
        (if u = k then ∑ m, J.first m u u * Linearization.connection J K m l i else 0) -
        J.first u k k * Linearization.connection J K k l i) -
      (1 / 2 : ℂ) * (Linearization.connection J K u l i * (J.metric i i)⁻¹ * J.first k i i +
        Linearization.connection J K u l k * (J.metric k k)⁻¹ * J.first i k k -
        (if k = i then ∑ m, Linearization.connection J K u l m * (J.metric m m)⁻¹ * J.first m k k
          else 0)) -
      (1 / 2 : ℂ) * (J.metric u u)⁻¹ * (J.first l u u * Linearization.connection J K u k i +
        (if u = l then ∑ m, J.first m u u * Linearization.connection J K m k i else 0) -
        J.first u l l * Linearization.connection J K l k i) := by
  unfold Linearization.curvature
  have hA := h.sum_mul_christoffel (fun m => Linearization.connection J K u k m) l i
  have hB := h.christoffel_mul_sum (fun m => Linearization.connection J K m l i) u k
  have hC := h.sum_mul_christoffel (fun m => Linearization.connection J K u l m) k i
  have hD := h.christoffel_mul_sum (fun m => Linearization.connection J K m k i) u l
  beta_reduce at hA hB hC hD
  have hsplit : (∑ m, ((Linearization.connection J K u k m * J.christoffel m l i +
      J.christoffel u k m * Linearization.connection J K m l i) -
      (Linearization.connection J K u l m * J.christoffel m k i +
        J.christoffel u l m * Linearization.connection J K m k i))) =
      (∑ m, Linearization.connection J K u k m * J.christoffel m l i) +
      (∑ m, J.christoffel u k m * Linearization.connection J K m l i) -
      (∑ m, Linearization.connection J K u l m * J.christoffel m k i) -
      ∑ m, J.christoffel u l m * Linearization.connection J K m k i := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [hsplit, hA, hB, hC, hD]
  ring

/-- Over an Einstein diagonal background, a perturbation solving the linearized Einstein
equation with the same constant has vanishing linearized scalar curvature. -/
theorem linearization_scalar_eq_zero (K : CoordinateMetricTwoJet d ℂ) (c : ℂ)
    (hJ : ∀ i j, J.ricci i j = c * J.metric i j)
    (hK : ∀ i j, Linearization.ricci J K i j = c * K.metric i j) :
    Linearization.scalar J K = 0 := by
  unfold Linearization.scalar
  simp only [hJ, hK, h.linearization_inverse_apply, h.inv_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [Finset.sum_eq_single i]
  · simp only [if_true]
    have := h.metric_diag_ne_zero i
    field_simp
    ring
  · intro j _ hji
    rw [h.metric_ne i j (Ne.symm hji)]
    simp [Ne.symm hji]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- Over an Einstein diagonal background, the quadratic scalar variation of a symmetric
perturbation solving the linearized equation is the background trace of the quadratic Ricci
variation: both inverse–Ricci cross terms cancel. -/
theorem quadratic_scalar_eq (K : CoordinateMetricTwoJet d ℂ) (c : ℂ)
    (hJ : ∀ i j, J.ricci i j = c * J.metric i j)
    (hK : ∀ i j, Linearization.ricci J K i j = c * K.metric i j)
    (hsym : ∀ i j, K.metric i j = K.metric j i) :
    Quadratic.scalar J K = ∑ i, (J.metric i i)⁻¹ * Quadratic.ricci J K i i := by
  unfold Quadratic.scalar
  simp only [hJ, hK, h.linearization_inverse_apply, h.inv_apply, h.quadratic_inverse_apply]
  have hterm : ∀ i j, ((2 * ∑ p, K.metric i p * K.metric p j /
      (J.metric i i * J.metric p p * J.metric j j)) * (c * J.metric i j) +
      -(K.metric i j / (J.metric i i * J.metric j j)) * (c * K.metric i j)) +
      (-(K.metric i j / (J.metric i i * J.metric j j)) * (c * K.metric i j) +
      (if i = j then (J.metric i i)⁻¹ else 0) * Quadratic.ricci J K i j) =
      (if i = j then 2 * c * ∑ p, K.metric i p * K.metric p i /
        (J.metric i i * J.metric p p) else 0) -
      2 * c * K.metric i j * K.metric i j / (J.metric i i * J.metric j j) +
      (if i = j then (J.metric i i)⁻¹ * Quadratic.ricci J K i j else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      have hg := h.metric_diag_ne_zero i
      have hsum : (2 * ∑ p, K.metric i p * K.metric p i /
          (J.metric i i * J.metric p p * J.metric i i)) * (c * J.metric i i) =
          2 * c * ∑ p, K.metric i p * K.metric p i / (J.metric i i * J.metric p p) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p _
        have hp := h.metric_diag_ne_zero p
        field_simp
      rw [hsum]
      ring
    · rw [h.metric_ne i j hij]
      simp only [hij, if_false]
      ring
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have hsq : ∑ i, ∑ j, 2 * c * K.metric i j * K.metric i j / (J.metric i i * J.metric j j) =
      ∑ i, 2 * c * ∑ p, K.metric i p * K.metric p i / (J.metric i i * J.metric p p) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [hsym p i]
    ring
  rw [hsq]
  ring

/-- The quadratic Einstein variation over an Einstein diagonal background reduces to the
quadratic Ricci variation minus half the background metric times its background trace. -/
theorem quadratic_einstein_eq (K : CoordinateMetricTwoJet d ℂ) (c : ℂ)
    (hJ : ∀ i j, J.ricci i j = c * J.metric i j)
    (hK : ∀ i j, Linearization.ricci J K i j = c * K.metric i j)
    (hsym : ∀ i j, K.metric i j = K.metric j i) (i j : Fin d) :
    Quadratic.einstein J K i j = Quadratic.ricci J K i j -
      (1 / 2 : ℂ) * (∑ u, (J.metric u u)⁻¹ * Quadratic.ricci J K u u) * J.metric i j := by
  unfold Quadratic.einstein
  rw [h.quadratic_scalar_eq K c hJ hK hsym, h.linearization_scalar_eq_zero K c hJ hK]
  ring

end IsDiagonalJet

end GaloisForLFunctions.HTGeometry.CoordinateMetricTwoJet
