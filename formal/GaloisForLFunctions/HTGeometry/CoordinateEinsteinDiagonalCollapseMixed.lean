import GaloisForLFunctions.HTGeometry.CoordinateEinsteinDiagonalCollapse
import GaloisForLFunctions.HTGeometry.CoordinateEinsteinComplexMixedQuadratic

/-!
# Index collapse of the mixed quadratic Einstein coefficients over a diagonal background

The mixed (polarized) quadratic variation `MixedQuadratic` of the Einstein tensor in two
independent perturbation jets `K`, `V` is expressed, over a diagonal background jet, through the
entries of `K` and `V` with every background index sum collapsed, exactly as the diagonal
quadratic variation in `CoordinateEinsteinDiagonalCollapse`. The mixed inverse variation is the
polarization `Σ_p (V_{up} K_{pm} + K_{up} V_{pm})/(g_{uu} g_{pp} g_{mm})`; the mixed Christoffel,
spatial Christoffel and Riemann variations keep the two ordered products of linearized
Christoffel variations as genuine sums; over an Einstein background and for symmetric
perturbations solving the linearized equation, the mixed Einstein variation is the mixed Ricci
variation minus half the background metric times its background trace.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.CoordinateMetricTwoJet

variable {d : ℕ}

namespace IsDiagonalJet
variable {J : CoordinateMetricTwoJet d ℂ} (h : IsDiagonalJet J)
include h

/-- Mixed inverse-metric variation over a diagonal background. -/
theorem mixedQuadratic_inverse_apply (K V : CoordinateMetricTwoJet d ℂ) (u m : Fin d) :
    MixedQuadratic.inverse J K V u m =
      ∑ p, (V.metric u p * K.metric p m + K.metric u p * V.metric p m) /
        (J.metric u u * J.metric p p * J.metric m m) := by
  have hL := h.inv_eq
  have hinvV := h.linearization_inverse_apply V
  have hu := h.metric_diag_ne_zero u
  have hm := h.metric_diag_ne_zero m
  rw [MixedQuadratic.inverse, Matrix.neg_apply, Matrix.add_apply, hL, Matrix.mul_diagonal,
    Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_apply, Matrix.mul_apply]
  simp only [hinvV]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hp := h.metric_diag_ne_zero p
  field_simp
  ring

/-- Mixed Christoffel variation over a diagonal background. -/
theorem mixedQuadratic_connection_eq (K V : CoordinateMetricTwoJet d ℂ) (u i j : Fin d) :
    MixedQuadratic.connection J K V u i j =
      (1 / 2 : ℂ) * (MixedQuadratic.inverse J K V u j * J.first i j j +
        MixedQuadratic.inverse J K V u i * J.first j i i -
        (if i = j then ∑ m, MixedQuadratic.inverse J K V u m * J.first m i i else 0) +
        ∑ m, (Linearization.inverse J K u m * (V.first i m j + V.first j m i - V.first m i j) +
          Linearization.inverse J V u m * (K.first i m j + K.first j m i - K.first m i j))) := by
  unfold MixedQuadratic.connection
  have hS1 : (∑ m, MixedQuadratic.inverse J K V u m * J.first i m j) =
      MixedQuadratic.inverse J K V u j * J.first i j j := by
    rw [Finset.sum_eq_single j]
    · intro m _ hm; rw [h.first_ne i m j hm, mul_zero]
    · intro habs; exact absurd (Finset.mem_univ j) habs
  have hS2 : (∑ m, MixedQuadratic.inverse J K V u m * J.first j m i) =
      MixedQuadratic.inverse J K V u i * J.first j i i := by
    rw [Finset.sum_eq_single i]
    · intro m _ hm; rw [h.first_ne j m i hm, mul_zero]
    · intro habs; exact absurd (Finset.mem_univ i) habs
  have hS3 : (∑ m, MixedQuadratic.inverse J K V u m * J.first m i j) =
      (if i = j then ∑ m, MixedQuadratic.inverse J K V u m * J.first m i i else 0) := by
    split_ifs with hij
    · subst hij; rfl
    · exact Finset.sum_eq_zero (fun m _ => by rw [h.first_ne m i j hij, mul_zero])
  have hsplit : (∑ m, ((MixedQuadratic.inverse J K V u m * (J.first i m j + J.first j m i - J.first m i j) +
      Linearization.inverse J K u m * (V.first i m j + V.first j m i - V.first m i j)) +
      Linearization.inverse J V u m * (K.first i m j + K.first j m i - K.first m i j))) =
      (∑ m, MixedQuadratic.inverse J K V u m * J.first i m j) +
      (∑ m, MixedQuadratic.inverse J K V u m * J.first j m i) -
      (∑ m, MixedQuadratic.inverse J K V u m * J.first m i j) +
      ∑ m, (Linearization.inverse J K u m * (V.first i m j + V.first j m i - V.first m i j) +
        Linearization.inverse J V u m * (K.first i m j + K.first j m i - K.first m i j)) := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [hsplit, hS1, hS2, hS3]

end IsDiagonalJet

namespace IsDiagonalJet
variable {J : CoordinateMetricTwoJet d ℂ} (h : IsDiagonalJet J)
include h

/-- Mixed spatial inverse variation over a diagonal background, with the linear and mixed inverses
retained as atoms and every diagonal factor evaluated. -/
theorem mixedQuadratic_inverseSpatial_apply (K V : CoordinateMetricTwoJet d ℂ) (k u m : Fin d) :
    MixedQuadratic.inverseSpatial J K V k u m =
      -(((MixedQuadratic.inverse J K V u m * J.first k m m +
            ∑ p, Linearization.inverse J K u p * V.first k p m) * (J.metric m m)⁻¹ +
          ∑ p, Linearization.inverse J K u p * J.first k p p * Linearization.inverse J V p m) +
        ((∑ p, Linearization.inverse J V u p * K.first k p m) * (J.metric m m)⁻¹ +
          ∑ p, (J.metric u u)⁻¹ * K.first k u p * Linearization.inverse J V p m) +
        (∑ p, (Linearization.inverse J V u p * J.first k p p + (J.metric u u)⁻¹ * V.first k u p) *
            Linearization.inverse J K p m +
          (J.metric u u)⁻¹ * J.first k u u * MixedQuadratic.inverse J K V u m)) := by
  have hL := h.inv_eq
  have hF := h.first_eq k
  rw [MixedQuadratic.inverseSpatial, Matrix.neg_apply, Matrix.add_apply, Matrix.add_apply, hL, hF]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero,
    zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end IsDiagonalJet

namespace IsDiagonalJet
variable {J : CoordinateMetricTwoJet d ℂ} (h : IsDiagonalJet J)
include h

/-- Mixed spatial Christoffel variation over a diagonal background. -/
theorem mixedQuadratic_connectionSpatial_eq (K V : CoordinateMetricTwoJet d ℂ) (k u i j : Fin d) :
    MixedQuadratic.connectionSpatial J K V k u i j =
      (1 / 2 : ℂ) * ((MixedQuadratic.inverseSpatial J K V k u j * J.first i j j +
          MixedQuadratic.inverseSpatial J K V k u i * J.first j i i -
          (if i = j then ∑ m, MixedQuadratic.inverseSpatial J K V k u m * J.first m i i else 0) +
          ∑ m, (Linearization.inverseSpatial J K k u m *
              (V.first i m j + V.first j m i - V.first m i j) +
            Linearization.inverseSpatial J V k u m *
              (K.first i m j + K.first j m i - K.first m i j))) +
        (MixedQuadratic.inverse J K V u j * J.second k i j j +
          MixedQuadratic.inverse J K V u i * J.second k j i i -
          (if i = j then ∑ m, MixedQuadratic.inverse J K V u m * J.second k m i i else 0) +
          ∑ m, (Linearization.inverse J K u m *
              (V.second k i m j + V.second k j m i - V.second k m i j) +
            Linearization.inverse J V u m *
              (K.second k i m j + K.second k j m i - K.second k m i j)))) := by
  unfold MixedQuadratic.connectionSpatial
  have hsecond_ne : ∀ a b c, a ≠ b → J.second k c a b = 0 := fun a b c hab => h.second_ne k c a b hab
  have hS1 : (∑ m, MixedQuadratic.inverseSpatial J K V k u m * J.first i m j) =
      MixedQuadratic.inverseSpatial J K V k u j * J.first i j j := by
    rw [Finset.sum_eq_single j]
    · intro m _ hm; rw [h.first_ne i m j hm, mul_zero]
    · intro habs; exact absurd (Finset.mem_univ j) habs
  have hS2 : (∑ m, MixedQuadratic.inverseSpatial J K V k u m * J.first j m i) =
      MixedQuadratic.inverseSpatial J K V k u i * J.first j i i := by
    rw [Finset.sum_eq_single i]
    · intro m _ hm; rw [h.first_ne j m i hm, mul_zero]
    · intro habs; exact absurd (Finset.mem_univ i) habs
  have hS3 : (∑ m, MixedQuadratic.inverseSpatial J K V k u m * J.first m i j) =
      (if i = j then ∑ m, MixedQuadratic.inverseSpatial J K V k u m * J.first m i i else 0) := by
    split_ifs with hij
    · subst hij; rfl
    · exact Finset.sum_eq_zero (fun m _ => by rw [h.first_ne m i j hij, mul_zero])
  have hS5 : (∑ m, MixedQuadratic.inverse J K V u m * J.second k i m j) =
      MixedQuadratic.inverse J K V u j * J.second k i j j := by
    rw [Finset.sum_eq_single j]
    · intro m _ hm; rw [hsecond_ne m j i hm, mul_zero]
    · intro habs; exact absurd (Finset.mem_univ j) habs
  have hS6 : (∑ m, MixedQuadratic.inverse J K V u m * J.second k j m i) =
      MixedQuadratic.inverse J K V u i * J.second k j i i := by
    rw [Finset.sum_eq_single i]
    · intro m _ hm; rw [hsecond_ne m i j hm, mul_zero]
    · intro habs; exact absurd (Finset.mem_univ i) habs
  have hS7 : (∑ m, MixedQuadratic.inverse J K V u m * J.second k m i j) =
      (if i = j then ∑ m, MixedQuadratic.inverse J K V u m * J.second k m i i else 0) := by
    split_ifs with hij
    · subst hij; rfl
    · exact Finset.sum_eq_zero (fun m _ => by rw [hsecond_ne i j m hij, mul_zero])
  have hsplit : (∑ m, (((MixedQuadratic.inverseSpatial J K V k u m *
      (J.first i m j + J.first j m i - J.first m i j) +
      Linearization.inverseSpatial J K k u m * (V.first i m j + V.first j m i - V.first m i j)) +
      Linearization.inverseSpatial J V k u m * (K.first i m j + K.first j m i - K.first m i j)) +
      (MixedQuadratic.inverse J K V u m * (J.second k i m j + J.second k j m i - J.second k m i j) +
      Linearization.inverse J K u m * (V.second k i m j + V.second k j m i - V.second k m i j)) +
      Linearization.inverse J V u m * (K.second k i m j + K.second k j m i - K.second k m i j))) =
      ((∑ m, MixedQuadratic.inverseSpatial J K V k u m * J.first i m j) +
        (∑ m, MixedQuadratic.inverseSpatial J K V k u m * J.first j m i) -
        (∑ m, MixedQuadratic.inverseSpatial J K V k u m * J.first m i j) +
        ∑ m, (Linearization.inverseSpatial J K k u m *
            (V.first i m j + V.first j m i - V.first m i j) +
          Linearization.inverseSpatial J V k u m *
            (K.first i m j + K.first j m i - K.first m i j))) +
      ((∑ m, MixedQuadratic.inverse J K V u m * J.second k i m j) +
        (∑ m, MixedQuadratic.inverse J K V u m * J.second k j m i) -
        (∑ m, MixedQuadratic.inverse J K V u m * J.second k m i j) +
        ∑ m, (Linearization.inverse J K u m *
            (V.second k i m j + V.second k j m i - V.second k m i j) +
          Linearization.inverse J V u m *
            (K.second k i m j + K.second k j m i - K.second k m i j))) := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [hsplit, hS1, hS2, hS3, hS5, hS6, hS7]

end IsDiagonalJet

namespace IsDiagonalJet
variable {J : CoordinateMetricTwoJet d ℂ} (h : IsDiagonalJet J)
include h

/-- Mixed Riemann variation over a diagonal background: every background-Christoffel sum
collapses; the two ordered products of linear Christoffel variations remain as genuine sums. -/
theorem mixedQuadratic_curvature_eq (K V : CoordinateMetricTwoJet d ℂ) (u i k l : Fin d) :
    MixedQuadratic.curvature J K V u i k l =
      MixedQuadratic.connectionSpatial J K V k u l i - MixedQuadratic.connectionSpatial J K V l u k i +
      (1 / 2 : ℂ) * (MixedQuadratic.connection J K V u k i * (J.metric i i)⁻¹ * J.first l i i +
        MixedQuadratic.connection J K V u k l * (J.metric l l)⁻¹ * J.first i l l -
        (if l = i then ∑ m, MixedQuadratic.connection J K V u k m * (J.metric m m)⁻¹ * J.first m l l
          else 0)) +
      (∑ m, (Linearization.connection J K u k m * Linearization.connection J V m l i +
        Linearization.connection J V u k m * Linearization.connection J K m l i)) +
      (1 / 2 : ℂ) * (J.metric u u)⁻¹ * (J.first k u u * MixedQuadratic.connection J K V u l i +
        (if u = k then ∑ m, J.first m u u * MixedQuadratic.connection J K V m l i else 0) -
        J.first u k k * MixedQuadratic.connection J K V k l i) -
      (1 / 2 : ℂ) * (MixedQuadratic.connection J K V u l i * (J.metric i i)⁻¹ * J.first k i i +
        MixedQuadratic.connection J K V u l k * (J.metric k k)⁻¹ * J.first i k k -
        (if k = i then ∑ m, MixedQuadratic.connection J K V u l m * (J.metric m m)⁻¹ * J.first m k k
          else 0)) -
      (∑ m, (Linearization.connection J K u l m * Linearization.connection J V m k i +
        Linearization.connection J V u l m * Linearization.connection J K m k i)) -
      (1 / 2 : ℂ) * (J.metric u u)⁻¹ * (J.first l u u * MixedQuadratic.connection J K V u k i +
        (if u = l then ∑ m, J.first m u u * MixedQuadratic.connection J K V m k i else 0) -
        J.first u l l * MixedQuadratic.connection J K V l k i) := by
  unfold MixedQuadratic.curvature
  have hA := h.sum_mul_christoffel (fun m => MixedQuadratic.connection J K V u k m) l i
  have hB := h.christoffel_mul_sum (fun m => MixedQuadratic.connection J K V m l i) u k
  have hC := h.sum_mul_christoffel (fun m => MixedQuadratic.connection J K V u l m) k i
  have hD := h.christoffel_mul_sum (fun m => MixedQuadratic.connection J K V m k i) u l
  beta_reduce at hA hB hC hD
  have hsplit : (∑ m, ((MixedQuadratic.connection J K V u k m * J.christoffel m l i +
      Linearization.connection J K u k m * Linearization.connection J V m l i) +
      (Linearization.connection J V u k m * Linearization.connection J K m l i +
        J.christoffel u k m * MixedQuadratic.connection J K V m l i) -
      (MixedQuadratic.connection J K V u l m * J.christoffel m k i +
        Linearization.connection J K u l m * Linearization.connection J V m k i) -
      (Linearization.connection J V u l m * Linearization.connection J K m k i +
        J.christoffel u l m * MixedQuadratic.connection J K V m k i))) =
      (∑ m, MixedQuadratic.connection J K V u k m * J.christoffel m l i) +
      (∑ m, (Linearization.connection J K u k m * Linearization.connection J V m l i +
        Linearization.connection J V u k m * Linearization.connection J K m l i)) +
      (∑ m, J.christoffel u k m * MixedQuadratic.connection J K V m l i) -
      (∑ m, MixedQuadratic.connection J K V u l m * J.christoffel m k i) -
      (∑ m, (Linearization.connection J K u l m * Linearization.connection J V m k i +
        Linearization.connection J V u l m * Linearization.connection J K m k i)) -
      ∑ m, J.christoffel u l m * MixedQuadratic.connection J K V m k i := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [hsplit, hA, hB, hC, hD]
  ring

end IsDiagonalJet

namespace IsDiagonalJet
variable {J : CoordinateMetricTwoJet d ℂ} (h : IsDiagonalJet J)
include h

/-- Over an Einstein diagonal background, the mixed scalar variation of two symmetric
perturbations solving the linearized equation is the background trace of the mixed Ricci
variation: all inverse–Ricci cross terms cancel. -/
theorem mixedQuadratic_scalar_eq (K V : CoordinateMetricTwoJet d ℂ) (c : ℂ)
    (hJ : ∀ i j, J.ricci i j = c * J.metric i j)
    (hK : ∀ i j, Linearization.ricci J K i j = c * K.metric i j)
    (hV : ∀ i j, Linearization.ricci J V i j = c * V.metric i j)
    (hKs : ∀ i j, K.metric i j = K.metric j i) (hVs : ∀ i j, V.metric i j = V.metric j i) :
    MixedQuadratic.scalar J K V = ∑ i, (J.metric i i)⁻¹ * MixedQuadratic.ricci J K V i i := by
  unfold MixedQuadratic.scalar
  simp only [hJ, hK, hV, h.linearization_inverse_apply, h.inv_apply, h.mixedQuadratic_inverse_apply]
  have hterm : ∀ i j, ((∑ p, (V.metric i p * K.metric p j + K.metric i p * V.metric p j) /
      (J.metric i i * J.metric p p * J.metric j j)) * (c * J.metric i j) +
      -(K.metric i j / (J.metric i i * J.metric j j)) * (c * V.metric i j)) +
      (-(V.metric i j / (J.metric i i * J.metric j j)) * (c * K.metric i j) +
      (if i = j then (J.metric i i)⁻¹ else 0) * MixedQuadratic.ricci J K V i j) =
      (if i = j then c * ∑ p, (V.metric i p * K.metric p i + K.metric i p * V.metric p i) /
        (J.metric i i * J.metric p p) else 0) -
      2 * c * K.metric i j * V.metric i j / (J.metric i i * J.metric j j) +
      (if i = j then (J.metric i i)⁻¹ * MixedQuadratic.ricci J K V i j else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      have hg := h.metric_diag_ne_zero i
      have hsum : (∑ p, (V.metric i p * K.metric p i + K.metric i p * V.metric p i) /
          (J.metric i i * J.metric p p * J.metric i i)) * (c * J.metric i i) =
          c * ∑ p, (V.metric i p * K.metric p i + K.metric i p * V.metric p i) /
            (J.metric i i * J.metric p p) := by
        rw [Finset.mul_sum, Finset.sum_mul]
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
  have hsq : ∑ i, ∑ j, 2 * c * K.metric i j * V.metric i j / (J.metric i i * J.metric j j) =
      ∑ i, c * ∑ p, (V.metric i p * K.metric p i + K.metric i p * V.metric p i) /
        (J.metric i i * J.metric p p) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [hKs p i, hVs p i]
    ring
  rw [hsq]
  ring

/-- The mixed Einstein variation over an Einstein diagonal background reduces to the mixed Ricci
variation minus half the background metric times its background trace. -/
theorem mixedQuadratic_einstein_eq (K V : CoordinateMetricTwoJet d ℂ) (c : ℂ)
    (hJ : ∀ i j, J.ricci i j = c * J.metric i j)
    (hK : ∀ i j, Linearization.ricci J K i j = c * K.metric i j)
    (hV : ∀ i j, Linearization.ricci J V i j = c * V.metric i j)
    (hKs : ∀ i j, K.metric i j = K.metric j i) (hVs : ∀ i j, V.metric i j = V.metric j i)
    (i j : Fin d) :
    MixedQuadratic.einstein J K V i j = MixedQuadratic.ricci J K V i j -
      (1 / 2 : ℂ) * (∑ u, (J.metric u u)⁻¹ * MixedQuadratic.ricci J K V u u) * J.metric i j := by
  unfold MixedQuadratic.einstein
  rw [h.mixedQuadratic_scalar_eq K V c hJ hK hV hKs hVs, h.linearization_scalar_eq_zero K c hJ hK,
    h.linearization_scalar_eq_zero V c hJ hV]
  ring

end IsDiagonalJet

end GaloisForLFunctions.HTGeometry.CoordinateMetricTwoJet
