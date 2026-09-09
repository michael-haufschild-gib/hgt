import GaloisForLFunctions.HTGeometry.CoordinateEinsteinComplexLinearization
import GaloisForLFunctions.HTGeometry.ComplexMetricCompatibility

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace GaloisForLFunctions.HTGeometry.EinsteinActionBoundary
noncomputable section
variable {d : ℕ}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ

private theorem cycle3 (f : Fin d → Fin d → Fin d → ℂ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
private theorem cycle4 (f : Fin d → Fin d → Fin d → Fin d → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ e, f a b c e) = ∑ b, ∑ c, ∑ e, ∑ a, f a b c e := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  exact cycle3 _
private theorem perm3210 (f : Fin d → Fin d → Fin d → Fin d → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ e, f a b c e) = ∑ e, ∑ c, ∑ a, ∑ b, f a b c e := by
  rw [cycle4 f, cycle4]
  rw [Finset.sum_comm]
private theorem perm1320 (f : Fin d → Fin d → Fin d → Fin d → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ e, f a b c e) = ∑ b, ∑ e, ∑ c, ∑ a, f a b c e := by
  rw [cycle4 f]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
private theorem perm3021 (f : Fin d → Fin d → Fin d → Fin d → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ e, f a b c e) = ∑ e, ∑ a, ∑ c, ∑ b, f a b c e := by
  rw [cycle4 f, cycle4, cycle4]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
private theorem swap14 (f : Fin d → Fin d → Fin d → Fin d → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ e, f a b c e) = ∑ e, ∑ b, ∑ c, ∑ a, f a b c e := by
  rw [cycle4 f, cycle4, cycle4]
  apply Finset.sum_congr rfl
  intro e _
  exact cycle3 _

private theorem contraction_divergence (G : Mat)
    (A D : Fin d → Fin d → Fin d → ℂ)
    (S : Fin d → Fin d → Fin d → Fin d → ℂ)
    (hA : ∀ u i j, A u i j = A u j i) :
    (∑ i, ∑ j, G i j * ∑ u, (S u u j i - S j u u i +
      ∑ m, ((D u u m * A m j i + A u u m * D m j i) -
        (D u j m * A m u i + A u j m * D m u i)))) =
    ∑ a, ((∑ i, ∑ j,
      ((-(∑ b, (A i a b * G b j + G i b * A j a b))) * D a j i + G i j * S a a j i)) -
      (∑ i, ∑ u,
      ((-(∑ b, (A i a b * G b a + G i b * A a a b))) * D u u i + G i a * S a u u i)) +
      (∑ b, A b b a) * ((∑ i, ∑ j, G i j * D a j i) - ∑ i, ∑ u, G i a * D u u i)) := by
  have hs1 := cycle3 (fun a i j => G i j * S a a j i)
  have hs2 : (∑ a, ∑ i, ∑ u, G i a * S a u u i) =
      ∑ i, ∑ a, ∑ u, G i a * S a u u i := Finset.sum_comm
  have ht1 : (∑ a, ∑ i, ∑ j, ∑ b, A i a b * G b j * D a j i) =
      ∑ i, ∑ j, ∑ u, ∑ m, G i j * D u j m * A m u i := by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      perm3210 (fun a i j b => A i a b * G b j * D a j i)
  have ht2 : (∑ a, ∑ i, ∑ j, ∑ b, G i b * A j a b * D a j i) =
      ∑ i, ∑ j, ∑ u, ∑ m, G i j * A u j m * D m u i := by
    rw [perm1320]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro m _
    rw [hA u m j]
  have ht3 : (∑ a, ∑ i, ∑ u, ∑ b, A i a b * G b a * D u u i) =
      ∑ i, ∑ j, ∑ u, ∑ m, G i j * D u u m * A m j i := by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      perm3021 (fun a i u b => A i a b * G b a * D u u i)
  have ht4 : (∑ a, ∑ i, ∑ u, ∑ b, G i b * A a a b * D u u i) =
      ∑ a, ∑ i, ∑ u, ∑ b, A b b a * G i a * D u u i := by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      swap14 (fun a i u b => G i b * A a a b * D u u i)
  have ht5 : (∑ a, ∑ i, ∑ j, ∑ b, A b b a * G i j * D a j i) =
      ∑ i, ∑ j, ∑ u, ∑ m, G i j * A u u m * D m j i := by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      cycle4 (fun a i j b => A b b a * G i j * D a j i)
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib, mul_add, mul_sub, add_mul,
    neg_mul]
  simp only [← mul_assoc]
  rw [hs1, hs2, ht1, ht2, ht3, ht4, ht5]
  ring

open CoordinateMetricTwoJet CoordinateMetricTwoJet.Linearization
local notation "Jet" => CoordinateMetricTwoJet d ℂ

/-- Connection-variation current of the actual Einstein contraction. -/
def current (J H : Jet) (a : Fin d) : ℂ :=
  (∑ i, ∑ j, J.metric⁻¹ i j * connection J H a j i) -
    ∑ i, ∑ u, J.metric⁻¹ i a * connection J H u u i

/-- Complete spatial jet of the current; both inverse-metric and connection derivatives remain. -/
def currentPartial (J H : Jet) (k a : Fin d) : ℂ :=
  (∑ i, ∑ j, (J.inverseDerivative k i j * connection J H a j i +
    J.metric⁻¹ i j * connectionSpatial J H k a j i)) -
  ∑ i, ∑ u, (J.inverseDerivative k i a * connection J H u u i +
    J.metric⁻¹ i a * connectionSpatial J H k u u i)

/-- The volume divergence includes the connection trace multiplying the current. -/
def divergence (J H : Jet) : ℂ :=
  ∑ a, (currentPartial J H a a + (∑ b, J.christoffel b b a) * current J H a)

/-- The entire contracted Ricci variation equals the current divergence, including every
connection-product term. It follows from the actual metric-derived connection and compatibility. -/
theorem contracted_ricci_eq_divergence (J H : Jet) (hJ : J.metric.det ≠ 0)
    (hs : J.metric.transpose = J.metric)
    (hf : ∀ k i j, J.first k i j = J.first k j i) :
    (∑ i, ∑ j, J.metric⁻¹ i j * Linearization.ricci J H i j) = divergence J H := by
  have hA (u i j : Fin d) : J.christoffel u i j = J.christoffel u j i := by
    unfold CoordinateMetricTwoJet.christoffel
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    rw [hf m i j]
    ring
  unfold divergence currentPartial current
  simp_rw [CoordinateMetricTwoJet.inverse_compatibility J hJ hs hf]
  simpa only [Linearization.ricci, Linearization.curvature, Matrix.neg_apply, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply, connectionMatrix, Finset.sum_add_distrib] using
    contraction_divergence J.metric⁻¹ J.christoffel (connection J H) (connectionSpatial J H) hA

end
end GaloisForLFunctions.HTGeometry.EinsteinActionBoundary
