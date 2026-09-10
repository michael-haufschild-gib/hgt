import GaloisForLFunctions.HTGeometry.GomesCenteredHamiltonianTensorProbes

/-!
# The finite quadratic boundary of the scalar reconstruction experiment

The energy-reference ambiguity exposed by the Gomes reconstruction experiment has a
sharp integrability boundary. A quadratic profile defines finite mass precisely for
negative curvature. Every finite profile with vanishing third derivative belongs to
this explicit family; its curvature is therefore strictly negative, without assumptions.
-/

noncomputable section
open Polynomial MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- Arbitrary affine terms do not affect the exact negative-coefficient criterion for a quadratic. -/
theorem gomesDilatonMeasure_quadratic_finite_iff (a b c : ℝ) :
    IsFiniteMeasure (gomesDilatonMeasure (C a * X ^ 2 + C b * X + C c)) ↔ a < 0 := by
  have ht := gomesPolynomialAffineTilt_finite_iff (C a * X ^ 2) b c
  have hshape : gomesPolynomialAffineTilt (C a * X ^ 2) b c =
      C a * X ^ 2 + C b * X + C c := by
    unfold gomesPolynomialAffineTilt
    ring
  rw [hshape] at ht
  rw [ht, gomesDilatonMeasure_finite_polynomial_iff]
  constructor
  · rintro ⟨_, _, h⟩
    simpa only [leadingCoeff_C_mul_X_pow] using h
  · intro h
    rw [natDegree_C_mul_X_pow 2 a h.ne, leadingCoeff_C_mul_X_pow]
    exact ⟨Nat.zero_lt_succ 1, ⟨1, rfl⟩, h⟩

/-- Curvature parametrization gives the exact sign of a finite quadratic density. -/
theorem gomesDilatonMeasure_curvature_quadratic_finite_iff (k a b : ℝ) :
    IsFiniteMeasure (gomesDilatonMeasure (C (k / 2) * X ^ 2 + C a * X + C b)) ↔ k < 0 := by
  rw [gomesDilatonMeasure_quadratic_finite_iff]
  constructor <;> intro h <;> linarith

/-- Finite mass and a prescribed constant curvature have an explicit negative quadratic classification. -/
theorem gomesDilatonMeasure_constant_curvature_iff (H : ℝ[X]) (k : ℝ) :
    (IsFiniteMeasure (gomesDilatonMeasure H) ∧ H.derivative.derivative = C k) ↔
      k < 0 ∧ ∃ a b : ℝ, H = C (k / 2) * X ^ 2 + C a * X + C b := by
  constructor
  · rintro ⟨hf, hd⟩
    obtain ⟨a, b, hab⟩ := (gomesDilaton_secondDerivative_constant_iff H k).mp hd
    refine ⟨?_, a, b, hab⟩
    apply (gomesDilatonMeasure_curvature_quadratic_finite_iff k a b).mp
    rwa [← hab]
  · rintro ⟨hk, a, b, hab⟩
    refine ⟨?_, (gomesDilaton_secondDerivative_constant_iff H k).mpr ⟨a, b, hab⟩⟩
    rw [hab]
    exact (gomesDilatonMeasure_curvature_quadratic_finite_iff k a b).mpr hk

/-- Constant curvature of a finite profile is automatically strictly negative. -/
theorem gomesFinitePolynomialProfile_constant_curvature_iff (P : GomesFinitePolynomialProfile) (k : ℝ) :
    P.val.derivative.derivative = C k ↔ k < 0 ∧ P.val.derivative.derivative = C k := by
  constructor
  · intro h
    exact ⟨((gomesDilatonMeasure_constant_curvature_iff P.val k).mp ⟨P.property, h⟩).1, h⟩
  · exact And.right

/-- Vanishing third derivative in the finite sector is exactly the negative-curvature quadratic family. -/
theorem gomesFinitePolynomialProfile_third_derivative_zero_iff (P : GomesFinitePolynomialProfile) :
    P.val.derivative.derivative.derivative = 0 ↔
      ∃ k : ℝ, k < 0 ∧ P.val.derivative.derivative = C k := by
  constructor
  · intro h
    let k := P.val.derivative.derivative.coeff 0
    have hk : P.val.derivative.derivative = C k := eq_C_of_derivative_eq_zero h
    exact ⟨k, (gomesFinitePolynomialProfile_constant_curvature_iff P k).mp hk⟩
  · rintro ⟨k, _, hk⟩
    rw [hk, derivative_C]

/-- Every finite quadratic profile carries its unique negative constant curvature at the origin. -/
theorem gomesFinitePolynomialProfile_quadratic_origin_curvature
    (P : {P : GomesFinitePolynomialProfile // P.val.derivative.derivative.derivative = 0}) :
    P.val.val.derivative.derivative.eval 0 < 0 ∧
      P.val.val.derivative.derivative = C (P.val.val.derivative.derivative.eval 0) := by
  obtain ⟨k, hk, hd⟩ := (gomesFinitePolynomialProfile_third_derivative_zero_iff P.val).mp P.property
  rw [hd, eval_C]
  exact ⟨hk, rfl⟩

end GaloisForLFunctions.HTGeometry
