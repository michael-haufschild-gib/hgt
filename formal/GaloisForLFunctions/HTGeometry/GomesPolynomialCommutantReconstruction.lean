import GaloisForLFunctions.HTGeometry.GomesPolynomialConnectionBicommutant
import GaloisForLFunctions.HTGeometry.GomesDilatonConnectionReconstruction

/-!
# What the concrete symmetry algebra reconstructs

Equality of the actual connection commutant subalgebras recovers the derivative of
the coefficient, hence the coefficient up to an additive constant. One scalar anchor
recovers the coefficient exactly. This distinguishes equality of symmetry sets from
abstract matrix-algebra descriptions and from structured conjugacy.
-/

noncomputable section
open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- The commutator of two polynomial connections measures the derivative of their difference. -/
theorem gomesPolynomialFirstOrder_pair_commutator (A B P : ℝ[X]) :
    gomesPolynomialFirstOrderLinearMap A (gomesPolynomialFirstOrderLinearMap B P) -
      gomesPolynomialFirstOrderLinearMap B (gomesPolynomialFirstOrderLinearMap A P) =
        (A.derivative - B.derivative) * P := by
  change gomesPolynomialFirstOrderOperator A (gomesPolynomialFirstOrderOperator B P) -
    gomesPolynomialFirstOrderOperator B (gomesPolynomialFirstOrderOperator A P) = _
  simp only [gomesPolynomialFirstOrderOperator, derivative_sub, derivative_mul]
  ring

/-- Two first-order connections commute exactly when their coefficients have the same derivative. -/
theorem gomesPolynomialFirstOrder_pair_commute_iff (A B : ℝ[X]) :
    (gomesPolynomialFirstOrderLinearMap A).comp (gomesPolynomialFirstOrderLinearMap B) =
      (gomesPolynomialFirstOrderLinearMap B).comp (gomesPolynomialFirstOrderLinearMap A) ↔
        A.derivative = B.derivative := by
  constructor
  · intro h
    have h1 := congrArg (fun E : ℝ[X] →ₗ[ℝ] ℝ[X] => E 1) h
    simp only [LinearMap.comp_apply] at h1
    have hc := gomesPolynomialFirstOrder_pair_commutator A B 1
    rw [h1, sub_self, mul_one] at hc
    exact sub_eq_zero.mp hc.symm
  · intro h
    apply LinearMap.ext
    intro P
    apply sub_eq_zero.mp
    change gomesPolynomialFirstOrderLinearMap A (gomesPolynomialFirstOrderLinearMap B P) -
      gomesPolynomialFirstOrderLinearMap B (gomesPolynomialFirstOrderLinearMap A P) = 0
    rw [gomesPolynomialFirstOrder_pair_commutator, h, sub_self, zero_mul]

/-- Adding a constant coefficient shifts the connection by the matching scalar identity. -/
theorem gomesPolynomialFirstOrder_constant_shift_apply (A P : ℝ[X]) (c : ℝ) :
    gomesPolynomialFirstOrderLinearMap (A + C c) P =
      gomesPolynomialFirstOrderLinearMap A P - c • P := by
  change P.derivative - (A + C c) * P = P.derivative - A * P - c • P
  rw [smul_eq_C_mul]
  ring

/-- Commuting maps are unchanged by any constant shift in the connection coefficient. -/
theorem gomesPolynomialConnectionCommutant_shift_mem_iff (A : ℝ[X]) (c : ℝ)
    (E : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    E ∈ gomesPolynomialConnectionCommutantAlgebra (A + C c) ↔
      E ∈ gomesPolynomialConnectionCommutantAlgebra A := by
  rw [gomesPolynomialConnectionCommutant_mem_iff, gomesPolynomialConnectionCommutant_mem_iff]
  constructor
  · intro h
    apply LinearMap.ext
    intro P
    have hp := congrArg (fun F : ℝ[X] →ₗ[ℝ] ℝ[X] => F P) h
    simp only [LinearMap.comp_apply, gomesPolynomialFirstOrder_constant_shift_apply,
      map_sub, map_smul] at hp
    exact sub_left_inj.mp hp
  · intro h
    apply LinearMap.ext
    intro P
    have hp := congrArg (fun F : ℝ[X] →ₗ[ℝ] ℝ[X] => F P) h
    simp only [LinearMap.comp_apply, gomesPolynomialFirstOrder_constant_shift_apply,
      map_sub, map_smul]
    exact congrArg (fun Q : ℝ[X] => Q - c • E P) hp

/-- Constant coefficient shifts preserve the entire concrete symmetry subalgebra. -/
theorem gomesPolynomialConnectionCommutant_shift (A : ℝ[X]) (c : ℝ) :
    gomesPolynomialConnectionCommutantAlgebra (A + C c) =
      gomesPolynomialConnectionCommutantAlgebra A := by
  ext E
  exact gomesPolynomialConnectionCommutant_shift_mem_iff A c E

/-- Equality of actual symmetry subalgebras reconstructs exactly the coefficient derivative. -/
theorem gomesPolynomialConnectionCommutant_eq_iff (A B : ℝ[X]) :
    gomesPolynomialConnectionCommutantAlgebra A = gomesPolynomialConnectionCommutantAlgebra B ↔
      A.derivative = B.derivative := by
  constructor
  · intro h
    have ht : gomesPolynomialFirstOrderLinearMap A ∈ gomesPolynomialConnectionCommutantAlgebra A :=
      (gomesPolynomialConnectionCommutant_mem_iff A _).mpr rfl
    rw [h] at ht
    exact (gomesPolynomialFirstOrder_pair_commute_iff A B).mp
      ((gomesPolynomialConnectionCommutant_mem_iff B _).mp ht)
  · intro h
    obtain ⟨c, hc⟩ := (gomesDilatonDerivative_eq_iff A B).mp h
    rw [hc, gomesPolynomialConnectionCommutant_shift]

/-- The exact ambiguity in reconstructing a coefficient from its full symmetry algebra is constant shift. -/
theorem gomesPolynomialConnectionCommutant_fibers (A B : ℝ[X]) :
    gomesPolynomialConnectionCommutantAlgebra A = gomesPolynomialConnectionCommutantAlgebra B ↔
      ∃ c : ℝ, A = B + C c := by
  rw [gomesPolynomialConnectionCommutant_eq_iff, gomesDilatonDerivative_eq_iff]

/-- One scalar anchor makes the full symmetry algebra sufficient for exact coefficient reconstruction. -/
theorem gomesPolynomialConnectionCommutant_anchored_iff (A B : ℝ[X]) :
    (gomesPolynomialConnectionCommutantAlgebra A = gomesPolynomialConnectionCommutantAlgebra B ∧
      A.coeff 0 = B.coeff 0) ↔ A = B := by
  constructor
  · rintro ⟨h, h0⟩
    obtain ⟨c, hc⟩ := (gomesPolynomialConnectionCommutant_fibers A B).mp h
    have he := congrArg (fun P : ℝ[X] => P.coeff 0) hc
    simp only [coeff_add, coeff_C_zero] at he
    have hz : c = 0 := by linarith
    simpa only [hz, map_zero, add_zero] using hc
  · rintro rfl
    exact ⟨rfl, rfl⟩

end GaloisForLFunctions.HTGeometry
