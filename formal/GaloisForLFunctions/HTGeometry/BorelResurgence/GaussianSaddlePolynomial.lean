import GaloisForLFunctions.HTGeometry.GomesFiniteQuadraticCurvature

/-!
# The polynomial information retained by Gaussian saddle actions

Eliminating the Gaussian saddle equation replaces a polynomial free energy `P` by
`P - X P'/2`. This diagonal operator erases exactly the quadratic coefficient. Its image consists
exactly of polynomials with zero quadratic coefficient, and coefficientwise inversion recovers
every other term. For the Gomes scalar densities, the erased coefficient decides finite mass.
-/

open Polynomial MeasureTheory
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The free-energy polynomial after eliminating the Gaussian saddle equation. -/
def gaussianSaddlePolynomial (P : ℝ[X]) : ℝ[X] := P - (1 / 2 : ℝ) • (X * P.derivative)

/-- Each homogeneous degree is multiplied by `1 - n/2`. -/
theorem coeff_gaussianSaddlePolynomial (P : ℝ[X]) (n : ℕ) :
    (gaussianSaddlePolynomial P).coeff n = (1 - (n : ℝ) / 2) * P.coeff n := by
  cases n with
  | zero => simp [gaussianSaddlePolynomial]
  | succ n =>
      simp only [gaussianSaddlePolynomial, coeff_sub, coeff_smul, smul_eq_mul,
        coeff_X_mul, coeff_derivative, Nat.cast_add, Nat.cast_one]
      ring

private theorem saddle_degree_factor_ne_zero {n : ℕ} (hn : n ≠ 2) :
    (1 - (n : ℝ) / 2) ≠ 0 := by
  intro h
  have he : (n : ℝ) = 2 := by linarith only [h]
  exact hn (by exact_mod_cast he)

/-- The quadratic monomial is the entire kernel, with no further invisible polynomial data. -/
theorem gaussianSaddlePolynomial_eq_zero_iff (P : ℝ[X]) :
    gaussianSaddlePolynomial P = 0 ↔ ∃ a : ℝ, P = C a * X ^ 2 := by
  constructor
  · intro h
    refine ⟨P.coeff 2, ?_⟩
    ext n
    by_cases hn : n = 2
    · subst n
      simp
    · have he := congrArg (fun Q : ℝ[X] => Q.coeff n) h
      rw [coeff_gaussianSaddlePolynomial, coeff_zero] at he
      have hp := (mul_eq_zero.mp he).resolve_left (saddle_degree_factor_ne_zero hn)
      simp [coeff_C_mul, coeff_X_pow, hn, hp]
  · rintro ⟨a, rfl⟩
    ext n
    rw [coeff_gaussianSaddlePolynomial]
    by_cases hn : n = 2 <;> simp [coeff_C_mul, coeff_X_pow, hn]

/-- Equal saddle actions identify exactly polynomials differing by a quadratic monomial. -/
theorem gaussianSaddlePolynomial_eq_iff (P Q : ℝ[X]) :
    gaussianSaddlePolynomial P = gaussianSaddlePolynomial Q ↔
      ∃ a : ℝ, P - Q = C a * X ^ 2 := by
  have hsub : gaussianSaddlePolynomial (P - Q) =
      gaussianSaddlePolynomial P - gaussianSaddlePolynomial Q := by
    unfold gaussianSaddlePolynomial
    rw [derivative_sub, mul_sub, smul_sub]
    abel
  rw [← gaussianSaddlePolynomial_eq_zero_iff, hsub, sub_eq_zero]

/-- Coefficientwise inverse away from the unique quadratic resonance. -/
def gaussianSaddleReconstruction (P : ℝ[X]) : ℝ[X] :=
  ∑ n ∈ P.support, monomial n (P.coeff n / (1 - (n : ℝ) / 2))

theorem coeff_gaussianSaddleReconstruction (P : ℝ[X]) (n : ℕ) :
    (gaussianSaddleReconstruction P).coeff n = P.coeff n / (1 - (n : ℝ) / 2) := by
  classical
  simp only [gaussianSaddleReconstruction, finsetSum_coeff, coeff_monomial]
  by_cases hn : n ∈ P.support
  · simp [hn]
  · have hz : P.coeff n = 0 := by simpa using hn
    simp [hn, hz]

/-- Reconstruction recovers every coefficient except the invisible quadratic coefficient. -/
theorem gaussianSaddleReconstruction_action (P : ℝ[X]) :
    gaussianSaddleReconstruction (gaussianSaddlePolynomial P) =
      P - monomial 2 (P.coeff 2) := by
  ext n
  rw [coeff_gaussianSaddleReconstruction, coeff_gaussianSaddlePolynomial,
    coeff_sub, coeff_monomial]
  by_cases hn : n = 2
  · subst n
    norm_num
  · simp only [if_neg (Ne.symm hn), sub_zero]
    exact (div_eq_iff (saddle_degree_factor_ne_zero hn)).mpr (by ring)

/-- Applying the saddle action after reconstruction gives the same exact quadratic projection. -/
theorem gaussianSaddlePolynomial_reconstruction (P : ℝ[X]) :
    gaussianSaddlePolynomial (gaussianSaddleReconstruction P) =
      P - monomial 2 (P.coeff 2) := by
  ext n
  rw [coeff_gaussianSaddlePolynomial, coeff_gaussianSaddleReconstruction,
    coeff_sub, coeff_monomial]
  by_cases hn : n = 2
  · subst n
    norm_num
  · simp only [if_neg (Ne.symm hn), sub_zero]
    rw [← mul_div_assoc]
    exact (div_eq_iff (saddle_degree_factor_ne_zero hn)).mpr (by ring)

/-- Vanishing quadratic coefficient is the sole obstruction to being a Gaussian saddle action. -/
theorem exists_gaussianSaddlePolynomial_iff (Q : ℝ[X]) :
    (∃ P : ℝ[X], gaussianSaddlePolynomial P = Q) ↔ Q.coeff 2 = 0 := by
  constructor
  · rintro ⟨P, rfl⟩
    norm_num [coeff_gaussianSaddlePolynomial]
  · intro h
    refine ⟨gaussianSaddleReconstruction Q, ?_⟩
    rw [gaussianSaddlePolynomial_reconstruction, h, monomial_zero_right, sub_zero]

/-- For scalar reconstruction densities, the invisible quadratic coefficient decides finite mass. -/
theorem gaussianSaddle_gomes_quadratic_classification (a b c : ℝ) :
    gaussianSaddlePolynomial (C a * X ^ 2 + C b * X + C c) = C (b / 2) * X + C c ∧
      (IsFiniteMeasure (gomesDilatonMeasure (C a * X ^ 2 + C b * X + C c)) ↔ a < 0) := by
  refine ⟨?_, gomesDilatonMeasure_quadratic_finite_iff a b c⟩
  ext n
  rw [coeff_gaussianSaddlePolynomial]
  by_cases h0 : n = 0
  · subst n; norm_num
  by_cases h1 : n = 1
  · subst n; norm_num; ring
  by_cases h2 : n = 2
  · subst n; norm_num
  simp [h0, h1, h2]

end

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.coeff_gaussianSaddlePolynomial
#print axioms GaloisForLFunctions.HTGeometry.gaussianSaddlePolynomial_eq_zero_iff
#print axioms GaloisForLFunctions.HTGeometry.gaussianSaddlePolynomial_eq_iff
#print axioms GaloisForLFunctions.HTGeometry.coeff_gaussianSaddleReconstruction
#print axioms GaloisForLFunctions.HTGeometry.gaussianSaddleReconstruction_action
#print axioms GaloisForLFunctions.HTGeometry.gaussianSaddlePolynomial_reconstruction
#print axioms GaloisForLFunctions.HTGeometry.exists_gaussianSaddlePolynomial_iff
#print axioms GaloisForLFunctions.HTGeometry.gaussianSaddle_gomes_quadratic_classification
