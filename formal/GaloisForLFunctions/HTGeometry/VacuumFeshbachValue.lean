import GaloisForLFunctions.HTGeometry.MomentFunctionalPositivity

/-!
# Vacuum Feshbach reduction for moment quadratic forms

Feshbach's projection formalism eliminates a chosen channel by a Schur complement.  For a real
moment functional, choose the constant polynomial as the one-dimensional vacuum channel.  Every
polynomial then splits into its constant coefficient and a tail with zero constant coefficient.
Completing the square gives the exact effective quadratic value on that tail.

This is a static value relation.  It introduces no evolution, spectrum, or positivity assumption.
When the vacuum value `s 0` is positive, positivity of the full Hankel form is equivalent to
nonnegativity of the Feshbach remainder only on zero-constant tails.

The projection-operator provenance is H. Feshbach, *A unified theory of nuclear reactions*,
Ann. Phys. 5 (1958), 357--390, DOI 10.1016/0003-4916(58)90007-1, and H. Feshbach,
*A unified theory of nuclear reactions. II*, Ann. Phys. 19 (1962), 287--313,
DOI 10.1016/0003-4916(62)90221-X.
-/

open Polynomial

namespace HTGeometry

noncomputable section

/-- Remove the one-dimensional constant-polynomial channel. -/
def polynomialVacuumTail {R : Type*} [Ring R] (p : Polynomial R) : Polynomial R :=
  p - C (p.coeff 0)

@[simp]
theorem polynomialVacuumTail_coeff_zero {R : Type*} [Ring R] (p : Polynomial R) :
    (polynomialVacuumTail p).coeff 0 = 0 := by
  simp [polynomialVacuumTail]

theorem C_coeff_zero_add_polynomialVacuumTail
    {R : Type*} [Ring R] (p : Polynomial R) :
    C (p.coeff 0) + polynomialVacuumTail p = p := by
  simp [polynomialVacuumTail]

/-- The scalar Schur complement obtained after eliminating the constant-polynomial channel. -/
def momentVacuumFeshbachRemainder (s : ℕ → ℝ) (q : Polynomial ℝ) : ℝ :=
  momentFunctional s (q ^ 2) - momentFunctional s q ^ 2 / s 0

/-- Quotient-free two-channel determinant between the constant vacuum and one observable. -/
def momentVacuumRobertsonDeterminant (s : ℕ → ℝ) (q : Polynomial ℝ) : ℝ :=
  s 0 * momentFunctional s (q ^ 2) - momentFunctional s q ^ 2

/-- Subtract the moment-functional mean of `q`.  This is the canonical representative orthogonal
to the constant channel whenever `s 0` is nonzero. -/
def momentVacuumCenteredPolynomial (s : ℕ → ℝ) (q : Polynomial ℝ) : Polynomial ℝ :=
  q - C (momentFunctional s q / s 0)

theorem momentFunctional_one_eq (s : ℕ → ℝ) :
    momentFunctional s (1 : Polynomial ℝ) = s 0 := by
  simpa using momentFunctional_X_pow s 0

theorem momentFunctional_C (s : ℕ → ℝ) (c : ℝ) :
    momentFunctional s (C c) = c * s 0 := by
  calc
    momentFunctional s (C c) = momentFunctional s (c • (1 : Polynomial ℝ)) := by
      congr 1
      simp [Polynomial.smul_eq_C_mul]
    _ = c * momentFunctional s (1 : Polynomial ℝ) := momentFunctional_smul s c 1
    _ = c * s 0 := by rw [momentFunctional_one_eq]

theorem momentFunctional_C_mul (s : ℕ → ℝ) (c : ℝ) (q : Polynomial ℝ) :
    momentFunctional s (C c * q) = c * momentFunctional s q := by
  rw [← Polynomial.smul_eq_C_mul, momentFunctional_smul]

/-- Block expansion before eliminating the constant channel. -/
theorem momentFunctional_C_add_sq
    (s : ℕ → ℝ) (c : ℝ) (q : Polynomial ℝ) :
    momentFunctional s ((C c + q) ^ 2) =
      s 0 * c ^ 2 + 2 * c * momentFunctional s q +
        momentFunctional s (q ^ 2) := by
  have hpoly :
      (C c + q) ^ 2 = C (c ^ 2) + C (2 * c) * q + q ^ 2 := by
    ring
  rw [hpoly, momentFunctional_add, momentFunctional_add,
    momentFunctional_C, momentFunctional_C_mul]
  ring

/-- **Vacuum Feshbach value identity.**  The full quadratic value is the positive vacuum square
plus the scalar Schur complement on the zero-constant sector. -/
theorem momentFunctional_C_add_sq_eq_vacuumSquare_add_feshbach
    (s : ℕ → ℝ) (h0 : s 0 ≠ 0) (c : ℝ) (q : Polynomial ℝ) :
    momentFunctional s ((C c + q) ^ 2) =
      s 0 * (c + momentFunctional s q / s 0) ^ 2 +
        momentVacuumFeshbachRemainder s q := by
  rw [momentFunctional_C_add_sq]
  unfold momentVacuumFeshbachRemainder
  field_simp [h0]
  ring

/-- The canonically centered observable has exactly the Feshbach/Schur-complement value. -/
theorem momentFunctional_momentVacuumCenteredPolynomial_sq
    (s : ℕ → ℝ) (h0 : s 0 ≠ 0) (q : Polynomial ℝ) :
    momentFunctional s ((momentVacuumCenteredPolynomial s q) ^ 2) =
      momentVacuumFeshbachRemainder s q := by
  have hpoly :
      momentVacuumCenteredPolynomial s q =
        C (-(momentFunctional s q / s 0)) + q := by
    unfold momentVacuumCenteredPolynomial
    ring
  rw [hpoly, momentFunctional_C_add_sq_eq_vacuumSquare_add_feshbach s h0]
  ring

/-- The centered representative is orthogonal to the vacuum for the moment bilinear form. -/
theorem momentFunctional_momentVacuumCenteredPolynomial
    (s : ℕ → ℝ) (h0 : s 0 ≠ 0) (q : Polynomial ℝ) :
    momentFunctional s (momentVacuumCenteredPolynomial s q) = 0 := by
  unfold momentVacuumCenteredPolynomial
  have hsub :
      q - C (momentFunctional s q / s 0) =
        q + C (-(momentFunctional s q / s 0)) := by ring
  rw [hsub, momentFunctional_add, momentFunctional_C]
  field_simp [h0]
  ring

/-- Cross-multiplying the Feshbach remainder by the vacuum mass gives exactly the
vacuum--observable Robertson determinant. -/
theorem momentVacuumRobertsonDeterminant_eq_mul_feshbach
    (s : ℕ → ℝ) (h0 : s 0 ≠ 0) (q : Polynomial ℝ) :
    momentVacuumRobertsonDeterminant s q =
      s 0 * momentVacuumFeshbachRemainder s q := by
  unfold momentVacuumRobertsonDeterminant momentVacuumFeshbachRemainder
  field_simp [h0]
  ring

/-- With positive vacuum mass, Feshbach positivity is exactly the quotient-free Robertson
determinant inequality. -/
theorem momentVacuumFeshbachRemainder_nonneg_iff_robertson
    (s : ℕ → ℝ) (h0 : 0 < s 0) (q : Polynomial ℝ) :
    0 ≤ momentVacuumFeshbachRemainder s q ↔
      0 ≤ momentVacuumRobertsonDeterminant s q := by
  rw [momentVacuumRobertsonDeterminant_eq_mul_feshbach s h0.ne',
    mul_nonneg_iff_of_pos_left h0]

/-- Robertson form as the vacuum--observable Cauchy--Schwarz inequality. -/
theorem momentVacuumRobertsonDeterminant_nonneg_iff_cauchySchwarz
    (s : ℕ → ℝ) (q : Polynomial ℝ) :
    0 ≤ momentVacuumRobertsonDeterminant s q ↔
      momentFunctional s q ^ 2 ≤ s 0 * momentFunctional s (q ^ 2) := by
  unfold momentVacuumRobertsonDeterminant
  constructor <;> intro h <;> linarith

/-- **Mori/Feshbach least-squares law.**  The vacuum Schur complement is a lower bound for every
scalar recentering of the observable. -/
theorem momentVacuumFeshbachRemainder_le_shifted_sq
    (s : ℕ → ℝ) (h0 : 0 < s 0) (q : Polynomial ℝ) (c : ℝ) :
    momentVacuumFeshbachRemainder s q ≤
      momentFunctional s ((q - C c) ^ 2) := by
  have hpoly : q - C c = C (-c) + q := by ring
  rw [hpoly,
    momentFunctional_C_add_sq_eq_vacuumSquare_add_feshbach s h0.ne']
  exact le_add_of_nonneg_left (mul_nonneg h0.le (sq_nonneg _))

/-- The canonical moment mean attains the scalar least-squares lower bound exactly. -/
theorem exists_shifted_sq_eq_momentVacuumFeshbachRemainder
    (s : ℕ → ℝ) (h0 : s 0 ≠ 0) (q : Polynomial ℝ) :
    ∃ c : ℝ,
      momentFunctional s ((q - C c) ^ 2) =
        momentVacuumFeshbachRemainder s q := by
  refine ⟨momentFunctional s q / s 0, ?_⟩
  exact momentFunctional_momentVacuumCenteredPolynomial_sq s h0 q

/-- **One-channel positivity reduction.**  If the vacuum value is positive, the complete moment
quadratic form is nonnegative exactly when the Feshbach remainder is nonnegative on polynomial
tails with zero constant coefficient. -/
theorem all_momentFunctional_sq_nonneg_iff_vacuumFeshbach
    (s : ℕ → ℝ) (h0 : 0 < s 0) :
    (∀ p : Polynomial ℝ, 0 ≤ momentFunctional s (p ^ 2)) ↔
      ∀ q : Polynomial ℝ, q.coeff 0 = 0 →
        0 ≤ momentVacuumFeshbachRemainder s q := by
  constructor
  · intro h q _hq
    rw [← momentFunctional_momentVacuumCenteredPolynomial_sq s h0.ne']
    exact h _
  · intro h p
    let q : Polynomial ℝ := polynomialVacuumTail p
    let c : ℝ := p.coeff 0
    have hq : q.coeff 0 = 0 := by
      exact polynomialVacuumTail_coeff_zero p
    have hrem : 0 ≤ momentVacuumFeshbachRemainder s q := h q hq
    have hsplit : C c + q = p := by
      exact C_coeff_zero_add_polynomialVacuumTail p
    rw [← hsplit,
      momentFunctional_C_add_sq_eq_vacuumSquare_add_feshbach s h0.ne']
    exact add_nonneg (mul_nonneg h0.le (sq_nonneg _)) hrem

/-- Equivalent centered-observable form of the one-channel reduction. -/
theorem all_momentFunctional_sq_nonneg_iff_vacuumCentered
    (s : ℕ → ℝ) (h0 : 0 < s 0) :
    (∀ p : Polynomial ℝ, 0 ≤ momentFunctional s (p ^ 2)) ↔
      ∀ q : Polynomial ℝ, q.coeff 0 = 0 →
        0 ≤ momentFunctional s ((momentVacuumCenteredPolynomial s q) ^ 2) := by
  rw [all_momentFunctional_sq_nonneg_iff_vacuumFeshbach s h0]
  constructor
  · intro h q hq
    rw [momentFunctional_momentVacuumCenteredPolynomial_sq s h0.ne']
    exact h q hq
  · intro h q hq
    rw [← momentFunctional_momentVacuumCenteredPolynomial_sq s h0.ne']
    exact h q hq

end

end HTGeometry
