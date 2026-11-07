import GaloisForLFunctions.ThetaCuspSections.WeightedLegendreDerivatives

/-!
# Degrees and leading coefficients of weighted Legendre modes

Bonnet's recurrence gives the exact polynomial degree. Formal
differentiation retains the falling leading product, so the shifted
derivatives form a degree-preserving polynomial family.
-/

open Polynomial
noncomputable section
namespace GaloisForLFunctions.ThetaCuspSections
open GaloisForLFunctions.SelectivePositivityAndThresholdLaws

private theorem legendrePoly_degree_and_lead (n : ℕ) :
    (legendrePoly n).natDegree = n ∧ (legendrePoly n).leadingCoeff = legendreLead n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · norm_num [legendrePoly, legendreLead]
    · norm_num [legendrePoly, legendreLead]
    · have hprev := ih n (by omega)
      have hcur := ih (n + 1) (by omega)
      have hne : legendrePoly (n + 1) ≠ 0 := by
        intro hz
        have hh := congrArg Polynomial.leadingCoeff hz
        rw [hcur.2, leadingCoeff_zero] at hh
        exact (legendreLead_pos (n + 1)).ne' hh
      let A : ℝ[X] := C (2 * (n : ℝ) + 3) * X * legendrePoly (n + 1)
      let B : ℝ[X] := C ((n : ℝ) + 1) * legendrePoly n
      have hA : A.natDegree = n + 2 := by
        dsimp only [A]
        rw [mul_assoc, natDegree_C_mul (by positivity : 2 * (n : ℝ) + 3 ≠ 0),
          natDegree_X_mul hne, hcur.1]
      have hB : B.natDegree = n := by
        dsimp only [B]
        rw [natDegree_C_mul (by positivity : (n : ℝ) + 1 ≠ 0), hprev.1]
      have hlt : B.natDegree < A.natDegree := by rw [hA, hB]; omega
      have hAB := natDegree_sub_eq_left_of_natDegree_lt hlt
      have hlead := leadingCoeff_sub_of_degree_lt (Polynomial.degree_lt_degree hlt)
      change (C (1 / ((n : ℝ) + 2)) * (A - B)).natDegree = n + 2 ∧
        (C (1 / ((n : ℝ) + 2)) * (A - B)).leadingCoeff = legendreLead (n + 2)
      constructor
      · rw [natDegree_C_mul (by positivity : 1 / ((n : ℝ) + 2) ≠ 0), hAB, hA]
      · rw [leadingCoeff_mul, leadingCoeff_C, hlead]
        simp only [A, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X, mul_one, hcur.2]
        conv_rhs => rw [legendreLead]
        push_cast
        ring

theorem legendrePoly_natDegree (n : ℕ) : (legendrePoly n).natDegree = n :=
  (legendrePoly_degree_and_lead n).1

theorem legendrePoly_leadingCoeff (n : ℕ) : (legendrePoly n).leadingCoeff = legendreLead n :=
  (legendrePoly_degree_and_lead n).2

/-- Differentiation lowers the exact degree until the polynomial becomes constant or zero. -/
theorem legendreDerivative_natDegree (n r : ℕ) :
    (legendreDerivative n r).natDegree = n - r := by
  induction r with
  | zero => simpa only [legendreDerivative, Nat.sub_zero] using legendrePoly_natDegree n
  | succ r ih =>
    rw [legendreDerivative, natDegree_derivative, ih]
    omega

/-- The leading coefficient retains each exact falling degree. -/
def legendreDerivativeLead (n : ℕ) : ℕ → ℝ
  | 0 => legendreLead n
  | r + 1 => legendreDerivativeLead n r * ((n - r : ℕ) : ℝ)

theorem legendreDerivative_leadingCoeff (n r : ℕ) :
    (legendreDerivative n r).leadingCoeff = legendreDerivativeLead n r := by
  induction r with
  | zero => exact legendrePoly_leadingCoeff n
  | succ r ih =>
    rw [legendreDerivative, leadingCoeff_derivative, ih, legendreDerivative_natDegree,
      legendreDerivativeLead]

theorem legendreDerivativeLead_pos {n r : ℕ} (hr : r ≤ n) : 0 < legendreDerivativeLead n r := by
  induction r with
  | zero => exact legendreLead_pos n
  | succ r ih =>
    rw [legendreDerivativeLead]
    exact mul_pos (ih (by omega)) (by exact_mod_cast (show 0 < n - r by omega))

theorem legendreDerivative_ne_zero {n r : ℕ} (hr : r ≤ n) : legendreDerivative n r ≠ 0 := by
  intro hz
  have hh := congrArg Polynomial.leadingCoeff hz
  rw [legendreDerivative_leadingCoeff, leadingCoeff_zero] at hh
  exact (legendreDerivativeLead_pos hr).ne' hh

/-- The shifted derivative modes have precisely their index as degree. -/
theorem shiftedLegendreDerivative_natDegree (r n : ℕ) :
    (legendreDerivative (n + r) r).natDegree = n := by
  rw [legendreDerivative_natDegree]
  omega

/-- Derivatives retain the parity forced by their remaining degree. -/
theorem legendreDerivative_neg (n r : ℕ) (x : ℝ) :
    (legendreDerivative n r).eval (-x) = (-1 : ℝ) ^ (n + r) * (legendreDerivative n r).eval x := by
  induction r generalizing x with
  | zero => simp only [legendreDerivative, legendrePoly_eval, Nat.add_zero, legP_neg]
  | succ r ih =>
    have he : (fun t : ℝ => (legendreDerivative n r).eval (-t)) =
        fun t => (-1 : ℝ) ^ (n + r) * (legendreDerivative n r).eval t := funext ih
    have hl := (hasDerivAt_legendreDerivative n r (-x)).comp x (hasDerivAt_id x).neg
    have hr := (hasDerivAt_legendreDerivative n r x).const_mul ((-1 : ℝ) ^ (n + r))
    change HasDerivAt (fun t => (legendreDerivative n r).eval (-t)) _ x at hl
    rw [he] at hl
    have hh := hl.unique hr
    rw [show n + (r + 1) = (n + r) + 1 by omega, pow_succ]
    nlinarith only [hh]

/-- The lowest shifted mode is a positive constant. -/
theorem legendreDerivative_diagonal_eval (r : ℕ) (x : ℝ) :
    (legendreDerivative r r).eval x = legendreDerivativeLead r r := by
  have hd : (legendreDerivative r r).natDegree = 0 := by rw [legendreDerivative_natDegree, Nat.sub_self]
  have hp := eq_C_of_natDegree_eq_zero hd
  have hc := coeff_natDegree (p := legendreDerivative r r)
  rw [hd, legendreDerivative_leadingCoeff] at hc
  rw [hp, eval_C, hc]

/-- The first nonconstant shifted mode is its leading monomial. -/
theorem legendreDerivative_next_eval (r : ℕ) (x : ℝ) :
    (legendreDerivative (r + 1) r).eval x = legendreDerivativeLead (r + 1) r * x := by
  have hd : (legendreDerivative (r + 1) r).natDegree = 1 := by
    rw [legendreDerivative_natDegree]
    omega
  have hz : (legendreDerivative (r + 1) r).eval 0 = 0 := by
    have hh := legendreDerivative_neg (r + 1) r 0
    rw [show r + 1 + r = 2 * r + 1 by omega, pow_add, pow_mul] at hh
    norm_num only [neg_zero, neg_sq, one_pow, pow_one, one_mul] at hh
    linarith only [hh]
  have hc0 : (legendreDerivative (r + 1) r).coeff 0 = 0 :=
    (coeff_zero_eq_eval_zero _).trans hz
  have hc1 := coeff_natDegree (p := legendreDerivative (r + 1) r)
  rw [hd, legendreDerivative_leadingCoeff] at hc1
  rw [eval_eq_sum_range, hd]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one,
    pow_one, hc0, hc1]

private theorem legendreDerivative_zero_succ (r : ℕ) : legendreDerivative 0 (r + 1) = 0 := by
  induction r with
  | zero => simp [legendreDerivative, legendrePoly]
  | succ r ih =>
    change (legendreDerivative 0 (r + 1)).derivative = 0
    rw [ih, derivative_zero]

private theorem legendreDerivative_one_add_two (r : ℕ) : legendreDerivative 1 (r + 2) = 0 := by
  induction r with
  | zero => simp [legendreDerivative, legendrePoly]
  | succ r ih =>
    change (legendreDerivative 1 (r + 2)).derivative = 0
    rw [ih, derivative_zero]

/-- Every derivative is nonnegative on the positive exterior of the orthogonality interval. -/
theorem legendreDerivative_eval_nonneg {x : ℝ} (hx : 1 ≤ x) (n r : ℕ) :
    0 ≤ (legendreDerivative n r).eval x := by
  induction r generalizing n with
  | zero =>
    simpa only [legendreDerivative, legendrePoly_eval] using (legP_nonneg_le_succ hx n).1
  | succ r ih =>
    induction n using Nat.strong_induction_on with
    | h n ihn =>
      rcases n with _ | _ | n
      · rw [legendreDerivative_zero_succ]
        simp
      · rcases r with _ | r
        · norm_num [legendreDerivative, legendrePoly]
        · rw [legendreDerivative_one_add_two]
          simp
      · rw [legendreDerivative_difference n r x]
        exact add_nonneg (mul_nonneg (by positivity) (ih (n + 1))) (ihn n (by omega))

#print axioms legendreDerivative_natDegree
#print axioms legendreDerivative_leadingCoeff
#print axioms legendreDerivative_neg
#print axioms legendreDerivative_eval_nonneg

end GaloisForLFunctions.ThetaCuspSections
