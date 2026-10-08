import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Local polynomial ambiguity and its exact variance rigidity

Two endpoint evaluations leave exactly the ideal X*(X-C r) invisible. The
geometric valuation weights detect every nonconstant polynomial. These are
model classifications; no full-positive arithmetic source is asserted here.
The connection to literal finite-period coefficient averages is separate.
-/

open Polynomial Finset
noncomputable section
namespace RHTower.WeilSingularArithmetic

/-- The exact ideal of finite local factors invisible at two distinct endpoints. -/
theorem localPolynomial_two_endpoints_iff {r : ℝ} (hr : r ≠ 0) (P : Polynomial ℝ) :
    (P.eval 0 = 1 ∧ P.eval r = 1) ↔
      ∃ Q : Polynomial ℝ, P = 1 + X * (X - C r) * Q := by
  constructor
  · intro h
    have hx : X ∣ P - 1 := by
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
      simp [h.1]
    obtain ⟨Q, hQ⟩ := hx
    have he : 0 = r * Q.eval r := by
      simpa [h.2] using congrArg (fun A : Polynomial ℝ => A.eval r) hQ
    have hroot : Q.eval r = 0 := (mul_eq_zero.mp he.symm).resolve_left hr
    obtain ⟨R, hR⟩ := (Polynomial.dvd_iff_isRoot.mpr hroot : X - C r ∣ Q)
    refine ⟨R, ?_⟩
    calc
      P = 1 + (P - 1) := by ring
      _ = 1 + X * (X - C r) * R := by rw [hQ, hR]; ring
  · rintro ⟨Q, rfl⟩
    simp

def localPolynomialPrefix (P : Polynomial ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ range (k + 1), P.coeff j

def localPolynomialValuationVariance (r : ℝ) (P : Polynomial ℝ) : ℝ :=
  (1 - r) * ∑ k ∈ range P.natDegree, r ^ k * (localPolynomialPrefix P k - P.eval r) ^ 2 +
    r ^ P.natDegree * (localPolynomialPrefix P P.natDegree - P.eval r) ^ 2

theorem localPolynomialValuationVariance_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (P : Polynomial ℝ) : 0 ≤ localPolynomialValuationVariance r P := by
  unfold localPolynomialValuationVariance
  exact add_nonneg
    (mul_nonneg (sub_nonneg.mpr hr1)
      (Finset.sum_nonneg fun k _ => mul_nonneg (pow_nonneg hr0 k) (sq_nonneg _)))
    (mul_nonneg (pow_nonneg hr0 P.natDegree) (sq_nonneg _))

theorem localPolynomialValuationVariance_eq_zero_iff {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (P : Polynomial ℝ) :
    localPolynomialValuationVariance r P = 0 ↔ P = C (P.eval r) := by
  constructor
  · intro hV
    let H := ∑ k ∈ range P.natDegree, r ^ k * (localPolynomialPrefix P k - P.eval r) ^ 2
    have hH0 : 0 ≤ H := Finset.sum_nonneg fun k _ => mul_nonneg (pow_nonneg hr0.le _) (sq_nonneg _)
    have hT0 : 0 ≤ r ^ P.natDegree * (localPolynomialPrefix P P.natDegree - P.eval r) ^ 2 :=
      mul_nonneg (pow_nonneg hr0.le _) (sq_nonneg _)
    change (1 - r) * H + r ^ P.natDegree *
      (localPolynomialPrefix P P.natDegree - P.eval r) ^ 2 = 0 at hV
    have hmul0 := mul_nonneg (sub_nonneg.mpr hr1.le) hH0
    have hmul : (1 - r) * H = 0 := by linarith only [hV, hT0, hmul0]
    have hH : H = 0 := (mul_eq_zero.mp hmul).resolve_left (ne_of_gt (sub_pos.mpr hr1))
    have hlast : r ^ P.natDegree * (localPolynomialPrefix P P.natDegree - P.eval r) ^ 2 = 0 := by
      linarith only [hV, hmul]
    have hT : (localPolynomialPrefix P P.natDegree - P.eval r) ^ 2 = 0 :=
      (mul_eq_zero.mp hlast).resolve_left (ne_of_gt (pow_pos hr0 P.natDegree))
    have hterms : ∀ k ∈ range P.natDegree,
        r ^ k * (localPolynomialPrefix P k - P.eval r) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ => mul_nonneg (pow_nonneg hr0.le k) (sq_nonneg _))).mp hH
    have hprefix (k : ℕ) (hk : k ≤ P.natDegree) : localPolynomialPrefix P k = P.eval r := by
      by_cases he : k = P.natDegree
      · subst k
        nlinarith
      · have ht := (mul_eq_zero.mp (hterms k (mem_range.mpr (lt_of_le_of_ne hk he)))).resolve_left
          (ne_of_gt (pow_pos hr0 k))
        nlinarith
    apply Polynomial.ext
    intro j
    cases j with
    | zero => simpa [localPolynomialPrefix] using hprefix 0 (Nat.zero_le _)
    | succ j =>
      by_cases hj : j + 1 ≤ P.natDegree
      · have h₀ := hprefix j ((Nat.le_succ j).trans hj)
        have h₁ := hprefix (j + 1) hj
        have hrec : localPolynomialPrefix P (j + 1) =
            localPolynomialPrefix P j + P.coeff (j + 1) := by
          simp only [localPolynomialPrefix, Finset.sum_range_succ]
        simp only [Polynomial.coeff_C, Nat.succ_ne_zero, if_false]
        change P.coeff (j + 1) = 0
        linarith
      · have hz := Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hj)
        simpa using hz
  · intro hP
    rw [hP]
    simp [localPolynomialValuationVariance, localPolynomialPrefix]

/-- With the unit coefficient fixed, zero local variance singles out the unit polynomial. -/
theorem localPolynomialValuationVariance_normalized_eq_zero_iff {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (P : Polynomial ℝ) (h0 : P.eval 0 = 1) :
    localPolynomialValuationVariance r P = 0 ↔ P = 1 := by
  constructor
  · intro hV
    have hP := (localPolynomialValuationVariance_eq_zero_iff hr0 hr1 P).mp hV
    have he := congrArg (fun A : Polynomial ℝ => A.eval 0) hP
    have hr : P.eval r = 1 := by simpa [h0] using he.symm
    simpa [hr] using hP
  · intro hP
    subst P
    simp [localPolynomialValuationVariance, localPolynomialPrefix]

/-- Endpoint-invisible nonconstant local factors still have positive valuation variance. -/
theorem localPolynomialValuationVariance_pos {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (P : Polynomial ℝ) (h0 : P.eval 0 = 1) (hP : P ≠ 1) :
    0 < localPolynomialValuationVariance r P := by
  by_contra h
  have hV : localPolynomialValuationVariance r P = 0 :=
    le_antisymm (le_of_not_gt h) (localPolynomialValuationVariance_nonneg hr0.le hr1.le P)
  exact hP ((localPolynomialValuationVariance_normalized_eq_zero_iff hr0 hr1 P h0).mp hV)

end RHTower.WeilSingularArithmetic
