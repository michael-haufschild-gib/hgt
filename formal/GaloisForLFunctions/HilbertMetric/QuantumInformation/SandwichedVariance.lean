import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Geometric-mean variance and skew information

The order-two variance deficit in sandwiched Rényi robustness is a sum of
squared differences of square-root populations. For arbitrary transition
amplitudes this compares the symmetrized Born quadratic form with the
geometric-mean quadratic form. For centered Hermitian observables these are
the Born variance and the order-two spectral variance, respectively.
-/

open scoped BigOperators NNReal
namespace GaloisForLFunctions.HilbertMetric.QuantumInformation
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- Symmetrized Born quadratic form in a diagonal positive state. -/
def bornQuadratic (p : ι → ℝ≥0) (A : ι → ι → ℂ) : ℝ :=
  ∑ i, ∑ j, ((p i : ℝ) + p j) / 2 * Complex.normSq (A i j)

/-- Geometric-mean quadratic form governing order-two sandwiched robustness. -/
def sandwichedQuadratic (p : ι → ℝ≥0) (A : ι → ι → ℂ) : ℝ :=
  ∑ i, ∑ j, Real.sqrt (p i) * Real.sqrt (p j) * Complex.normSq (A i j)

/-- Wigner--Yanase skew information, extended to arbitrary transition amplitudes. -/
def skewInformation (p : ι → ℝ≥0) (A : ι → ι → ℂ) : ℝ :=
  ∑ i, ∑ j, (Real.sqrt (p i) - Real.sqrt (p j)) ^ (2 : ℕ) / 2 * Complex.normSq (A i j)

theorem sandwichedQuadratic_nonneg (p : ι → ℝ≥0) (A : ι → ι → ℂ) :
    0 ≤ sandwichedQuadratic p A := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (Complex.normSq_nonneg _)

theorem skewInformation_nonneg (p : ι → ℝ≥0) (A : ι → ι → ℂ) :
    0 ≤ skewInformation p A := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) (Complex.normSq_nonneg _)

/-- Exact variance deflation; no normalization or invertibility is needed. -/
theorem born_sub_sandwiched_eq_skewInformation (p : ι → ℝ≥0) (A : ι → ι → ℂ) :
    bornQuadratic p A - sandwichedQuadratic p A = skewInformation p A := by
  unfold bornQuadratic sandwichedQuadratic skewInformation
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hi : Real.sqrt (p i) ^ (2 : ℕ) = (p i : ℝ) := Real.sq_sqrt (p i).property
  have hj : Real.sqrt (p j) ^ (2 : ℕ) = (p j : ℝ) := Real.sq_sqrt (p j).property
  calc
    _ = ((Real.sqrt (p i) ^ (2 : ℕ) + Real.sqrt (p j) ^ (2 : ℕ)) / 2 -
        Real.sqrt (p i) * Real.sqrt (p j)) * Complex.normSq (A i j) := by
      rw [hi, hj]
      ring
    _ = _ := by ring

theorem sandwichedQuadratic_le_born (p : ι → ℝ≥0) (A : ι → ι → ℂ) :
    sandwichedQuadratic p A ≤ bornQuadratic p A := by
  have h := skewInformation_nonneg p A
  rw [← born_sub_sandwiched_eq_skewInformation] at h
  exact sub_nonneg.mp h

/-- No deflation occurs exactly when amplitudes join only equal populations. -/
theorem skewInformation_eq_zero_iff (p : ι → ℝ≥0) (A : ι → ι → ℂ) :
    skewInformation p A = 0 ↔ ∀ i j, p i = p j ∨ A i j = 0 := by
  have hn (i j : ι) : 0 ≤ (Real.sqrt (p i) - Real.sqrt (p j)) ^ (2 : ℕ) / 2 *
      Complex.normSq (A i j) :=
    mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) (Complex.normSq_nonneg _)
  unfold skewInformation
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => hn i j)]
  simp only [Finset.mem_univ, forall_const]
  have hz (i : ι) := Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) => hn i j)
  simp_rw [hz]
  simp only [Finset.mem_univ, forall_const, mul_eq_zero, div_eq_zero_iff,
    sq_eq_zero_iff, sub_eq_zero, Complex.normSq_eq_zero, OfNat.ofNat_ne_zero,
    or_false]
  constructor
  · intro h i j
    rcases h i j with hij | hij
    · left
      exact NNReal.coe_injective ((Real.sqrt_inj (p i).property (p j).property).mp hij)
    · exact Or.inr hij
  · intro h i j
    rcases h i j with hij | hij
    · exact Or.inl (congrArg (fun x : ℝ≥0 => Real.sqrt (x : ℝ)) hij)
    · exact Or.inr hij

/-- Strict variance deflation detects a transition between distinct populations. -/
theorem sandwichedQuadratic_lt_born_iff (p : ι → ℝ≥0) (A : ι → ι → ℂ) :
    sandwichedQuadratic p A < bornQuadratic p A ↔
      ∃ i j, p i ≠ p j ∧ A i j ≠ 0 := by
  have h := skewInformation_nonneg p A
  rw [← sub_pos, born_sub_sandwiched_eq_skewInformation,
    lt_iff_le_and_ne]
  simp only [h, true_and]
  rw [ne_comm]
  simp only [ne_eq, skewInformation_eq_zero_iff, not_forall, not_or]

/-- The equality condition is exactly commutation with the diagonal state. -/
theorem skewInformation_eq_zero_iff_commute [DecidableEq ι]
    (p : ι → ℝ≥0) (A : Matrix ι ι ℂ) :
    skewInformation p A = 0 ↔
      Matrix.diagonal (fun i => ((p i : ℝ) : ℂ)) * A =
        A * Matrix.diagonal (fun i => ((p i : ℝ) : ℂ)) := by
  rw [skewInformation_eq_zero_iff, ← Matrix.ext_iff]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  constructor
  · intro h i j
    rcases h i j with hij | hij
    · rw [hij, mul_comm]
    · rw [hij, mul_zero, zero_mul]
  · intro h i j
    have hz : (((p i : ℝ) : ℂ) - ((p j : ℝ) : ℂ)) * A i j = 0 := by
      rw [sub_mul, h i j, mul_comm (A i j), sub_self]
    rcases mul_eq_zero.mp hz with hij | hij
    · left
      exact NNReal.coe_injective (Complex.ofReal_injective (sub_eq_zero.mp hij))
    · exact Or.inr hij

end
end GaloisForLFunctions.HilbertMetric.QuantumInformation
