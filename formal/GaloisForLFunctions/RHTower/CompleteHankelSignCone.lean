import GaloisForLFunctions.RHTower.ExponentialMomentPolynomialSignCone
import GaloisForLFunctions.HTGeometry.MomentFunctionalPositivity

/-!
# Complete Hankel sign cone

This file upgrades polynomial-square positivity to its intrinsic matrix formulation.  Every
finite Hankel section is tested, with no fixed degree cutoff.  For a bounded continuous density
over a finite open-positive measure with an entire bilateral exponential-moment window, that
complete Hankel cone is exactly the pointwise nonnegative cone.
-/

noncomputable section

open MeasureTheory Polynomial Set
open scoped BigOperators ENNReal

namespace RHTower

/-- Nonnegativity of every finite Hankel quadratic form associated with `s`. -/
def CompleteHankelCone (s : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (v : Fin n → ℝ),
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, v i * v j * s ((i : ℕ) + (j : ℕ))

/-- The finite-vector polynomial used to identify Hankel forms with polynomial squares. -/
def finCoefficientPolynomial {n : ℕ} (v : Fin n → ℝ) : Polynomial ℝ :=
  ∑ i : Fin n, v i • Polynomial.X ^ (i : ℕ)

/-- Every real polynomial is its finite coefficient polynomial in degrees through its natural
degree. -/
theorem finCoefficientPolynomial_coeff_natDegree_eq (p : Polynomial ℝ) :
    finCoefficientPolynomial
      (n := p.natDegree + 1) (fun i ↦ p.coeff (i : ℕ)) = p := by
  rw [finCoefficientPolynomial]
  calc
    (∑ i : Fin (p.natDegree + 1), p.coeff (i : ℕ) • X ^ (i : ℕ)) =
        ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • X ^ i := by
          exact Fin.sum_univ_eq_sum_range
            (fun i : ℕ ↦ p.coeff i • (X : Polynomial ℝ) ^ i) (p.natDegree + 1)
    _ = p := by
      simpa only [smul_eq_C_mul] using p.as_sum_range_C_mul_X_pow.symm

/-- Purely algebraic equivalence between positivity on polynomial squares and positivity of every
finite Hankel section. -/
theorem completeHankelCone_iff_momentFunctional_square_nonnegative (s : ℕ → ℝ) :
    CompleteHankelCone s ↔
      ∀ p : Polynomial ℝ, 0 ≤ HTGeometry.momentFunctional s (p ^ 2) := by
  constructor
  · intro h p
    let v : Fin (p.natDegree + 1) → ℝ := fun i ↦ p.coeff (i : ℕ)
    have hv := h (p.natDegree + 1) v
    rw [← HTGeometry.momentFunctional_sq_eq_hankelForm s v] at hv
    change 0 ≤ HTGeometry.momentFunctional s ((finCoefficientPolynomial v) ^ 2) at hv
    rw [show finCoefficientPolynomial v = p from
      finCoefficientPolynomial_coeff_natDegree_eq p] at hv
    exact hv
  · intro h n v
    rw [← HTGeometry.momentFunctional_sq_eq_hankelForm s v]
    exact h (finCoefficientPolynomial v)

/-- Moments of the signed density `J` with respect to `mu`. -/
def weightedMoment (mu : Measure ℝ) (J : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x, x ^ n * J x ∂mu

/-- Monomials remain integrable after multiplication by an `L∞` density. -/
theorem integrable_monomial_mul_of_entireExponentialMoments
    {mu : Measure ℝ} [IsFiniteMeasure mu]
    (hmu : HasEntireExponentialMoments mu)
    (J : ℝ → ℝ) (hJ : MemLp J ∞ mu) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n * J x) mu := by
  have hn : Integrable (fun x : ℝ ↦ x ^ n) mu :=
    memLp_one_iff_integrable.mp
      ((monomial_memLp_two_of_entireExponentialMoments hmu n).mono_exponent (by norm_num))
  exact hn.mul_bdd hJ.aestronglyMeasurable (ae_le_lpNorm_exponent_top hJ)

/-- The moment functional of a bounded signed density is exactly integration against that
density. -/
theorem momentFunctional_weightedMoment_eq_integral
    {mu : Measure ℝ} [IsFiniteMeasure mu]
    (hmu : HasEntireExponentialMoments mu)
    (J : ℝ → ℝ) (hJ : MemLp J ∞ mu) (p : Polynomial ℝ) :
    HTGeometry.momentFunctional (weightedMoment mu J) p =
      ∫ x, p.eval x * J x ∂mu := by
  rw [HTGeometry.momentFunctional_eq_support_sum]
  have heval : (fun x : ℝ ↦ p.eval x * J x) =
      fun x ↦ ∑ k ∈ p.support, p.coeff k * (x ^ k * J x) := by
    funext x
    rw [eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [heval, integral_finsetSum p.support]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [integral_const_mul]
    rfl
  · intro k hk
    exact (integrable_monomial_mul_of_entireExponentialMoments hmu J hJ k).const_mul _

/-- Square specialization of the weighted moment-functional identity. -/
theorem momentFunctional_weightedMoment_sq_eq_integral
    {mu : Measure ℝ} [IsFiniteMeasure mu]
    (hmu : HasEntireExponentialMoments mu)
    (J : ℝ → ℝ) (hJ : MemLp J ∞ mu) (p : Polynomial ℝ) :
    HTGeometry.momentFunctional (weightedMoment mu J) (p ^ 2) =
      ∫ x, (p.eval x) ^ 2 * J x ∂mu := by
  rw [momentFunctional_weightedMoment_eq_integral hmu J hJ]
  apply integral_congr_ae
  filter_upwards with x
  rw [Polynomial.eval_pow]

/-- **Almost-everywhere complete Hankel sign-cone law.** The entire tower of finite Hankel
sections of a bounded signed density is positive semidefinite exactly when that density is
nonnegative almost everywhere. -/
theorem completeHankelCone_weightedMoment_iff_ae
    {mu : Measure ℝ} [IsFiniteMeasure mu]
    (hmu : HasEntireExponentialMoments mu)
    (J : ℝ → ℝ) (hJ : MemLp J ∞ mu) :
    CompleteHankelCone (weightedMoment mu J) ↔ 0 ≤ᵐ[mu] J := by
  rw [completeHankelCone_iff_momentFunctional_square_nonnegative]
  constructor
  · intro h
    apply (polynomialSquareIntegral_nonnegative_iff_ae hmu J hJ).mp
    intro p
    have hp := h p
    rw [momentFunctional_weightedMoment_sq_eq_integral hmu J hJ] at hp
    exact hp
  · intro h p
    rw [momentFunctional_weightedMoment_sq_eq_integral hmu J hJ]
    exact (polynomialSquareIntegral_nonnegative_iff_ae hmu J hJ).mpr h p

/-- **Pointwise complete Hankel sign-cone law.** For a finite open-positive measure with an
entire bilateral exponential-moment window, the complete Hankel cone of a continuous `L∞`
density equals its pointwise sign cone. -/
theorem completeHankelCone_weightedMoment_iff
    {mu : Measure ℝ} [IsFiniteMeasure mu] [mu.IsOpenPosMeasure]
    (hmu : HasEntireExponentialMoments mu)
    (J : ℝ → ℝ) (hJcont : Continuous J) (hJ : MemLp J ∞ mu) :
    CompleteHankelCone (weightedMoment mu J) ↔ ∀ x, 0 ≤ J x := by
  rw [completeHankelCone_weightedMoment_iff_ae hmu J hJ]
  constructor
  · exact continuous_nonnegative_of_ae hJcont
  · exact fun h ↦ Filter.Eventually.of_forall h

end RHTower
