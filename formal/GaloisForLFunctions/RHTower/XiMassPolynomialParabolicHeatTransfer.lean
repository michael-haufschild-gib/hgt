import GaloisForLFunctions.RHTower.XiMassParabolicHeatTransfer
import GaloisForLFunctions.RHTower.XiPoissonMomentSummable

/-!
# Polynomial-filtered parabolic mass-to-heat transfer

The unfiltered relativistic mass trace converges to the Xi Gaussian heat trace under rest-energy
renormalization.  Polynomial spectral filters do not disturb that limit: they are independent of
the mass aperture, and the Poisson weight remains summable after multiplication by every spectral
power.  This gives the complete multiplicity-exact polynomial version of the parabolic transfer.

No RH hypothesis, finite divisor truncation, or numerical estimate occurs.
-/

open Complex Filter
open scoped BigOperators

namespace RHTower

noncomputable section

/-- One polynomial-filtered, rest-energy-renormalized mass multiplier. -/
def xiMassPolynomialParabolicTerm
    (P : Polynomial ℝ) (a t : ℝ) (q : XiZeroCopy) : ℂ :=
  evalRealPolynomial P (xiSpectralPoint q ^ (2 : ℕ)) ^ (2 : ℕ) *
    xiMassParabolicTerm a t q

/-- Complete polynomial-filtered parabolic mass trace with analytic multiplicities. -/
def xiMassPolynomialParabolicTrace
    (P : Polynomial ℝ) (a t : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, xiMassPolynomialParabolicTerm P a t q

/-- Exact rest-energy form of the polynomial-filtered mass multiplier. -/
theorem xiMassPolynomialParabolicTerm_eq_restEnergyRenormalized
    (P : Polynomial ℝ) (a t : ℝ) (q : XiZeroCopy) :
    xiMassPolynomialParabolicTerm P a t q =
      evalRealPolynomial P (xiSpectralPoint q ^ (2 : ℕ)) ^ (2 : ℕ) *
        Complex.exp (((2 * a ^ (2 : ℕ) * t : ℝ) : ℂ)) *
          xiMassAnalyticTest a (((2 * a * t : ℝ) : ℂ))
            (xiSpectralPoint q) := by
  rw [xiMassPolynomialParabolicTerm,
    xiMassParabolicTerm_eq_restEnergyRenormalized]
  ring

/-- Pointwise polynomial-filtered parabolic convergence on each divisor copy. -/
theorem tendsto_xiMassPolynomialParabolicTerm_atTop
    (P : Polynomial ℝ) (t : ℝ) (q : XiZeroCopy) :
    Tendsto (fun a : ℝ => xiMassPolynomialParabolicTerm P a t q) atTop
      (nhds (xiPolynomialGaussianHeatTerm P t q)) := by
  have hc : Tendsto
      (fun _ : ℝ => evalRealPolynomial P (xiSpectralPoint q ^ (2 : ℕ)) ^ (2 : ℕ))
      atTop
      (nhds (evalRealPolynomial P (xiSpectralPoint q ^ (2 : ℕ)) ^ (2 : ℕ))) :=
    tendsto_const_nhds
  have h := hc.mul
    (tendsto_xiMassParabolicTerm_atTop t q)
  simpa only [xiMassPolynomialParabolicTerm,
    xiPolynomialGaussianHeatTerm] using h

private theorem evalRealPolynomial_eq_sum_range
    (P : Polynomial ℝ) (z : ℂ) :
    evalRealPolynomial P z =
      ∑ k ∈ Finset.range (P.natDegree + 1),
        (P.coeff k : ℂ) * z ^ k := by
  rw [evalRealPolynomial, Polynomial.eval_eq_sum_range]
  simp only [Polynomial.natDegree_map_eq_of_injective
      (f := algebraMap ℝ ℂ) Complex.ofReal_injective,
    Polynomial.coeff_map, coe_algebraMap]

/-- Every polynomial-square spectral weight remains summable against a positive Poisson weight. -/
theorem summable_norm_evalRealPolynomial_sq_mul_xiPoissonWeight
    (P : Polynomial ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun q : XiZeroCopy =>
      ‖evalRealPolynomial P (xiSpectralPoint q ^ (2 : ℕ))‖ ^ (2 : ℕ) *
        xiPoissonWeight σ q) := by
  let Q : Polynomial ℝ := P * P
  let b : XiZeroCopy → ℝ := fun q =>
    ∑ k ∈ Finset.range (Q.natDegree + 1),
      ‖Q.coeff k‖ *
        (‖xiPoissonPoint q‖ ^ (2 * k) * xiPoissonWeight σ q)
  have hb : Summable b := by
    dsimp only [b]
    apply summable_sum
    intro k hk
    exact (summable_pow_mul_xiPoissonWeight hσ (2 * k)).mul_left
      ‖Q.coeff k‖
  refine Summable.of_nonneg_of_le
    (fun q => mul_nonneg (sq_nonneg _) (xiPoissonWeight_pos σ q).le)
    (fun q => ?_) hb
  have hQ : evalRealPolynomial Q (xiSpectralPoint q ^ (2 : ℕ)) =
      evalRealPolynomial P (xiSpectralPoint q ^ (2 : ℕ)) ^ (2 : ℕ) := by
    simp only [Q, evalRealPolynomial_mul, pow_two]
  calc
    ‖evalRealPolynomial P (xiSpectralPoint q ^ (2 : ℕ))‖ ^ (2 : ℕ) *
          xiPoissonWeight σ q =
        ‖evalRealPolynomial Q (xiSpectralPoint q ^ (2 : ℕ))‖ *
          xiPoissonWeight σ q := by
            rw [hQ, norm_pow]
    _ ≤ (∑ k ∈ Finset.range (Q.natDegree + 1),
          ‖(Q.coeff k : ℂ) * (xiSpectralPoint q ^ (2 : ℕ)) ^ k‖) *
            xiPoissonWeight σ q := by
      apply mul_le_mul_of_nonneg_right _ (xiPoissonWeight_pos σ q).le
      rw [evalRealPolynomial_eq_sum_range]
      exact norm_sum_le _ _
    _ = b q := by
      dsimp only [b]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_mul, norm_pow, norm_pow, ← norm_xiPoissonPoint q]
      simp only [Complex.norm_real]
      ring

/-- Uniform summable majorant for the polynomial-filtered parabolic family. -/
theorem norm_xiMassPolynomialParabolicTerm_le_poissonMajorant
    (P : Polynomial ℝ) {a t : ℝ} (ha : 1 ≤ a) (ht : 0 < t)
    (q : XiZeroCopy) :
    ‖xiMassPolynomialParabolicTerm P a t q‖ ≤
      ‖evalRealPolynomial P (xiSpectralPoint q ^ (2 : ℕ))‖ ^ (2 : ℕ) *
        xiPoissonWeight (t / 2) q := by
  rw [xiMassPolynomialParabolicTerm, norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left
    (norm_xiMassParabolicTerm_le_poissonWeight ha ht q)
    (sq_nonneg _)

/-- **Full polynomial-filtered parabolic transfer.**  For every real polynomial and positive heat
time, the complete rest-energy-renormalized mass trace converges to the exact polynomial-square
Gaussian Xi trace, unconditionally and with analytic multiplicities. -/
theorem tendsto_xiMassPolynomialParabolicTrace_atTop
    (P : Polynomial ℝ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun a : ℝ => xiMassPolynomialParabolicTrace P a t) atTop
      (nhds (xiPolynomialGaussianHeatTrace P t)) := by
  change Tendsto
    (fun a : ℝ => ∑' q : XiZeroCopy, xiMassPolynomialParabolicTerm P a t q)
    atTop (nhds (∑' q : XiZeroCopy, xiPolynomialGaussianHeatTerm P t q))
  apply tendsto_tsum_of_dominated_convergence
    (summable_norm_evalRealPolynomial_sq_mul_xiPoissonWeight P
      (by linarith : 0 < t / 2))
  · exact fun q => tendsto_xiMassPolynomialParabolicTerm_atTop P t q
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
    exact fun q => norm_xiMassPolynomialParabolicTerm_le_poissonMajorant P ha ht q

end

end RHTower
