import GaloisForLFunctions.HTGeometry.MonicOrthoExtremalComparison
import GaloisForLFunctions.RHTower.SoninSemilocalJacobiResidueCorollaries
import GaloisForLFunctions.RHTower.SoninSemilocalJacobiOrthonormal
import GaloisForLFunctions.RHTower.CCM.CCMMetaplecticGammaMomentDeterminacy

/-!
# Semilocal Jacobi linear growth and the prolate domain gate

The finite-prime semilocal cyclic spectral measure is the archimedean Gamma measure multiplied by
the positive Euler density `∏_p |1 - p^{-1/2} e^{i log p · s}|^{-2}` and renormalized.  Because that
density is bounded above and below by explicit positive constants, the two measures are uniformly
equivalent, so the extremal description of the monic orthogonal norms transfers a two-sided bound to
the whole Jacobi ladder:

`K_P⁻¹ a_n(∅) ≤ a_n(P) ≤ K_P a_n(∅)`,  `K_P = ∏_p ((1 + p^{-1/2})/(1 - p^{-1/2}))²`,

with the archimedean coefficients `a_n(∅) = √((n + 1/2)(n + 1)) = √((2n+1)(2n+2))/2` supplied by the
corpus's exact Gamma--Jacobi recurrence.  Consequently the off-diagonal coefficients
`b_n^± (P)` of the two parity blocks of the formal prolate Jacobi matrix grow quadratically from both
sides, so `∑_n 1/b_n^±(P) < ∞`: the Carleman divergence criterion for essential self-adjointness is
unavailable, and the formal semilocal prolate expression does not by itself select a resolvent.

Everything here is unconditional.
-/

noncomputable section

open Complex Filter MeasureTheory Polynomial Real Set
open scoped BigOperators

namespace RHTower

/-! ## The archimedean moment form -/

/-- Finite sets are null for the archimedean Gamma measure. -/
theorem semilocalArchimedeanGammaMeasure_finset_eq_zero (F : Finset ℝ) :
    semilocalArchimedeanGammaMeasure (F : Set ℝ) = 0 := by
  have hvol : volume (F : Set ℝ) = 0 := (F.finite_toSet).measure_zero volume
  rw [semilocalArchimedeanGammaMeasure]
  exact (withDensity_absolutelyContinuous volume _) hvol

/-- The archimedean Gamma measure charges the complement of every finite set. -/
theorem semilocalArchimedeanGammaMeasure_compl_finset_pos (F : Finset ℝ) :
    0 < semilocalArchimedeanGammaMeasure {x : ℝ | x ∉ F} := by
  have hcompl : {x : ℝ | x ∉ F} = (F : Set ℝ)ᶜ := rfl
  have hone : semilocalArchimedeanGammaMeasure ((F : Set ℝ)ᶜ) = 1 := by
    rw [measure_compl (F.finite_toSet.measurableSet)
      (by rw [semilocalArchimedeanGammaMeasure_finset_eq_zero]; exact ENNReal.zero_ne_top),
      semilocalArchimedeanGammaMeasure_finset_eq_zero, measure_univ, tsub_zero]
  rw [hcompl, hone]
  exact zero_lt_one

/-- The archimedean Gamma moment form is positive definite. -/
theorem positiveMomentForm_ccmMetaplecticGammaMoment :
    HTGeometry.PositiveMomentForm ccmMetaplecticGammaMoment :=
  HTGeometry.positiveMomentForm_of_infiniteSupport ccmMetaplecticGammaMoment
    (fun _ => rfl) integrable_pow_semilocalArchimedeanGammaMeasure
    semilocalArchimedeanGammaMeasure_compl_finset_pos

theorem momentInner_ccmMetaplecticGammaMoment_self (q : ℝ[X]) :
    HTGeometry.momentInner ccmMetaplecticGammaMoment q q =
      ∫ s : ℝ, (Polynomial.eval s q) ^ 2 ∂semilocalArchimedeanGammaMeasure := by
  rw [HTGeometry.momentInner_self]
  exact HTGeometry.momentFunctional_pow_two_eq_integral_sq ccmMetaplecticGammaMoment
    (fun _ => rfl) integrable_pow_semilocalArchimedeanGammaMeasure q

/-! ## The archimedean Jacobi ladder -/

/-- Leading-coefficient step of the orthonormal Gamma--Jacobi family. -/
theorem semilocalArchimedeanJacobiPolynomial_leadingCoeff_succ (n : ℕ) :
    (semilocalArchimedeanJacobiPolynomial (n + 1)).leadingCoeff =
      (semilocalArchimedeanJacobiCoefficient n)⁻¹ *
        (semilocalArchimedeanJacobiPolynomial n).leadingCoeff := by
  cases n with
  | zero =>
      have h1 : semilocalArchimedeanJacobiPolynomial (0 + 1) =
          C (semilocalArchimedeanJacobiCoefficient 0)⁻¹ * X := rfl
      rw [h1, semilocalArchimedeanJacobiPolynomial_zero, leadingCoeff_mul, leadingCoeff_C,
        leadingCoeff_X, leadingCoeff_one, mul_one]
  | succ n =>
      have haN : semilocalArchimedeanJacobiCoefficient n ≠ 0 :=
        (semilocalArchimedeanJacobiCoefficient_pos n).ne'
      have hp1 : semilocalArchimedeanJacobiPolynomial (n + 1) ≠ 0 := by
        have := semilocalArchimedeanJacobiPolynomial_leadingCoeff_pos (n + 1)
        exact leadingCoeff_ne_zero.mp this.ne'
      have hdegree :
          degree (C (semilocalArchimedeanJacobiCoefficient n) *
              semilocalArchimedeanJacobiPolynomial n) <
            degree (X * semilocalArchimedeanJacobiPolynomial (n + 1)) := by
        apply degree_lt_degree
        rw [natDegree_C_mul haN, semilocalArchimedeanJacobiPolynomial_natDegree,
          natDegree_X_mul hp1, semilocalArchimedeanJacobiPolynomial_natDegree]
        omega
      rw [semilocalArchimedeanJacobiPolynomial, leadingCoeff_mul, leadingCoeff_C,
        leadingCoeff_sub_of_degree_lt hdegree, leadingCoeff_mul, leadingCoeff_X, one_mul]

theorem semilocalArchimedeanJacobiPolynomial_ne_zero (n : ℕ) :
    semilocalArchimedeanJacobiPolynomial n ≠ 0 :=
  leadingCoeff_ne_zero.mp (semilocalArchimedeanJacobiPolynomial_leadingCoeff_pos n).ne'

theorem momentInner_semilocalArchimedeanJacobiPolynomial (m n : ℕ) :
    HTGeometry.momentInner ccmMetaplecticGammaMoment
        (semilocalArchimedeanJacobiPolynomial m) (semilocalArchimedeanJacobiPolynomial n) =
      semilocalArchimedeanJacobiGram m n := by
  rw [HTGeometry.momentInner_def,
    HTGeometry.momentFunctional_mul_eq_integral ccmMetaplecticGammaMoment (fun _ => rfl)
      integrable_pow_semilocalArchimedeanGammaMeasure]
  rfl

/-- **The archimedean monic norms are the inverse squared leading coefficients.** -/
theorem monicOrthoNormSq_ccmMetaplecticGammaMoment (n : ℕ) :
    HTGeometry.monicOrthoNormSq ccmMetaplecticGammaMoment n =
      ((semilocalArchimedeanJacobiPolynomial n).leadingCoeff)⁻¹ ^ 2 := by
  rw [HTGeometry.monicOrthoNormSq_of_orthogonal_family positiveMomentForm_ccmMetaplecticGammaMoment
    semilocalArchimedeanJacobiPolynomial_natDegree semilocalArchimedeanJacobiPolynomial_ne_zero
    (fun m n hmn => by
      rw [momentInner_semilocalArchimedeanJacobiPolynomial,
        semilocalArchimedeanJacobiGram_eq_ite, if_neg hmn]) n,
    momentInner_semilocalArchimedeanJacobiPolynomial, semilocalArchimedeanJacobiGram_self,
    mul_one]

/-- **The archimedean lower Jacobi coefficient is `a_n² = (n + 1/2)(n + 1)`.** -/
theorem monicOrthoBeta_ccmMetaplecticGammaMoment (n : ℕ) :
    HTGeometry.monicOrthoBeta ccmMetaplecticGammaMoment (n + 1) =
      ((n : ℝ) + 1 / 2) * ((n : ℝ) + 1) := by
  have hlcn : (semilocalArchimedeanJacobiPolynomial n).leadingCoeff ≠ 0 :=
    (semilocalArchimedeanJacobiPolynomial_leadingCoeff_pos n).ne'
  have han : semilocalArchimedeanJacobiCoefficient n ≠ 0 :=
    (semilocalArchimedeanJacobiCoefficient_pos n).ne'
  have hstep := semilocalArchimedeanJacobiPolynomial_leadingCoeff_succ n
  have hbeta : HTGeometry.monicOrthoBeta ccmMetaplecticGammaMoment (n + 1) =
      HTGeometry.monicOrthoNormSq ccmMetaplecticGammaMoment (n + 1) /
        HTGeometry.monicOrthoNormSq ccmMetaplecticGammaMoment n := rfl
  rw [hbeta, monicOrthoNormSq_ccmMetaplecticGammaMoment,
    monicOrthoNormSq_ccmMetaplecticGammaMoment, hstep,
    ← semilocalArchimedeanJacobiCoefficient_sq n]
  field_simp


/-! ## Two-sided bounds for the finite-prime Euler density -/

/-- Uniform lower bound `∏ (1 + p^{-1/2})^{-2}` for the finite-prime Euler density. -/
def semilocalEulerDensityLower {n : ℕ} (p : Fin n → ℕ) : ℝ :=
  ∏ i, ((1 + semilocalPrimePoissonRatio (p i)) ^ 2)⁻¹

/-- Uniform upper bound `∏ (1 - p^{-1/2})^{-2}` for the finite-prime Euler density. -/
def semilocalEulerDensityUpper {n : ℕ} (p : Fin n → ℕ) : ℝ :=
  ∏ i, ((1 - semilocalPrimePoissonRatio (p i)) ^ 2)⁻¹

/-- The card's comparison constant `K_P = ∏ ((1 + p^{-1/2})/(1 - p^{-1/2}))²`. -/
def semilocalJacobiComparisonConstant {n : ℕ} (p : Fin n → ℕ) : ℝ :=
  ∏ i, ((1 + semilocalPrimePoissonRatio (p i)) /
    (1 - semilocalPrimePoissonRatio (p i))) ^ 2

theorem semilocalEulerDensityLower_pos {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime) :
    0 < semilocalEulerDensityLower p := by
  refine Finset.prod_pos fun i _ => inv_pos.mpr ?_
  have := semilocalPrimePoissonRatio_pos (hprime i)
  positivity

theorem semilocalEulerDensityUpper_pos {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime) :
    0 < semilocalEulerDensityUpper p := by
  refine Finset.prod_pos fun i _ => inv_pos.mpr ?_
  have h1 := semilocalPrimePoissonRatio_lt_one (hprime i)
  have : 0 < 1 - semilocalPrimePoissonRatio (p i) := by linarith
  positivity

theorem semilocalJacobiComparisonConstant_pos {n : ℕ} (p : Fin n → ℕ)
    (hprime : ∀ i, (p i).Prime) : 0 < semilocalJacobiComparisonConstant p := by
  refine Finset.prod_pos fun i _ => ?_
  have h0 := semilocalPrimePoissonRatio_pos (hprime i)
  have h1 := semilocalPrimePoissonRatio_lt_one (hprime i)
  have : 0 < 1 - semilocalPrimePoissonRatio (p i) := by linarith
  positivity

theorem semilocalEulerDensityUpper_eq {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime) :
    semilocalEulerDensityUpper p =
      semilocalJacobiComparisonConstant p * semilocalEulerDensityLower p := by
  rw [semilocalEulerDensityUpper, semilocalJacobiComparisonConstant, semilocalEulerDensityLower,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h0 := semilocalPrimePoissonRatio_pos (hprime i)
  have h1 := semilocalPrimePoissonRatio_lt_one (hprime i)
  have hne1 : (1 : ℝ) - semilocalPrimePoissonRatio (p i) ≠ 0 := by linarith
  have hne2 : (1 : ℝ) + semilocalPrimePoissonRatio (p i) ≠ 0 := by linarith
  rw [div_pow]
  field_simp

/-- Pointwise two-sided bound for one Euler factor. -/
theorem semilocalPrimeEulerFactor_bounds {p : ℕ} (hp : p.Prime) (s : ℝ) :
    ((1 + semilocalPrimePoissonRatio p) ^ 2)⁻¹ ≤
        (Complex.normSq (1 - (semilocalPrimePoissonRatio p : ℂ) * semilocalPrimePhase p s))⁻¹ ∧
      (Complex.normSq (1 - (semilocalPrimePoissonRatio p : ℂ) * semilocalPrimePhase p s))⁻¹ ≤
        ((1 - semilocalPrimePoissonRatio p) ^ 2)⁻¹ := by
  set r : ℝ := semilocalPrimePoissonRatio p with hr
  have hr0 : 0 < r := semilocalPrimePoissonRatio_pos hp
  have hr1 : r < 1 := semilocalPrimePoissonRatio_lt_one hp
  have hnormz : ‖(r : ℂ) * semilocalPrimePhase p s‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le,
      norm_semilocalPrimePhase, mul_one]
  have hupper : ‖(1 : ℂ) - (r : ℂ) * semilocalPrimePhase p s‖ ≤ 1 + r := by
    calc ‖(1 : ℂ) - (r : ℂ) * semilocalPrimePhase p s‖
        ≤ ‖(1 : ℂ)‖ + ‖(r : ℂ) * semilocalPrimePhase p s‖ := norm_sub_le _ _
      _ = 1 + r := by rw [norm_one, hnormz]
  have hlower : 1 - r ≤ ‖(1 : ℂ) - (r : ℂ) * semilocalPrimePhase p s‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((r : ℂ) * semilocalPrimePhase p s)
    rw [norm_one, hnormz] at this
    exact this
  have hnsq : Complex.normSq (1 - (r : ℂ) * semilocalPrimePhase p s)
      = ‖(1 : ℂ) - (r : ℂ) * semilocalPrimePhase p s‖ ^ 2 := Complex.normSq_eq_norm_sq _
  have hsq1 : (1 - r) ^ 2 ≤ Complex.normSq (1 - (r : ℂ) * semilocalPrimePhase p s) := by
    rw [hnsq]
    exact pow_le_pow_left₀ (by linarith) hlower 2
  have hsq2 : Complex.normSq (1 - (r : ℂ) * semilocalPrimePhase p s) ≤ (1 + r) ^ 2 := by
    rw [hnsq]
    exact pow_le_pow_left₀ (norm_nonneg _) hupper 2
  have hpos : (0 : ℝ) < (1 - r) ^ 2 := by nlinarith
  have hnsqpos : 0 < Complex.normSq (1 - (r : ℂ) * semilocalPrimePhase p s) :=
    lt_of_lt_of_le hpos hsq1
  refine ⟨?_, ?_⟩
  · gcongr
  · gcongr

/-- **Uniform equivalence of the semilocal and archimedean densities.** -/
theorem semilocalFinitePrimeEulerDensity_bounds {n : ℕ} (p : Fin n → ℕ)
    (hprime : ∀ i, (p i).Prime) (s : ℝ) :
    semilocalEulerDensityLower p ≤ semilocalFinitePrimeEulerDensity p s ∧
      semilocalFinitePrimeEulerDensity p s ≤ semilocalEulerDensityUpper p := by
  constructor
  · refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => (semilocalPrimeEulerFactor_bounds (hprime i) s).1)
    have := semilocalPrimePoissonRatio_pos (hprime i)
    positivity
  · refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => (semilocalPrimeEulerFactor_bounds (hprime i) s).2)
    exact inv_nonneg.mpr (Complex.normSq_nonneg _)


/-! ## The semilocal cyclic moment sequence -/

/-- The normalizing mass `Z_P = ∫ w_P dμ_∞`. -/
def semilocalFinitePrimeMass {n : ℕ} (p : Fin n → ℕ) : ℝ :=
  ∫ s : ℝ, semilocalFinitePrimeEulerDensity p s ∂semilocalArchimedeanGammaMeasure

/-- The moment sequence of the normalized semilocal cyclic spectral measure `ν_P`. -/
def semilocalFinitePrimeCyclicMoment {n : ℕ} (p : Fin n → ℕ) (k : ℕ) : ℝ :=
  (∫ s : ℝ, s ^ k * semilocalFinitePrimeEulerDensity p s ∂semilocalArchimedeanGammaMeasure) /
    semilocalFinitePrimeMass p

theorem integrable_pow_mul_semilocalFinitePrimeEulerDensity {n : ℕ} (p : Fin n → ℕ)
    (hprime : ∀ i, (p i).Prime) (k : ℕ) :
    Integrable (fun s : ℝ => s ^ k * semilocalFinitePrimeEulerDensity p s)
      semilocalArchimedeanGammaMeasure := by
  refine (integrable_eval_mul_semilocalFinitePrimeEulerDensity p hprime (X ^ k)).congr ?_
  filter_upwards with s
  simp

theorem integrable_sq_eval_mul_semilocalFinitePrimeEulerDensity {n : ℕ} (p : Fin n → ℕ)
    (hprime : ∀ i, (p i).Prime) (q : ℝ[X]) :
    Integrable (fun s : ℝ => (Polynomial.eval s q) ^ 2 * semilocalFinitePrimeEulerDensity p s)
      semilocalArchimedeanGammaMeasure := by
  refine (integrable_eval_mul_semilocalFinitePrimeEulerDensity p hprime (q ^ 2)).congr ?_
  filter_upwards with s
  simp

theorem integrable_sq_eval_semilocalArchimedeanGammaMeasure (q : ℝ[X]) :
    Integrable (fun s : ℝ => (Polynomial.eval s q) ^ 2) semilocalArchimedeanGammaMeasure := by
  refine (HTGeometry.integrable_eval integrable_pow_semilocalArchimedeanGammaMeasure (q ^ 2)).congr ?_
  filter_upwards with s
  simp

/-- The mass is bounded below by the uniform density floor, hence strictly positive. -/
theorem semilocalEulerDensityLower_le_mass {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime) :
    semilocalEulerDensityLower p ≤ semilocalFinitePrimeMass p := by
  have hint : Integrable (fun s : ℝ => semilocalFinitePrimeEulerDensity p s)
      semilocalArchimedeanGammaMeasure := by
    refine (integrable_pow_mul_semilocalFinitePrimeEulerDensity p hprime 0).congr ?_
    filter_upwards with s
    simp
  have hmono : ∫ _s : ℝ, semilocalEulerDensityLower p ∂semilocalArchimedeanGammaMeasure ≤
      semilocalFinitePrimeMass p :=
    integral_mono (integrable_const _) hint
      (fun s => (semilocalFinitePrimeEulerDensity_bounds p hprime s).1)
  simpa using hmono

theorem semilocalFinitePrimeMass_pos {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime) :
    0 < semilocalFinitePrimeMass p :=
  lt_of_lt_of_le (semilocalEulerDensityLower_pos p hprime)
    (semilocalEulerDensityLower_le_mass p hprime)

theorem momentFunctional_semilocalFinitePrimeCyclicMoment {n : ℕ} (p : Fin n → ℕ)
    (hprime : ∀ i, (p i).Prime) (q : ℝ[X]) :
    HTGeometry.momentFunctional (semilocalFinitePrimeCyclicMoment p) q =
      (∫ s : ℝ, Polynomial.eval s q * semilocalFinitePrimeEulerDensity p s
        ∂semilocalArchimedeanGammaMeasure) / semilocalFinitePrimeMass p := by
  have hsum : (∫ s : ℝ, Polynomial.eval s q * semilocalFinitePrimeEulerDensity p s
        ∂semilocalArchimedeanGammaMeasure)
      = ∑ k ∈ q.support, q.coeff k *
          ∫ s : ℝ, s ^ k * semilocalFinitePrimeEulerDensity p s
            ∂semilocalArchimedeanGammaMeasure := by
    have hrw : (fun s : ℝ => Polynomial.eval s q * semilocalFinitePrimeEulerDensity p s)
        = fun s : ℝ => ∑ k ∈ q.support,
            q.coeff k * (s ^ k * semilocalFinitePrimeEulerDensity p s) := by
      funext s
      rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hrw, integral_finsetSum _ (fun k _ =>
      (integrable_pow_mul_semilocalFinitePrimeEulerDensity p hprime k).const_mul _)]
    exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
  rw [HTGeometry.momentFunctional_eq_support_sum, hsum, Finset.sum_div]
  exact Finset.sum_congr rfl fun k _ => by
    rw [semilocalFinitePrimeCyclicMoment, mul_div_assoc]

theorem momentInner_semilocalFinitePrimeCyclicMoment_self {n : ℕ} (p : Fin n → ℕ)
    (hprime : ∀ i, (p i).Prime) (q : ℝ[X]) :
    HTGeometry.momentInner (semilocalFinitePrimeCyclicMoment p) q q =
      (∫ s : ℝ, (Polynomial.eval s q) ^ 2 * semilocalFinitePrimeEulerDensity p s
        ∂semilocalArchimedeanGammaMeasure) / semilocalFinitePrimeMass p := by
  rw [HTGeometry.momentInner_def, momentFunctional_semilocalFinitePrimeCyclicMoment p hprime]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp [Polynomial.eval_mul, sq]

/-! ## Uniform equivalence of the two moment forms -/

theorem momentInner_semilocalFinitePrimeCyclicMoment_le {n : ℕ} (p : Fin n → ℕ)
    (hprime : ∀ i, (p i).Prime) (q : ℝ[X]) :
    HTGeometry.momentInner (semilocalFinitePrimeCyclicMoment p) q q ≤
      semilocalJacobiComparisonConstant p *
        HTGeometry.momentInner ccmMetaplecticGammaMoment q q := by
  set A : ℝ := ∫ s : ℝ, (Polynomial.eval s q) ^ 2 ∂semilocalArchimedeanGammaMeasure with hA
  set N : ℝ := ∫ s : ℝ, (Polynomial.eval s q) ^ 2 * semilocalFinitePrimeEulerDensity p s
    ∂semilocalArchimedeanGammaMeasure with hN
  have hZpos : 0 < semilocalFinitePrimeMass p := semilocalFinitePrimeMass_pos p hprime
  have hAnonneg : 0 ≤ A := integral_nonneg fun s => sq_nonneg _
  have hKpos : 0 < semilocalJacobiComparisonConstant p :=
    semilocalJacobiComparisonConstant_pos p hprime
  have hupper : N ≤ semilocalEulerDensityUpper p * A := by
    have hmono : N ≤ ∫ s : ℝ, (Polynomial.eval s q) ^ 2 * semilocalEulerDensityUpper p
        ∂semilocalArchimedeanGammaMeasure := by
      refine integral_mono (integrable_sq_eval_mul_semilocalFinitePrimeEulerDensity p hprime q)
        ((integrable_sq_eval_semilocalArchimedeanGammaMeasure q).mul_const _) fun s => ?_
      exact mul_le_mul_of_nonneg_left
        (semilocalFinitePrimeEulerDensity_bounds p hprime s).2 (sq_nonneg _)
    calc N ≤ ∫ s : ℝ, (Polynomial.eval s q) ^ 2 * semilocalEulerDensityUpper p
              ∂semilocalArchimedeanGammaMeasure := hmono
      _ = semilocalEulerDensityUpper p * A := by
          rw [integral_mul_const, hA]; ring
  have hlowZ : semilocalEulerDensityLower p ≤ semilocalFinitePrimeMass p :=
    semilocalEulerDensityLower_le_mass p hprime
  rw [momentInner_semilocalFinitePrimeCyclicMoment_self p hprime,
    momentInner_ccmMetaplecticGammaMoment_self, ← hA, ← hN, div_le_iff₀ hZpos]
  calc N ≤ semilocalEulerDensityUpper p * A := hupper
    _ = semilocalJacobiComparisonConstant p * A * semilocalEulerDensityLower p := by
        rw [semilocalEulerDensityUpper_eq p hprime]; ring
    _ ≤ semilocalJacobiComparisonConstant p * A * semilocalFinitePrimeMass p :=
        mul_le_mul_of_nonneg_left hlowZ (by positivity)

theorem momentInner_ccmMetaplecticGammaMoment_le {n : ℕ} (p : Fin n → ℕ)
    (hprime : ∀ i, (p i).Prime) (q : ℝ[X]) :
    HTGeometry.momentInner ccmMetaplecticGammaMoment q q ≤
      semilocalJacobiComparisonConstant p *
        HTGeometry.momentInner (semilocalFinitePrimeCyclicMoment p) q q := by
  set A : ℝ := ∫ s : ℝ, (Polynomial.eval s q) ^ 2 ∂semilocalArchimedeanGammaMeasure with hA
  set N : ℝ := ∫ s : ℝ, (Polynomial.eval s q) ^ 2 * semilocalFinitePrimeEulerDensity p s
    ∂semilocalArchimedeanGammaMeasure with hN
  have hZpos : 0 < semilocalFinitePrimeMass p := semilocalFinitePrimeMass_pos p hprime
  have hAnonneg : 0 ≤ A := integral_nonneg fun s => sq_nonneg _
  have hKpos : 0 < semilocalJacobiComparisonConstant p :=
    semilocalJacobiComparisonConstant_pos p hprime
  have hlower : semilocalEulerDensityLower p * A ≤ N := by
    have hmono : (∫ s : ℝ, (Polynomial.eval s q) ^ 2 * semilocalEulerDensityLower p
        ∂semilocalArchimedeanGammaMeasure) ≤ N := by
      refine integral_mono ((integrable_sq_eval_semilocalArchimedeanGammaMeasure q).mul_const _)
        (integrable_sq_eval_mul_semilocalFinitePrimeEulerDensity p hprime q) fun s => ?_
      exact mul_le_mul_of_nonneg_left
        (semilocalFinitePrimeEulerDensity_bounds p hprime s).1 (sq_nonneg _)
    calc semilocalEulerDensityLower p * A
        = ∫ s : ℝ, (Polynomial.eval s q) ^ 2 * semilocalEulerDensityLower p
            ∂semilocalArchimedeanGammaMeasure := by rw [integral_mul_const, hA]; ring
      _ ≤ N := hmono
  have hupZ : semilocalFinitePrimeMass p ≤ semilocalEulerDensityUpper p := by
    have hint : Integrable (fun s : ℝ => semilocalFinitePrimeEulerDensity p s)
        semilocalArchimedeanGammaMeasure := by
      refine (integrable_pow_mul_semilocalFinitePrimeEulerDensity p hprime 0).congr ?_
      filter_upwards with s
      simp
    have hmono : semilocalFinitePrimeMass p ≤
        ∫ _s : ℝ, semilocalEulerDensityUpper p ∂semilocalArchimedeanGammaMeasure :=
      integral_mono hint (integrable_const _)
        (fun s => (semilocalFinitePrimeEulerDensity_bounds p hprime s).2)
    simpa using hmono
  rw [momentInner_semilocalFinitePrimeCyclicMoment_self p hprime,
    momentInner_ccmMetaplecticGammaMoment_self, ← hA, ← hN,
    show semilocalJacobiComparisonConstant p * (N / semilocalFinitePrimeMass p)
      = semilocalJacobiComparisonConstant p * N / semilocalFinitePrimeMass p from by ring,
    le_div_iff₀ hZpos]
  calc A * semilocalFinitePrimeMass p ≤ A * semilocalEulerDensityUpper p :=
        mul_le_mul_of_nonneg_left hupZ hAnonneg
    _ = semilocalJacobiComparisonConstant p * (semilocalEulerDensityLower p * A) := by
        rw [semilocalEulerDensityUpper_eq p hprime]; ring
    _ ≤ semilocalJacobiComparisonConstant p * N :=
        mul_le_mul_of_nonneg_left hlower hKpos.le

theorem positiveMomentForm_semilocalFinitePrimeCyclicMoment {n : ℕ} (p : Fin n → ℕ)
    (hprime : ∀ i, (p i).Prime) :
    HTGeometry.PositiveMomentForm (semilocalFinitePrimeCyclicMoment p) := by
  refine ⟨fun q hq => ?_⟩
  have harch : 0 < HTGeometry.momentInner ccmMetaplecticGammaMoment q q :=
    positiveMomentForm_ccmMetaplecticGammaMoment.pos_of_ne_zero q hq
  have hle := momentInner_ccmMetaplecticGammaMoment_le p hprime q
  have hKpos : 0 < semilocalJacobiComparisonConstant p :=
    semilocalJacobiComparisonConstant_pos p hprime
  nlinarith

/-! ## The semilocal Jacobi ladder -/

/-- The Jacobi coefficient `a_n(P)` of the normalized semilocal cyclic measure. -/
def semilocalFinitePrimeJacobiCoefficient {n : ℕ} (p : Fin n → ℕ) (k : ℕ) : ℝ :=
  Real.sqrt (HTGeometry.monicOrthoBeta (semilocalFinitePrimeCyclicMoment p) (k + 1))

theorem semilocalFinitePrimeJacobiCoefficient_pos {n : ℕ} (p : Fin n → ℕ)
    (hprime : ∀ i, (p i).Prime) (k : ℕ) :
    0 < semilocalFinitePrimeJacobiCoefficient p k :=
  Real.sqrt_pos.mpr
    (HTGeometry.monicOrthoBeta_pos (positiveMomentForm_semilocalFinitePrimeCyclicMoment p hprime)
      (Nat.succ_pos k))

/-- **Upper Jacobi comparison.**  `a_k(P) ≤ K_P · a_k(∅)`. -/
theorem semilocalFinitePrimeJacobiCoefficient_le {n : ℕ} (p : Fin n → ℕ)
    (hprime : ∀ i, (p i).Prime) (k : ℕ) :
    semilocalFinitePrimeJacobiCoefficient p k ≤
      semilocalJacobiComparisonConstant p * semilocalArchimedeanJacobiCoefficient k := by
  have hKpos : 0 < semilocalJacobiComparisonConstant p :=
    semilocalJacobiComparisonConstant_pos p hprime
  have hbeta : HTGeometry.monicOrthoBeta (semilocalFinitePrimeCyclicMoment p) (k + 1) ≤
      semilocalJacobiComparisonConstant p ^ 2 * (((k : ℝ) + 1 / 2) * ((k : ℝ) + 1)) := by
    have := HTGeometry.monicOrthoBeta_le_of_momentInner_le
      positiveMomentForm_ccmMetaplecticGammaMoment
      (positiveMomentForm_semilocalFinitePrimeCyclicMoment p hprime) hKpos
      (momentInner_semilocalFinitePrimeCyclicMoment_le p hprime)
      (momentInner_ccmMetaplecticGammaMoment_le p hprime) k
    rwa [monicOrthoBeta_ccmMetaplecticGammaMoment k] at this
  calc semilocalFinitePrimeJacobiCoefficient p k
      ≤ Real.sqrt (semilocalJacobiComparisonConstant p ^ 2 *
          (((k : ℝ) + 1 / 2) * ((k : ℝ) + 1))) := Real.sqrt_le_sqrt hbeta
    _ = semilocalJacobiComparisonConstant p * semilocalArchimedeanJacobiCoefficient k := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hKpos.le,
          semilocalArchimedeanJacobiCoefficient]

/-- **Lower Jacobi comparison.**  `a_k(∅) ≤ K_P · a_k(P)`. -/
theorem semilocalArchimedeanJacobiCoefficient_le {n : ℕ} (p : Fin n → ℕ)
    (hprime : ∀ i, (p i).Prime) (k : ℕ) :
    semilocalArchimedeanJacobiCoefficient k ≤
      semilocalJacobiComparisonConstant p * semilocalFinitePrimeJacobiCoefficient p k := by
  have hKpos : 0 < semilocalJacobiComparisonConstant p :=
    semilocalJacobiComparisonConstant_pos p hprime
  have hbeta : ((k : ℝ) + 1 / 2) * ((k : ℝ) + 1) ≤
      semilocalJacobiComparisonConstant p ^ 2 *
        HTGeometry.monicOrthoBeta (semilocalFinitePrimeCyclicMoment p) (k + 1) := by
    have := HTGeometry.monicOrthoBeta_le_of_momentInner_le
      (positiveMomentForm_semilocalFinitePrimeCyclicMoment p hprime)
      positiveMomentForm_ccmMetaplecticGammaMoment hKpos
      (momentInner_ccmMetaplecticGammaMoment_le p hprime)
      (momentInner_semilocalFinitePrimeCyclicMoment_le p hprime) k
    rwa [monicOrthoBeta_ccmMetaplecticGammaMoment k] at this
  calc semilocalArchimedeanJacobiCoefficient k
      = Real.sqrt (((k : ℝ) + 1 / 2) * ((k : ℝ) + 1)) := rfl
    _ ≤ Real.sqrt (semilocalJacobiComparisonConstant p ^ 2 *
          HTGeometry.monicOrthoBeta (semilocalFinitePrimeCyclicMoment p) (k + 1)) :=
        Real.sqrt_le_sqrt hbeta
    _ = semilocalJacobiComparisonConstant p * semilocalFinitePrimeJacobiCoefficient p k := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hKpos.le,
          semilocalFinitePrimeJacobiCoefficient]

/-! ## Linear growth and the failure of the Carleman criterion -/

theorem le_semilocalArchimedeanJacobiCoefficient (k : ℕ) :
    (k : ℝ) + 1 / 2 ≤ semilocalArchimedeanJacobiCoefficient k := by
  rw [semilocalArchimedeanJacobiCoefficient]
  refine Real.le_sqrt' (by positivity) |>.mpr ?_
  nlinarith [(by positivity : (0:ℝ) ≤ (k : ℝ))]

/-- Linear lower growth of the semilocal Jacobi coefficients. -/
theorem semilocalFinitePrimeJacobiCoefficient_lower {n : ℕ} (p : Fin n → ℕ)
    (hprime : ∀ i, (p i).Prime) (k : ℕ) :
    ((k : ℝ) + 1 / 2) / semilocalJacobiComparisonConstant p ≤
      semilocalFinitePrimeJacobiCoefficient p k := by
  have hKpos : 0 < semilocalJacobiComparisonConstant p :=
    semilocalJacobiComparisonConstant_pos p hprime
  rw [div_le_iff₀ hKpos]
  have h1 := le_semilocalArchimedeanJacobiCoefficient k
  have h2 := semilocalArchimedeanJacobiCoefficient_le p hprime k
  nlinarith

/-- Even parity block off-diagonal `b_k^+(P) = a_{2k}(P) a_{2k+1}(P)`. -/
def semilocalProlateEvenOffDiagonal {n : ℕ} (p : Fin n → ℕ) (k : ℕ) : ℝ :=
  semilocalFinitePrimeJacobiCoefficient p (2 * k) *
    semilocalFinitePrimeJacobiCoefficient p (2 * k + 1)

/-- Odd parity block off-diagonal `b_k^-(P) = a_{2k+1}(P) a_{2k+2}(P)`. -/
def semilocalProlateOddOffDiagonal {n : ℕ} (p : Fin n → ℕ) (k : ℕ) : ℝ :=
  semilocalFinitePrimeJacobiCoefficient p (2 * k + 1) *
    semilocalFinitePrimeJacobiCoefficient p (2 * k + 2)

theorem semilocalProlate_offDiagonal_lower {n : ℕ} (p : Fin n → ℕ)
    (hprime : ∀ i, (p i).Prime) (k : ℕ) :
    ((k : ℝ) + 1) ^ 2 / (4 * semilocalJacobiComparisonConstant p ^ 2) ≤
        semilocalProlateEvenOffDiagonal p k ∧
      ((k : ℝ) + 1) ^ 2 / (4 * semilocalJacobiComparisonConstant p ^ 2) ≤
        semilocalProlateOddOffDiagonal p k := by
  have hKpos : 0 < semilocalJacobiComparisonConstant p :=
    semilocalJacobiComparisonConstant_pos p hprime
  have key : ∀ m : ℕ, ((k : ℝ) + 1) / (2 * semilocalJacobiComparisonConstant p) ≤
      semilocalFinitePrimeJacobiCoefficient p (2 * k + m) := by
    intro m
    have h := semilocalFinitePrimeJacobiCoefficient_lower p hprime (2 * k + m)
    have hcast : ((k : ℝ) + 1) / 2 ≤ ((2 * k + m : ℕ) : ℝ) + 1 / 2 := by
      push_cast
      have : (0 : ℝ) ≤ (m : ℕ) := Nat.cast_nonneg m
      nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ (k : ℝ))]
    have hdiv : ((k : ℝ) + 1) / (2 * semilocalJacobiComparisonConstant p) ≤
        (((2 * k + m : ℕ) : ℝ) + 1 / 2) / semilocalJacobiComparisonConstant p := by
      rw [div_le_div_iff₀ (by positivity) hKpos]
      nlinarith
    exact hdiv.trans h
  have hposq : (0 : ℝ) ≤ ((k : ℝ) + 1) / (2 * semilocalJacobiComparisonConstant p) := by
    positivity
  have hsplit : ((k : ℝ) + 1) ^ 2 / (4 * semilocalJacobiComparisonConstant p ^ 2)
      = (((k : ℝ) + 1) / (2 * semilocalJacobiComparisonConstant p)) *
        (((k : ℝ) + 1) / (2 * semilocalJacobiComparisonConstant p)) := by
    field_simp
    ring
  constructor
  · rw [hsplit, semilocalProlateEvenOffDiagonal]
    exact mul_le_mul (by simpa using key 0) (key 1) hposq
      (le_trans hposq (by simpa using key 0))
  · rw [hsplit, semilocalProlateOddOffDiagonal]
    exact mul_le_mul (key 1) (key 2) hposq (le_trans hposq (key 1))

theorem summable_one_div_succ_sq : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
  have hbase : Summable fun k : ℕ => 1 / (k : ℝ) ^ 2 :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff 1).mpr hbase
  refine hshift.congr fun k => ?_
  push_cast
  ring

/-- **The Carleman divergence criterion is unavailable.**  Both parity blocks of the formal
semilocal prolate Jacobi matrix have summable reciprocal off-diagonals. -/
theorem summable_inv_semilocalProlateOffDiagonal {n : ℕ} (p : Fin n → ℕ)
    (hprime : ∀ i, (p i).Prime) :
    Summable (fun k : ℕ => (semilocalProlateEvenOffDiagonal p k)⁻¹) ∧
      Summable (fun k : ℕ => (semilocalProlateOddOffDiagonal p k)⁻¹) := by
  have hKpos : 0 < semilocalJacobiComparisonConstant p :=
    semilocalJacobiComparisonConstant_pos p hprime
  have hmaj : Summable fun k : ℕ =>
      4 * semilocalJacobiComparisonConstant p ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) :=
    summable_one_div_succ_sq.mul_left _
  have hstep : ∀ (b : ℕ → ℝ), (∀ k, 0 < b k) →
      (∀ k : ℕ, ((k : ℝ) + 1) ^ 2 / (4 * semilocalJacobiComparisonConstant p ^ 2) ≤ b k) →
      Summable (fun k : ℕ => (b k)⁻¹) := by
    intro b hbpos hblow
    refine hmaj.of_nonneg_of_le (fun k => (inv_pos.mpr (hbpos k)).le) fun k => ?_
    have hlow := hblow k
    have hposd : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 / (4 * semilocalJacobiComparisonConstant p ^ 2) := by
      positivity
    have : (b k)⁻¹ ≤ (((k : ℝ) + 1) ^ 2 / (4 * semilocalJacobiComparisonConstant p ^ 2))⁻¹ := by
      gcongr
    refine this.trans_eq ?_
    field_simp
  refine ⟨hstep _ (fun k => ?_) (fun k => (semilocalProlate_offDiagonal_lower p hprime k).1),
    hstep _ (fun k => ?_) (fun k => (semilocalProlate_offDiagonal_lower p hprime k).2)⟩
  · exact mul_pos (semilocalFinitePrimeJacobiCoefficient_pos p hprime _)
      (semilocalFinitePrimeJacobiCoefficient_pos p hprime _)
  · exact mul_pos (semilocalFinitePrimeJacobiCoefficient_pos p hprime _)
      (semilocalFinitePrimeJacobiCoefficient_pos p hprime _)

/-- The card's closed form `a_n(∅) = √((2n+1)(2n+2))/2`. -/
theorem semilocalArchimedeanJacobiCoefficient_eq_sqrt_div_two (k : ℕ) :
    semilocalArchimedeanJacobiCoefficient k =
      Real.sqrt ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2)) / 2 := by
  rw [semilocalArchimedeanJacobiCoefficient, eq_div_iff (by norm_num : (2 : ℝ) ≠ 0),
    ← Real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_mul (by positivity)]
  congr 1
  ring

/-- Quadratic upper growth of the semilocal Jacobi coefficients. -/
theorem semilocalFinitePrimeJacobiCoefficient_upper {n : ℕ} (p : Fin n → ℕ)
    (hprime : ∀ i, (p i).Prime) (k : ℕ) :
    semilocalFinitePrimeJacobiCoefficient p k ≤
      semilocalJacobiComparisonConstant p * ((k : ℝ) + 1) := by
  have hKpos : 0 < semilocalJacobiComparisonConstant p :=
    semilocalJacobiComparisonConstant_pos p hprime
  have h1 := semilocalFinitePrimeJacobiCoefficient_le p hprime k
  have h2 : semilocalArchimedeanJacobiCoefficient k ≤ (k : ℝ) + 1 := by
    rw [semilocalArchimedeanJacobiCoefficient]
    have hle : ((k : ℝ) + 1 / 2) * ((k : ℝ) + 1) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
    calc Real.sqrt (((k : ℝ) + 1 / 2) * ((k : ℝ) + 1))
        ≤ Real.sqrt (((k : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt hle
      _ = (k : ℝ) + 1 := Real.sqrt_sq (by positivity)
  nlinarith

theorem semilocalProlate_offDiagonal_upper {n : ℕ} (p : Fin n → ℕ)
    (hprime : ∀ i, (p i).Prime) (k : ℕ) :
    semilocalProlateEvenOffDiagonal p k ≤
        semilocalJacobiComparisonConstant p ^ 2 * (2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2) ∧
      semilocalProlateOddOffDiagonal p k ≤
        semilocalJacobiComparisonConstant p ^ 2 * (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 3) := by
  have hKpos : 0 < semilocalJacobiComparisonConstant p :=
    semilocalJacobiComparisonConstant_pos p hprime
  have hstep : ∀ m : ℕ, semilocalFinitePrimeJacobiCoefficient p m ≤
      semilocalJacobiComparisonConstant p * ((m : ℝ) + 1) :=
    semilocalFinitePrimeJacobiCoefficient_upper p hprime
  have hpos : ∀ m : ℕ, 0 < semilocalFinitePrimeJacobiCoefficient p m :=
    semilocalFinitePrimeJacobiCoefficient_pos p hprime
  constructor
  · have h0 := hstep (2 * k)
    have h1 := hstep (2 * k + 1)
    have hc0 : ((2 * k : ℕ) : ℝ) + 1 = 2 * (k : ℝ) + 1 := by push_cast; ring
    have hc1 : ((2 * k + 1 : ℕ) : ℝ) + 1 = 2 * (k : ℝ) + 2 := by push_cast; ring
    rw [hc0] at h0
    rw [hc1] at h1
    rw [semilocalProlateEvenOffDiagonal]
    nlinarith [hpos (2 * k), hpos (2 * k + 1), (Nat.cast_nonneg k : (0:ℝ) ≤ (k : ℝ))]
  · have h1 := hstep (2 * k + 1)
    have h2 := hstep (2 * k + 2)
    have hc1 : ((2 * k + 1 : ℕ) : ℝ) + 1 = 2 * (k : ℝ) + 2 := by push_cast; ring
    have hc2 : ((2 * k + 2 : ℕ) : ℝ) + 1 = 2 * (k : ℝ) + 3 := by push_cast; ring
    rw [hc1] at h1
    rw [hc2] at h2
    rw [semilocalProlateOddOffDiagonal]
    nlinarith [hpos (2 * k + 1), hpos (2 * k + 2), (Nat.cast_nonneg k : (0:ℝ) ≤ (k : ℝ))]

end RHTower
