import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.PolynomialQuotientFrequencies
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.EntirePrimeOrbitValue

/-!
# Polynomial restriction to the full prime orbit

Every polynomial uses finitely many primes, but no common finite invariant
set is required. Unique factorization separates its frequencies, Bohr
averages recover its coefficients, and finite spectra give entire extensions.
-/

open Finset Complex Filter Topology
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

/-- The orbit with one coordinate for every prime. -/
def globalOrbitPoint (t : ℝ) (p : Nat.Primes) : ℂ :=
  InfiniteRankWeilTheory.phase (p : ℕ) t

/-- The frequency of a monomial in arbitrary prime variables. -/
def globalFrequency (α : Nat.Primes →₀ ℕ) : ℝ :=
  α.sum fun p n => (n : ℝ) * Real.log (p : ℕ)

theorem globalFrequency_injective : Function.Injective globalFrequency := by
  intro α β h
  exact log_prime_nat_relation_eq α β h

/-- Exponentiating a prime frequency recovers its natural-number monomial. -/
theorem exp_globalFrequency (α : Nat.Primes →₀ ℕ) :
    Real.exp (globalFrequency α) = (primeProduct α : ℝ) := by
  rw [globalFrequency, ← log_primeProduct, Real.exp_log]
  exact_mod_cast primeProduct_pos α

/-- Polynomial evaluation along the full prime orbit. -/
def globalOrbitValue (F : MvPolynomial Nat.Primes ℂ) (t : ℝ) : ℂ :=
  MvPolynomial.eval (globalOrbitPoint t) F

theorem globalOrbitValue_eq_wave (F : MvPolynomial Nat.Primes ℂ) (t : ℝ) :
    globalOrbitValue F t =
      finiteExpWave F.support F.coeff (fun α => -globalFrequency α) t := by
  classical
  rw [globalOrbitValue, MvPolynomial.eval_eq]
  unfold finiteExpWave
  refine sum_congr rfl fun α _ => ?_
  congr 1
  simp only [globalOrbitPoint, InfiniteRankWeilTheory.phase, ← Complex.exp_nat_mul,
    ← Complex.exp_sum, expChar]
  congr 1
  unfold globalFrequency Finsupp.sum
  push_cast
  rw [← sum_neg_distrib, sum_mul, sum_mul]
  refine sum_congr rfl fun p _ => ?_
  ring

theorem globalOrbitValue_mul (F G : MvPolynomial Nat.Primes ℂ) (t : ℝ) :
    globalOrbitValue (F * G) t = globalOrbitValue F t * globalOrbitValue G t :=
  map_mul (MvPolynomial.eval (globalOrbitPoint t)) F G

/-- Orbit restriction loses no coefficient, even with infinitely many available variables. -/
theorem bohrCoefficient_globalOrbitValue (F : MvPolynomial Nat.Primes ℂ)
    (α : Nat.Primes →₀ ℕ) :
    bohrCoefficient (globalOrbitValue F) (-globalFrequency α) = F.coeff α := by
  classical
  have hfun : globalOrbitValue F =
      fun t => ∑ β ∈ F.support, F.coeff β * expChar (-globalFrequency β) t :=
    funext (globalOrbitValue_eq_wave F)
  rw [hfun, bohrCoefficient_sum_expChar]
  simp only [neg_inj, globalFrequency_injective.eq_iff, sum_ite_eq']
  by_cases hα : F.coeff α = 0 <;> simp [MvPolynomial.mem_support_iff, hα]

theorem globalOrbitValue_injective : Function.Injective globalOrbitValue := by
  intro F G h
  ext α
  have hc := congrArg (fun f : ℝ → ℂ => bohrCoefficient f (-globalFrequency α)) h
  simpa only [bohrCoefficient_globalOrbitValue] using hc

/-- The entire finite exponential sum determined by a global polynomial. -/
def entireGlobalOrbitValue (F : MvPolynomial Nat.Primes ℂ) (z : ℂ) : ℂ :=
  entireExpWave F.support F.coeff (fun α => ((-globalFrequency α : ℝ) : ℂ) * Complex.I) z

theorem entireGlobalOrbitValue_ofReal (F : MvPolynomial Nat.Primes ℂ) (t : ℝ) :
    entireGlobalOrbitValue F t = globalOrbitValue F t := by
  rw [globalOrbitValue_eq_wave]
  unfold entireGlobalOrbitValue entireExpWave finiteExpWave
  apply sum_congr rfl
  intro α _
  congr 1
  unfold expChar
  congr 1
  push_cast
  ring

theorem analyticOnNhd_entireGlobalOrbitValue (F : MvPolynomial Nat.Primes ℂ) :
    AnalyticOnNhd ℂ (entireGlobalOrbitValue F) Set.univ :=
  analyticOnNhd_univ_iff_differentiable.mpr (differentiable_entireExpWave _ _ _)

theorem entireGlobalOrbitValue_proximity (F : MvPolynomial Nat.Primes ℂ) :
    ValueDistribution.proximity (entireGlobalOrbitValue F) ⊤ =o[atTop]
      fun r : ℝ => r ^ (2 : ℕ) := by
  obtain ⟨C, hC, hb⟩ := entireExpWave_orderOne_bound F.support F.coeff
    (fun α => ((-globalFrequency α : ℝ) : ℂ) * Complex.I)
  exact _root_.RHTower.OrderOneRigidity.proximity_isLittleO_sq_of_growth hC
    (differentiable_entireExpWave _ _ _) hb

/-- A quotient character has a difference of finite prime frequencies. -/
theorem global_polynomial_quotient_character_frequency
    (N D : MvPolynomial Nat.Primes ℂ) (c : ℂ) (γ : ℝ) (hc : c ≠ 0)
    (hD : D ≠ 0)
    (h : ∀ t, globalOrbitValue N t = c * expChar γ t * globalOrbitValue D t) :
    ∃ α β : Nat.Primes →₀ ℕ, γ = globalFrequency α - globalFrequency β := by
  classical
  have hDs : D.support.Nonempty := by
    by_contra he
    have hs : D.support = ∅ := not_nonempty_iff_eq_empty.mp he
    apply hD
    conv_lhs => rw [MvPolynomial.as_sum D]
    rw [hs, sum_empty]
  obtain ⟨α, hα⟩ := hDs
  have hcα : c * D.coeff α ≠ 0 := mul_ne_zero hc (MvPolynomial.mem_support_iff.mp hα)
  have hfun : globalOrbitValue N =
      fun t => globalOrbitValue (MvPolynomial.C c * D) t * expChar γ t := by
    funext t
    rw [h t]
    simp only [globalOrbitValue, map_mul, MvPolynomial.eval_C]
    ring
  have hcoef : bohrCoefficient (globalOrbitValue N) (γ - globalFrequency α) =
      c * D.coeff α := by
    rw [hfun, bohrCoefficient_mul_expChar,
      show γ - globalFrequency α - γ = -globalFrequency α by ring,
      bohrCoefficient_globalOrbitValue, MvPolynomial.coeff_C_mul]
  have hNfun : globalOrbitValue N =
      fun t => ∑ β ∈ N.support, N.coeff β * expChar (-globalFrequency β) t :=
    funext (globalOrbitValue_eq_wave N)
  rw [hNfun, bohrCoefficient_sum_expChar] at hcoef
  have hβ : ∃ β ∈ N.support, -globalFrequency β = γ - globalFrequency α := by
    by_contra hnone
    push Not at hnone
    have hz : (∑ β ∈ N.support,
        if -globalFrequency β = γ - globalFrequency α then N.coeff β else 0) = 0 := by
      apply sum_eq_zero
      intro β hβ
      exact if_neg (hnone β hβ)
    rw [hz] at hcoef
    exact hcα hcoef.symm
  obtain ⟨β, _, hβ⟩ := hβ
  exact ⟨α, β, by linarith⟩

#print axioms globalOrbitValue_injective
#print axioms entireGlobalOrbitValue_proximity
#print axioms global_polynomial_quotient_character_frequency
end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
