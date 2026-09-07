import GaloisForLFunctions.RHTower.FiniteDirichletDivisorPoleSurvival
import GaloisForLFunctions.RHTower.GibbsMoebiusAnchor
import GaloisForLFunctions.RHTower.Sieve.EulerExpansion
import GaloisForLFunctions.RHTower.FiniteDirichletCriticalNonannihilation

/-!
# Exact finite numerators of retained-prime functionals

The coefficient of a squarefree integer supported on the retained prime set is
its literal Möbius value times the functional at its prime-factor subset. These
coefficients recover every retained coordinate. Their Dirichlet polynomial is
exactly the complete subset sum, and a nonzero functional leaves arbitrarily
high simple critical poles in the candidate Mellin expression. The infinite
weighted Möbius Euler identity and source-integral transport remain separate.
-/

noncomputable section
open scoped BigOperators
namespace RHTower

/-- The exact finite Möbius numerator attached to a functional on retained prime subsets. -/
def retainedPrimeDirichletCoefficients (P : Finset ℕ) (y : Finset ℕ → ℂ) : ℕ →₀ ℂ :=
  Finsupp.onFinset (P.powerset.image (fun R => ∏ p ∈ R, p))
    (fun n => if n.primeFactors ⊆ P then (ArithmeticFunction.moebius n : ℂ) * y n.primeFactors else 0)
    (by
      intro n hn
      by_cases hs : n.primeFactors ⊆ P
      · have hm : (ArithmeticFunction.moebius n : ℂ) ≠ 0 := by
          intro hm
          simp [hs, hm] at hn
        have hmi : ArithmeticFunction.moebius n ≠ 0 := by exact_mod_cast hm
        have hsq := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmi
        exact Finset.mem_image.mpr ⟨n.primeFactors, Finset.mem_powerset.mpr hs,
          Nat.prod_primeFactors_of_squarefree hsq⟩
      · simp [hs] at hn)

/-- No coefficient is introduced at the excluded Dirichlet index zero. -/
@[simp] theorem retainedPrimeDirichletCoefficients_zero (P : Finset ℕ) (y : Finset ℕ → ℂ) :
    retainedPrimeDirichletCoefficients P y 0 = 0 := by
  simp [retainedPrimeDirichletCoefficients]

/-- Every retained subset is recovered at its own squarefree product. -/
theorem retainedPrimeDirichletCoefficients_prod (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (y : Finset ℕ → ℂ) {R : Finset ℕ} (hR : R ⊆ P) :
    retainedPrimeDirichletCoefficients P y (∏ p ∈ R, p) =
      (ArithmeticFunction.moebius (∏ p ∈ R, p) : ℂ) * y R := by
  simp only [retainedPrimeDirichletCoefficients, Finsupp.onFinset_apply,
    Sieve.primeFactors_prod_of_subset hP hR, if_pos hR]

/-- A nonzero retained coordinate makes the finite Möbius numerator nonzero. -/
theorem retainedPrimeDirichletCoefficients_ne_zero (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (y : Finset ℕ → ℂ) (hy : ∃ R : Finset ℕ, R ⊆ P ∧ y R ≠ 0) :
    retainedPrimeDirichletCoefficients P y ≠ 0 := by
  obtain ⟨R, hR, hyR⟩ := hy
  intro h
  have he := congrArg (fun a : ℕ →₀ ℂ => a (∏ p ∈ R, p)) h
  rw [retainedPrimeDirichletCoefficients_prod P hP y hR] at he
  have hm : (ArithmeticFunction.moebius (∏ p ∈ R, p) : ℂ) ≠ 0 := by
    exact_mod_cast (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr
      (GibbsGas.squarefree_prod_primes (fun p hp => hP p (hR hp))))
  exact (mul_ne_zero hm hyR) he

/-- The finite Dirichlet polynomial is literally the Möbius-weighted sum over
all retained subsets; no coordinate or scalar term is omitted. -/
theorem finiteDirichletPolynomial_retainedPrime_eq_sum
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (y : Finset ℕ → ℂ) (s : ℂ) :
    finiteDirichletPolynomial (retainedPrimeDirichletCoefficients P y) s =
      ∑ R ∈ P.powerset, (ArithmeticFunction.moebius (∏ p ∈ R, p) : ℂ) * y R *
        ((∏ p ∈ R, p : ℕ) : ℂ) ^ (-s) := by
  let a := retainedPrimeDirichletCoefficients P y
  have hs : a.support ⊆ P.powerset.image (fun R => ∏ p ∈ R, p) :=
    Finsupp.support_onFinset_subset
  calc
    finiteDirichletPolynomial a s =
        ∑ n ∈ P.powerset.image (fun R => ∏ p ∈ R, p), a n * (n : ℂ) ^ (-s) := by
      apply Finset.sum_subset hs
      intro n hn hna
      rw [Finsupp.notMem_support_iff.mp hna, zero_mul]
    _ = ∑ R ∈ P.powerset, a (∏ p ∈ R, p) * ((∏ p ∈ R, p : ℕ) : ℂ) ^ (-s) := by
      rw [Finset.sum_image]
      exact Sieve.prod_injOn_powerset hP
    _ = _ := by
      apply Finset.sum_congr rfl
      intro R hR
      rw [show a = retainedPrimeDirichletCoefficients P y by rfl,
        retainedPrimeDirichletCoefficients_prod P hP y (Finset.mem_powerset.mp hR)]

/-- Every nonzero functional on a finite retained prime field has a numerator
that survives at simple critical Xi zeros beyond every height. -/
theorem exists_high_simpleCritical_retainedPrime_numerator_ne_zero
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (y : Finset ℕ → ℂ)
    (hy : ∃ R : Finset ℕ, R ⊆ P ∧ y R ≠ 0) (T : ℝ) :
    ∃ t : ℝ, T < t ∧ 0 < t ∧ xi (linePt t) = 0 ∧
      (analyticOrderAt xi (linePt t)).toNat = 1 ∧
      (∑ R ∈ P.powerset, (ArithmeticFunction.moebius (∏ p ∈ R, p) : ℂ) * y R *
        ((∏ p ∈ R, p : ℕ) : ℂ) ^ (-linePt t)) ≠ 0 := by
  have h := exists_high_simpleCritical_finiteDirichletPolynomial_ne_zero
    (retainedPrimeDirichletCoefficients P y) (retainedPrimeDirichletCoefficients_zero P y)
    (retainedPrimeDirichletCoefficients_ne_zero P hP y hy) T
  simpa only [finiteDirichletPolynomial_retainedPrime_eq_sum P hP y] using h


/-- The numerator vanishes exactly when every retained coordinate vanishes. -/
theorem retainedPrimeDirichletCoefficients_eq_zero_iff
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (y : Finset ℕ → ℂ) :
    retainedPrimeDirichletCoefficients P y = 0 ↔ ∀ R : Finset ℕ, R ⊆ P → y R = 0 := by
  constructor
  · intro hz R hR
    by_contra hRne
    exact retainedPrimeDirichletCoefficients_ne_zero P hP y ⟨R, hR, hRne⟩ hz
  · intro hy
    ext n
    by_cases hn : n.primeFactors ⊆ P
    · simp [retainedPrimeDirichletCoefficients, hn, hy _ hn]
    · simp [retainedPrimeDirichletCoefficients, hn]

/-- Every nonzero retained-field functional leaves arbitrarily high simple critical
poles in the proposed source Mellin transform, with any finite Euler aperture. -/
theorem exists_high_simpleCritical_retainedPrime_Mellin_pole
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (y : Finset ℕ → ℂ)
    (hy : ∃ R : Finset ℕ, R ⊆ P ∧ y R ≠ 0) (Q : Finset Nat.Primes) (c : ℂ) (T : ℝ) :
    ∃ t : ℝ, T < t ∧ 0 < t ∧ xi (linePt t) = 0 ∧
      (analyticOrderAt xi (linePt t)).toNat = 1 ∧
      meromorphicOrderAt
        (finiteDirichletDivisorMellin (retainedPrimeDirichletCoefficients P y) Q c)
        (linePt t + 1 / 2) = ((-1 : ℤ) : WithTop ℤ) :=
  exists_high_simpleCritical_finiteDirichletDivisorMellin_pole
    (retainedPrimeDirichletCoefficients P y) (retainedPrimeDirichletCoefficients_zero P y)
    (retainedPrimeDirichletCoefficients_ne_zero P hP y hy) Q c T

end RHTower
