import Mathlib

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Finite point-count law. Probability axioms are carried as data. -/
structure FinitePointCountLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  count : Ω → ℕ
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  weight_sum_one : ∑ ω, weight ω = 1

/-- Factorial moment `E[(N)_k]`. -/
def FinitePointCountLaw.factorialMoment {Ω : Type*} [Fintype Ω]
    (law : FinitePointCountLaw Ω) (k : ℕ) : ℝ :=
  ∑ ω, law.weight ω * (law.count ω).descFactorial k

/-- First factorial cumulant. -/
def FinitePointCountLaw.factorialCumulantOne {Ω : Type*} [Fintype Ω]
    (law : FinitePointCountLaw Ω) : ℝ :=
  law.factorialMoment 1

/-- Second factorial cumulant. -/
def FinitePointCountLaw.factorialCumulantTwo {Ω : Type*} [Fintype Ω]
    (law : FinitePointCountLaw Ω) : ℝ :=
  law.factorialMoment 2 - law.factorialMoment 1 ^ (2 : ℕ)

/-- Third factorial cumulant. -/
def FinitePointCountLaw.factorialCumulantThree {Ω : Type*} [Fintype Ω]
    (law : FinitePointCountLaw Ω) : ℝ :=
  law.factorialMoment 3 -
    3 * law.factorialMoment 2 * law.factorialMoment 1 +
    2 * law.factorialMoment 1 ^ (3 : ℕ)

/-- Exact void mass `P(N=0)`. -/
def FinitePointCountLaw.voidMass {Ω : Type*} [Fintype Ω]
    (law : FinitePointCountLaw Ω) : ℝ :=
  ∑ ω, if law.count ω = 0 then law.weight ω else 0

/-- Alternating binomial sum over a count is its zero-count indicator. -/
theorem greedyBump_alternating_choose_real (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ k * (n.choose k : ℝ)) = if n = 0 then 1 else 0 := by
  exact_mod_cast Int.alternating_sum_range_choose (n := n)

/-- Exact finite inclusion-exclusion formula for void mass. -/
theorem FinitePointCountLaw.voidMass_eq_alternating_choose
    {Ω : Type*} [Fintype Ω] (law : FinitePointCountLaw Ω) :
    law.voidMass =
      ∑ ω, law.weight ω *
        (∑ k ∈ Finset.range (law.count ω + 1),
          (-1 : ℝ) ^ k * (law.count ω).choose k) := by
  unfold voidMass
  apply Finset.sum_congr rfl
  intro ω hω
  rw [greedyBump_alternating_choose_real]
  split_ifs with h
  · simp
  · simp

/-- Probability parameter, with admissibility carried as data. -/
abbrev ProbabilityParameter := {p : ℝ // 0 ≤ p ∧ p ≤ 1}

/-- Hellinger affinity of two one-point hard-exclusion count laws. -/
def greedyBumpBernoulliHellingerAffinity (p q : ProbabilityParameter) : ℝ :=
  Real.sqrt ((1 - (p : ℝ)) * (1 - (q : ℝ))) + Real.sqrt ((p : ℝ) * (q : ℝ))

/-- One possible extremum in a cell: a finite hard-exclusion law. -/
def greedyBumpBernoulliExclusion (p : ProbabilityParameter) :
    FinitePointCountLaw Bool where
  weight b := if b then (p : ℝ) else 1 - (p : ℝ)
  count b := if b then 1 else 0
  weight_nonneg b := by
    cases b <;> simp [sub_nonneg.mpr p.property.2, p.property.1]
  weight_sum_one := by
    simp

/-- Hard exclusion has first factorial cumulant `p`. -/
theorem greedyBumpBernoulli_factorialCumulantOne (p : ProbabilityParameter) :
    (greedyBumpBernoulliExclusion p).factorialCumulantOne = p := by
  simp [FinitePointCountLaw.factorialCumulantOne,
    FinitePointCountLaw.factorialMoment, greedyBumpBernoulliExclusion]

/-- Hard exclusion forces negative second factorial cumulant `-p^(2 : ℕ)`. -/
theorem greedyBumpBernoulli_factorialCumulantTwo (p : ProbabilityParameter) :
    (greedyBumpBernoulliExclusion p).factorialCumulantTwo = -(p : ℝ) ^ (2 : ℕ) := by
  simp [FinitePointCountLaw.factorialCumulantTwo,
    FinitePointCountLaw.factorialMoment, greedyBumpBernoulliExclusion]

/-- Hard exclusion has third factorial cumulant `2p^(3 : ℕ)`. -/
theorem greedyBumpBernoulli_factorialCumulantThree (p : ProbabilityParameter) :
    (greedyBumpBernoulliExclusion p).factorialCumulantThree = 2 * (p : ℝ) ^ (3 : ℕ) := by
  simp [FinitePointCountLaw.factorialCumulantThree,
    FinitePointCountLaw.factorialMoment, greedyBumpBernoulliExclusion]

/-- Hard exclusion void mass is exactly `1-p`. -/
theorem greedyBumpBernoulli_voidMass (p : ProbabilityParameter) :
    (greedyBumpBernoulliExclusion p).voidMass = 1 - (p : ℝ) := by
  simp [FinitePointCountLaw.voidMass, greedyBumpBernoulliExclusion]

/-- Strict probability parameter, with the open upper bound carried as data. -/
abbrev StrictProbabilityParameter := {p : ℝ // 0 ≤ p ∧ p < 1}

/-- Forget the strict upper bound on a probability parameter. -/
def StrictProbabilityParameter.toProbabilityParameter (p : StrictProbabilityParameter) :
    ProbabilityParameter :=
  ⟨p, p.property.1, p.property.2.le⟩

/-- Order-`k+1` factorial cumulant of a one-point hard-exclusion law. -/
def greedyBumpBernoulliFactorialCumulantSucc
    (p : StrictProbabilityParameter) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * k.factorial * (p : ℝ) ^ (k + 1)

/-- Paper's signed, factorially normalized order-`k+1` void contribution. -/
def greedyBumpBernoulliLogVoidContribution
    (p : StrictProbabilityParameter) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ (k + 1) * greedyBumpBernoulliFactorialCumulantSucc p k /
    (k + 1).factorial

/-- The all-order hierarchy extends the actual first factorial cumulant. -/
theorem greedyBumpBernoulli_factorialCumulantSucc_zero
    (p : StrictProbabilityParameter) :
    greedyBumpBernoulliFactorialCumulantSucc p 0 =
      (greedyBumpBernoulliExclusion p.toProbabilityParameter).factorialCumulantOne := by
  rw [greedyBumpBernoulli_factorialCumulantOne]
  simp [greedyBumpBernoulliFactorialCumulantSucc,
    StrictProbabilityParameter.toProbabilityParameter]

/-- The all-order hierarchy extends the actual second factorial cumulant. -/
theorem greedyBumpBernoulli_factorialCumulantSucc_one
    (p : StrictProbabilityParameter) :
    greedyBumpBernoulliFactorialCumulantSucc p 1 =
      (greedyBumpBernoulliExclusion p.toProbabilityParameter).factorialCumulantTwo := by
  rw [greedyBumpBernoulli_factorialCumulantTwo]
  simp [greedyBumpBernoulliFactorialCumulantSucc,
    StrictProbabilityParameter.toProbabilityParameter]

/-- The all-order hierarchy extends the actual third factorial cumulant. -/
theorem greedyBumpBernoulli_factorialCumulantSucc_two
    (p : StrictProbabilityParameter) :
    greedyBumpBernoulliFactorialCumulantSucc p 2 =
      (greedyBumpBernoulliExclusion p.toProbabilityParameter).factorialCumulantThree := by
  rw [greedyBumpBernoulli_factorialCumulantThree]
  norm_num [greedyBumpBernoulliFactorialCumulantSucc,
    StrictProbabilityParameter.toProbabilityParameter]

/-- Alternating factorial cumulants become nonnegative after sign correction. -/
theorem greedyBumpBernoulli_signed_factorialCumulantSucc_nonneg
    (p : StrictProbabilityParameter) (k : ℕ) :
    0 ≤ (-1 : ℝ) ^ k * greedyBumpBernoulliFactorialCumulantSucc p k := by
  rw [greedyBumpBernoulliFactorialCumulantSucc]
  have hs : 0 ≤ ((-1 : ℝ) ^ k) ^ (2 : ℕ) := sq_nonneg _
  have hr : 0 ≤ (k.factorial : ℝ) * (p : ℝ) ^ (k + 1) := by
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg p.property.1 _)
  simpa only [pow_two, mul_assoc] using mul_nonneg hs hr

/-- Each normalized cumulant contribution is exactly one negative logarithmic-series term. -/
theorem greedyBumpBernoulli_logVoidContribution_eq
    (p : StrictProbabilityParameter) (k : ℕ) :
    greedyBumpBernoulliLogVoidContribution p k =
      -((p : ℝ) ^ (k + 1) / (k + 1)) := by
  have hsign : (-1 : ℝ) ^ (k + 1) * (-1 : ℝ) ^ k = -1 := by
    rw [← pow_add]
    have hk : k + 1 + k = 2 * k + 1 := by omega
    rw [hk, pow_succ, pow_mul]
    norm_num
  simp only [greedyBumpBernoulliLogVoidContribution,
    greedyBumpBernoulliFactorialCumulantSucc, Nat.factorial_succ]
  calc
    (-1 : ℝ) ^ (k + 1) *
          ((-1 : ℝ) ^ k * (k.factorial : ℝ) * (p : ℝ) ^ (k + 1)) /
          (((k + 1) * k.factorial : ℕ) : ℝ) =
        ((-1 : ℝ) ^ (k + 1) * (-1 : ℝ) ^ k) * (k.factorial : ℝ) *
          (p : ℝ) ^ (k + 1) / (((k + 1) * k.factorial : ℕ) : ℝ) := by ring
    _ = -(k.factorial : ℝ) * (p : ℝ) ^ (k + 1) /
          (((k + 1) * k.factorial : ℕ) : ℝ) := by rw [hsign]; ring
    _ = -((p : ℝ) ^ (k + 1) / (k + 1)) := by
      field_simp [Nat.factorial_ne_zero]
      push_cast
      ring

/-- Exact all-order factorial-cumulant expansion of the hard-exclusion log void mass. -/
theorem greedyBumpBernoulli_logVoidSeries_hasSum
    (p : StrictProbabilityParameter) :
    HasSum (greedyBumpBernoulliLogVoidContribution p) (Real.log (1 - (p : ℝ))) := by
  have hpabs : |(p : ℝ)| < 1 := by
    simpa [abs_of_nonneg p.property.1] using p.property.2
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one hpabs).mul_left (-1)
  have hseries :
      HasSum (fun k : ℕ => -((p : ℝ) ^ (k + 1) / (k + 1)))
        (Real.log (1 - (p : ℝ))) := by
    simpa using h
  refine HasSum.congr_fun hseries fun k => ?_
  exact greedyBumpBernoulli_logVoidContribution_eq p k

/-- Log void probability equals the complete signed factorial-cumulant series. -/
theorem greedyBumpBernoulli_log_voidMass_eq_cumulantSeries
    (p : StrictProbabilityParameter) :
    Real.log ((greedyBumpBernoulliExclusion p.toProbabilityParameter).voidMass) =
      ∑' k : ℕ, greedyBumpBernoulliLogVoidContribution p k := by
  rw [greedyBumpBernoulli_voidMass]
  exact (greedyBumpBernoulli_logVoidSeries_hasSum p).tsum_eq.symm

end

end GaloisForLFunctions.HTGeometry
