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
  law.factorialMoment 2 - law.factorialMoment 1 ^ 2

/-- Third factorial cumulant. -/
def FinitePointCountLaw.factorialCumulantThree {Ω : Type*} [Fintype Ω]
    (law : FinitePointCountLaw Ω) : ℝ :=
  law.factorialMoment 3 -
    3 * law.factorialMoment 2 * law.factorialMoment 1 +
    2 * law.factorialMoment 1 ^ 3

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

/-- Hard exclusion forces negative second factorial cumulant `-p^2`. -/
theorem greedyBumpBernoulli_factorialCumulantTwo (p : ProbabilityParameter) :
    (greedyBumpBernoulliExclusion p).factorialCumulantTwo = -(p : ℝ) ^ 2 := by
  simp [FinitePointCountLaw.factorialCumulantTwo,
    FinitePointCountLaw.factorialMoment, greedyBumpBernoulliExclusion]

/-- Hard exclusion has third factorial cumulant `2p^3`. -/
theorem greedyBumpBernoulli_factorialCumulantThree (p : ProbabilityParameter) :
    (greedyBumpBernoulliExclusion p).factorialCumulantThree = 2 * (p : ℝ) ^ 3 := by
  simp [FinitePointCountLaw.factorialCumulantThree,
    FinitePointCountLaw.factorialMoment, greedyBumpBernoulliExclusion]

/-- Hard exclusion void mass is exactly `1-p`. -/
theorem greedyBumpBernoulli_voidMass (p : ProbabilityParameter) :
    (greedyBumpBernoulliExclusion p).voidMass = 1 - (p : ℝ) := by
  simp [FinitePointCountLaw.voidMass, greedyBumpBernoulliExclusion]

end

end GaloisForLFunctions.HTGeometry

