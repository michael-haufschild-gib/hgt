import GaloisForLFunctions.HTGeometry.GreedyBumpFactorialCumulants
import GaloisForLFunctions.RHTower.SquarefreeCriticalNormalCone

/-!
# Factorial cumulants of squarefree binary digits

The binary-digit factorization used by the squarefree critical normal cone has Bernoulli success
probability `a^(2^j)/(1+a^(2^j))`.  This module reads every such digit as a hard-exclusion point
count and applies the factorial-cumulant/void laws of arXiv:2609.03581.  Prime positivity makes
the construction unconditional for every drift and digit depth.
-/

open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Odds of the `j`-th binary valuation digit at a prime. -/
def radialBinaryDigitOdds (c : ℝ) (p : Nat.Primes) (j : ℕ) : ℝ :=
  radialNome c p ^ (2 ^ j)

/-- The `j`-th radial binary digit's Bernoulli success probability. -/
def radialBinaryDigitProbability (c : ℝ) (p : Nat.Primes) (j : ℕ) :
    ProbabilityParameter := by
  let a := radialBinaryDigitOdds c p j
  have ha : 0 < a := by
    exact pow_pos (radialNome_pos p.property.two_le) _
  exact ⟨a / (1 + a),
    ⟨div_nonneg ha.le (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩⟩

/-- Every squarefree binary digit is a one-point hard-exclusion count law. -/
def greedyBumpRadialBinaryDigitCount (c : ℝ) (p : Nat.Primes) (j : ℕ) :
    FinitePointCountLaw Bool :=
  greedyBumpBernoulliExclusion (radialBinaryDigitProbability c p j)

/-- First factorial cumulant equals the binary digit's normalized odds. -/
theorem greedyBumpRadialBinaryDigit_factorialCumulantOne
    (c : ℝ) (p : Nat.Primes) (j : ℕ) :
    (greedyBumpRadialBinaryDigitCount c p j).factorialCumulantOne =
      radialBinaryDigitOdds c p j / (1 + radialBinaryDigitOdds c p j) := by
  exact greedyBumpBernoulli_factorialCumulantOne
    (radialBinaryDigitProbability c p j)

/-- Hard exclusion forces a negative second factorial cumulant at every prime and digit depth. -/
theorem greedyBumpRadialBinaryDigit_factorialCumulantTwo
    (c : ℝ) (p : Nat.Primes) (j : ℕ) :
    (greedyBumpRadialBinaryDigitCount c p j).factorialCumulantTwo =
      -(radialBinaryDigitOdds c p j / (1 + radialBinaryDigitOdds c p j)) ^ 2 := by
  exact greedyBumpBernoulli_factorialCumulantTwo
    (radialBinaryDigitProbability c p j)

/-- Third factorial cumulant is twice the cubed digit probability. -/
theorem greedyBumpRadialBinaryDigit_factorialCumulantThree
    (c : ℝ) (p : Nat.Primes) (j : ℕ) :
    (greedyBumpRadialBinaryDigitCount c p j).factorialCumulantThree =
      2 * (radialBinaryDigitOdds c p j / (1 + radialBinaryDigitOdds c p j)) ^ 3 := by
  exact greedyBumpBernoulli_factorialCumulantThree
    (radialBinaryDigitProbability c p j)

/-- Void probability is the reciprocal normalization of the digit odds. -/
theorem greedyBumpRadialBinaryDigit_voidMass
    (c : ℝ) (p : Nat.Primes) (j : ℕ) :
    (greedyBumpRadialBinaryDigitCount c p j).voidMass =
      1 / (1 + radialBinaryDigitOdds c p j) := by
  change (greedyBumpBernoulliExclusion
    (radialBinaryDigitProbability c p j)).voidMass = _
  rw [greedyBumpBernoulli_voidMass]
  change 1 - radialBinaryDigitOdds c p j / (1 + radialBinaryDigitOdds c p j) = _
  have ha : 0 < radialBinaryDigitOdds c p j :=
    pow_pos (radialNome_pos p.property.two_le) _
  field_simp [ne_of_gt (by linarith : 0 < 1 + radialBinaryDigitOdds c p j)]
  ring

/-- The factorial-cumulant signs alternate through order three for every radial digit. -/
theorem greedyBumpRadialBinaryDigit_cumulantSigns
    (c : ℝ) (p : Nat.Primes) (j : ℕ) :
    0 < (greedyBumpRadialBinaryDigitCount c p j).factorialCumulantOne ∧
    (greedyBumpRadialBinaryDigitCount c p j).factorialCumulantTwo < 0 ∧
    0 < (greedyBumpRadialBinaryDigitCount c p j).factorialCumulantThree := by
  rw [greedyBumpRadialBinaryDigit_factorialCumulantOne,
    greedyBumpRadialBinaryDigit_factorialCumulantTwo,
    greedyBumpRadialBinaryDigit_factorialCumulantThree]
  have ha : 0 < radialBinaryDigitOdds c p j :=
    pow_pos (radialNome_pos p.property.two_le) _
  have hprob : 0 < radialBinaryDigitOdds c p j /
      (1 + radialBinaryDigitOdds c p j) := div_pos ha (by linarith)
  exact ⟨hprob, neg_neg_iff_pos.mpr (sq_pos_of_pos hprob),
    mul_pos (by norm_num) (pow_pos hprob _)⟩

/-- The parity digit (`j=0`) has success odds exactly equal to the radial nome. -/
theorem greedyBumpRadialParityDigit_probability
    (c : ℝ) (p : Nat.Primes) :
    (radialBinaryDigitProbability c p 0 : ℝ) =
      radialNome c p / (1 + radialNome c p) := by
  simp [radialBinaryDigitProbability, radialBinaryDigitOdds]

/-- The corpus parity-digit affinity is exactly hard-exclusion Hellinger affinity. -/
theorem greedyBumpRadialParityDigit_hellingerAffinity
    (c d : ℝ) (p : Nat.Primes) :
    greedyBumpBernoulliHellingerAffinity
        (radialBinaryDigitProbability c p 0)
        (radialBinaryDigitProbability d p 0) =
      bitHellingerAffinity (radialNome c p) (radialNome d p) 0 := by
  simp only [greedyBumpBernoulliHellingerAffinity,
    radialBinaryDigitProbability, radialBinaryDigitOdds, pow_zero, pow_one]
  let a := radialNome c p
  let b := radialNome d p
  have ha : 0 < a := radialNome_pos p.property.two_le
  have hb : 0 < b := radialNome_pos p.property.two_le
  change Real.sqrt ((1 - a / (1 + a)) * (1 - b / (1 + b))) +
      Real.sqrt ((a / (1 + a)) * (b / (1 + b))) =
    bitHellingerAffinity a b 0
  have hA : 0 < 1 + a := by linarith
  have hB : 0 < 1 + b := by linarith
  have honeA : 1 - a / (1 + a) = 1 / (1 + a) := by
    field_simp [ne_of_gt hA]
    ring
  have honeB : 1 - b / (1 + b) = 1 / (1 + b) := by
    field_simp [ne_of_gt hB]
    ring
  have hfirst : (1 / (1 + a)) * (1 / (1 + b)) =
      1 / ((1 + a) * (1 + b)) := by
    field_simp [ne_of_gt hA, ne_of_gt hB]
  have hsecond : (a / (1 + a)) * (b / (1 + b)) =
      (a * b) / ((1 + a) * (1 + b)) := by
    field_simp [ne_of_gt hA, ne_of_gt hB]
  rw [honeA, honeB, hfirst, hsecond,
    Real.sqrt_div (by positivity : (0 : ℝ) ≤ 1),
    Real.sqrt_div (mul_nonneg ha.le hb.le)]
  simp only [Real.sqrt_one, one_div]
  rw [bitHellingerAffinity]
  norm_num
  ring

end

end RHTower
