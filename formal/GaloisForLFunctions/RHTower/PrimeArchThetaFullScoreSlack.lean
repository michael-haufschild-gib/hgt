import GaloisForLFunctions.RHTower.PrimeArchThetaScoreMomentDefect

/-!
# Strict complete-source theta score slack

The actual theta source and its summable derivative series retain every atom's
Born--Witten score defect.  The second atom is strictly positive everywhere on
the half-line, giving a continuous strict surplus above the prescribed first-atom
square without a spectral or nonvanishing premise.
-/

open Real Set
open scoped BigOperators
namespace RHTower
noncomputable section

/-- Atom contribution to the complete source's quadratic score. -/
def thetaCuspSourceScoreTerm (n : ℕ) (x : ℝ) : ℝ :=
  (1 - 303 * x ^ 2) * thetaCuspSourceTerm x n -
    16 * x * deriv (fun y => thetaCuspSourceTerm y n) x

/-- Literal surplus over the prescribed first-atom score floor. -/
def thetaCuspFullScoreSlack (x : ℝ) : ℝ :=
  (1 - 303 * x ^ 2) * thetaCuspFullSource x -
    16 * x * deriv thetaCuspFullSource x -
    Real.pi * thetaCuspBornWittenAmplitude 1 x ^ 2 * (x - 1) ^ 2

/-- The derivative of the complete source is the summable derivative series. -/
theorem deriv_thetaCuspFullSource_eq_tsum_sourceTerm (x : ℝ) :
    deriv thetaCuspFullSource x =
      ∑' n : ℕ, deriv (fun y => thetaCuspSourceTerm y n) x := by
  have h := congrFun (iteratedDeriv_thetaCuspFullSource 1) x
  simpa only [iteratedDeriv_one, thetaCuspFullDerivative] using h

/-- Actual source and derivative summability justify the complete atom score sum. -/
theorem summable_thetaCuspSourceScoreTerm (x : ℝ) :
    Summable (fun n : ℕ => thetaCuspSourceScoreTerm n x) := by
  have hd : Summable (fun n : ℕ => deriv (fun y => thetaCuspSourceTerm y n) x) := by
    simpa only [iteratedDeriv_one] using summable_iteratedDeriv_thetaCuspSourceTerm 1 x
  exact ((summable_thetaCuspSourceTerm x).mul_left (1 - 303 * x ^ 2)).sub
    (hd.mul_left (16 * x))

/-- Exact complete-source score decomposition, including the zero atom. -/
theorem thetaCuspFullScore_eq_tsum_sourceScoreTerm (x : ℝ) :
    (1 - 303 * x ^ 2) * thetaCuspFullSource x -
      16 * x * deriv thetaCuspFullSource x =
      ∑' n : ℕ, thetaCuspSourceScoreTerm n x := by
  have hd : Summable (fun n : ℕ => deriv (fun y => thetaCuspSourceTerm y n) x) := by
    simpa only [iteratedDeriv_one] using summable_iteratedDeriv_thetaCuspSourceTerm 1 x
  rw [deriv_thetaCuspFullSource_eq_tsum_sourceTerm, thetaCuspFullSource]
  symm
  exact (((summable_thetaCuspSourceTerm x).mul_left (1 - 303 * x ^ 2)).tsum_sub
    (hd.mul_left (16 * x))).trans (by rw [tsum_mul_left, tsum_mul_left])

/-- Each atom score is its exact Born--Witten defect, also at the endpoint `x=0`. -/
theorem thetaCuspSourceScoreTerm_eq_bornWittenDefect (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspSourceScoreTerm n x =
      Real.pi * (1 + 32 * x * thetaCuspBornWittenSuperpotential n x - 303 * x ^ 2) *
        thetaCuspBornWittenAmplitude n x ^ 2 := by
  cases n with
  | zero =>
      simp [thetaCuspSourceScoreTerm, thetaCuspSourceTerm, thetaCuspSeed,
        thetaCuspBornWittenAmplitude, thetaCuspMorseGroundState, thetaCuspMorseZeroMode]
  | succ n =>
      have hn : 0 < n + 1 := by omega
      by_cases hx0 : x = 0
      · subst x
        simpa [thetaCuspSourceScoreTerm] using
          thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq
            (x := (0 : ℝ)) hn (by norm_num)
      · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
        rw [thetaCuspSourceScoreTerm,
          (hasDerivAt_thetaCuspSourceTerm_eq_bornWittenScore hn hxpos).deriv,
          thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq hn hx]
        ring

/-- The complete-source score is a literal sum of exact atom defects. -/
theorem thetaCuspFullScore_eq_tsum_bornWittenDefect {x : ℝ} (hx : 0 ≤ x) :
    (1 - 303 * x ^ 2) * thetaCuspFullSource x -
      16 * x * deriv thetaCuspFullSource x =
      ∑' n : ℕ, Real.pi *
        (1 + 32 * x * thetaCuspBornWittenSuperpotential n x - 303 * x ^ 2) *
        thetaCuspBornWittenAmplitude n x ^ 2 := by
  rw [thetaCuspFullScore_eq_tsum_sourceScoreTerm]
  exact tsum_congr fun n => thetaCuspSourceScoreTerm_eq_bornWittenDefect n hx

/-- Every atom after the first has a strictly positive score defect on the complete half-line. -/
theorem thetaCuspBornWitten_scoreDefect_pos_of_one_lt {n : ℕ} (hn : 1 < n)
    {x : ℝ} (hx : 0 ≤ x) :
    0 < 1 + 32 * x * thetaCuspBornWittenSuperpotential n x - 303 * x ^ 2 := by
  by_cases hx0 : x = 0
  · subst x
    norm_num
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hfirst := thetaCuspBornWitten_scoreDefect_ge_square (by norm_num : 0 < 1) hx
    have horder := thetaCuspBornWittenSuperpotential_strictMono_nat
      (by norm_num : 0 < 1) hn hx
    have hmul := mul_lt_mul_of_pos_left horder (show 0 < 32 * x by positivity)
    nlinarith [sq_nonneg (x - 1)]

/-- Every atom score is nonnegative on the complete half-line. -/
theorem thetaCuspSourceScoreTerm_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ thetaCuspSourceScoreTerm n x := by
  cases n with
  | zero =>
      simp [thetaCuspSourceScoreTerm, thetaCuspSourceTerm, thetaCuspSeed]
  | succ n =>
      rw [thetaCuspSourceScoreTerm_eq_bornWittenDefect _ hx]
      have hdef := thetaCuspBornWitten_scoreDefect_ge_square (by omega : 0 < n + 1) hx
      exact mul_nonneg (mul_nonneg Real.pi_pos.le
        (le_trans (sq_nonneg _) hdef)) (sq_nonneg _)

/-- The second atom supplies a strict positive contribution everywhere, including `x=1`. -/
theorem thetaCuspSecondAtomScoreTerm_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspSourceScoreTerm 2 x := by
  rw [thetaCuspSourceScoreTerm_eq_bornWittenDefect _ hx]
  exact mul_pos (mul_pos Real.pi_pos
    (thetaCuspBornWitten_scoreDefect_pos_of_one_lt (by norm_num) hx))
    (sq_pos_of_pos (thetaCuspBornWittenAmplitude_pos (by norm_num) hx))

/-- The literal slack retains the complete second-atom score as a lower bound. -/
theorem thetaCuspFullScoreSlack_ge_secondAtomScore {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspSourceScoreTerm 2 x ≤ thetaCuspFullScoreSlack x := by
  have hfirst : Real.pi * thetaCuspBornWittenAmplitude 1 x ^ 2 * (x - 1) ^ 2 ≤
      thetaCuspSourceScoreTerm 1 x := by
    rw [thetaCuspSourceScoreTerm_eq_bornWittenDefect _ hx]
    have h := mul_le_mul_of_nonneg_left
      (thetaCuspBornWitten_scoreDefect_ge_square (by norm_num : 0 < 1) hx)
      (show 0 ≤ Real.pi * thetaCuspBornWittenAmplitude 1 x ^ 2 by positivity)
    nlinarith
  have hsum := (summable_thetaCuspSourceScoreTerm x).sum_le_tsum
    ({1, 2} : Finset ℕ) (fun n _ => thetaCuspSourceScoreTerm_nonneg n hx)
  have htwo : thetaCuspSourceScoreTerm 1 x + thetaCuspSourceScoreTerm 2 x ≤
      ∑' n : ℕ, thetaCuspSourceScoreTerm n x := by
    simpa using hsum
  unfold thetaCuspFullScoreSlack
  rw [thetaCuspFullScore_eq_tsum_sourceScoreTerm]
  linarith

/-- The full score strictly dominates the prescribed first-atom square. -/
theorem thetaCuspFullScore_gt_firstAtomSquare {x : ℝ} (hx : 0 ≤ x) :
    Real.pi * thetaCuspBornWittenAmplitude 1 x ^ 2 * (x - 1) ^ 2 <
      (1 - 303 * x ^ 2) * thetaCuspFullSource x -
        16 * x * deriv thetaCuspFullSource x := by
  have h := thetaCuspFullScoreSlack_ge_secondAtomScore hx
  unfold thetaCuspFullScoreSlack at h
  linarith [thetaCuspSecondAtomScoreTerm_pos hx]

/-- The actual complete-source score surplus is continuous on the entire real line. -/
theorem continuous_thetaCuspFullScoreSlack : Continuous thetaCuspFullScoreSlack := by
  have hk := contDiff_thetaCuspFullSource.continuous
  have hdk : Continuous (deriv thetaCuspFullSource) :=
    contDiff_thetaCuspFullSource.continuous_deriv (by simp)
  have hamp : Continuous (thetaCuspBornWittenAmplitude 1) := by
    unfold thetaCuspBornWittenAmplitude thetaCuspBornWittenWeight
      thetaCuspMorseGroundState thetaCuspMorseZeroMode
      thetaCuspMorseSuperpotential thetaCuspMorseScale
    fun_prop
  unfold thetaCuspFullScoreSlack
  fun_prop

/-- Strict complete-source slack without a nonvanishing, RH, or sign premise. -/
theorem thetaCuspFullScoreSlack_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspFullScoreSlack x := by
  unfold thetaCuspFullScoreSlack
  linarith [thetaCuspFullScore_gt_firstAtomSquare hx]

end
end RHTower
