import Mathlib

/-!
# Complex-time generative mechanics

Finite exact core of complex-time exponential generation and positive-observer Fisher
conservation.  Real exponential tilt, infinitesimal centering, and Markov information loss are
proved in one algebraic calculus.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

section ExponentialGeneration

variable {n : ℕ}

/-- Finite real exponential partition function. -/
noncomputable def finiteExpPartition (w r : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ x, w x * Real.exp (t * r x)

/-- Normalized exponential tilt. -/
noncomputable def finiteExponentialTilt (w r : Fin n → ℝ) (t : ℝ) (x : Fin n) : ℝ :=
  w x * Real.exp (t * r x) / finiteExpPartition w r t

/-- Source expectation of a score. -/
def finiteScoreMean (w r : Fin n → ℝ) : ℝ :=
  ∑ x, w x * r x

/-- Infinitesimal normalized exponential tangent. -/
def finiteExponentialTangent (w r : Fin n → ℝ) (x : Fin n) : ℝ :=
  w x * (r x - finiteScoreMean w r)

theorem finiteExpPartition_zero (w r : Fin n → ℝ) :
    finiteExpPartition w r 0 = ∑ x, w x := by
  simp [finiteExpPartition]

theorem finiteExpPartition_pos {w r : Fin n → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hsum : ∑ x, w x = 1) (t : ℝ) :
    0 < finiteExpPartition w r t := by
  have hex : ∃ x, 0 < w x := by
    by_contra hnone
    push Not at hnone
    have hall : ∀ x, w x = 0 := fun x => le_antisymm (hnone x) (hw x)
    have : ∑ x, w x = 0 := by simp [hall]
    linarith
  obtain ⟨x, hx⟩ := hex
  unfold finiteExpPartition
  exact Finset.sum_pos' (fun y _ => mul_nonneg (hw y) (Real.exp_pos _).le)
    ⟨x, Finset.mem_univ x, mul_pos hx (Real.exp_pos _)⟩

/-- Exponential tilt remains a probability vector. -/
theorem finiteExponentialTilt_sum {w r : Fin n → ℝ} (hw : ∀ x, 0 ≤ w x)
    (hsum : ∑ x, w x = 1) (t : ℝ) :
    ∑ x, finiteExponentialTilt w r t x = 1 := by
  unfold finiteExponentialTilt finiteExpPartition
  rw [← Finset.sum_div]
  exact div_self (finiteExpPartition_pos hw hsum t).ne'

theorem hasDerivAt_finiteExpPartition (w r : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (finiteExpPartition w r)
      (∑ x, w x * r x * Real.exp (t * r x)) t := by
  unfold finiteExpPartition
  refine HasDerivAt.fun_sum fun x _ => ?_
  have hinner : HasDerivAt (fun s : ℝ => s * r x) (r x) t := by
    simpa using (hasDerivAt_id t).mul_const (r x)
  have hexp := hinner.exp
  simpa [mul_assoc, mul_comm] using hexp.const_mul (w x)

/-- At time zero, normalized exponential generation has exactly the centered score tangent. -/
theorem hasDerivAt_finiteExponentialTilt_zero {w r : Fin n → ℝ}
    (hsum : ∑ x, w x = 1) (x : Fin n) :
    HasDerivAt (fun t => finiteExponentialTilt w r t x)
      (finiteExponentialTangent w r x) 0 := by
  have hnum : HasDerivAt (fun t : ℝ => w x * Real.exp (t * r x)) (w x * r x) 0 := by
    have hinner : HasDerivAt (fun t : ℝ => t * r x) (r x) 0 := by
      simpa using (hasDerivAt_id (𝕜 := ℝ) 0).mul_const (r x)
    simpa [mul_assoc, mul_comm] using hinner.exp.const_mul (w x)
  have hden := hasDerivAt_finiteExpPartition w r 0
  have hden0 : finiteExpPartition w r 0 = 1 := by
    rw [finiteExpPartition_zero, hsum]
  have hquot := hnum.div hden (by rw [hden0]; norm_num)
  have hderivEq :
      (w x * r x * finiteExpPartition w r 0 -
        w x * Real.exp (0 * r x) *
          (∑ x, w x * r x * Real.exp (0 * r x))) /
        finiteExpPartition w r 0 ^ 2 = finiteExponentialTangent w r x := by
    rw [hden0]
    simp [finiteExponentialTangent, finiteScoreMean]
    ring
  rw [hderivEq] at hquot
  change HasDerivAt
    ((fun t : ℝ => w x * Real.exp (t * r x)) / finiteExpPartition w r)
    (finiteExponentialTangent w r x) 0
  exact hquot

/-- The exponential tangent conserves total probability. -/
theorem finiteExponentialTangent_sum {w r : Fin n → ℝ} (hsum : ∑ x, w x = 1) :
    ∑ x, finiteExponentialTangent w r x = 0 := by
  unfold finiteExponentialTangent finiteScoreMean
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum]
  ring

end ExponentialGeneration

section MarkovFisher

variable {n m : ℕ}

/-- Pushforward probability under a finite Markov kernel. -/
def markovPushforward (w : Fin n → ℝ) (K : Fin n → Fin m → ℝ) (y : Fin m) : ℝ :=
  ∑ x, w x * K x y

/-- Unnormalized pushed score current. -/
def markovScoreCurrent (w r : Fin n → ℝ) (K : Fin n → Fin m → ℝ) (y : Fin m) : ℝ :=
  ∑ x, w x * K x y * r x

/-- Conditional Fisher loss. -/
def markovConditionalLoss (w r : Fin n → ℝ) (K : Fin n → Fin m → ℝ)
    (s : Fin m → ℝ) : ℝ :=
  ∑ x, ∑ y, w x * K x y * (r x - s y) ^ 2

/-- Exact law of total second moment for a Markov score transport. -/
theorem markov_secondMoment_conservation
    {w r : Fin n → ℝ} {K : Fin n → Fin m → ℝ} {s : Fin m → ℝ}
    (hrow : ∀ x, ∑ y, K x y = 1)
    (hscore : ∀ y, markovPushforward w K y * s y = markovScoreCurrent w r K y) :
    ∑ x, w x * r x ^ 2 =
      ∑ y, markovPushforward w K y * s y ^ 2 +
        markovConditionalLoss w r K s := by
  have hfirst :
      ∑ x, ∑ y, w x * K x y * r x ^ 2 = ∑ x, w x * r x ^ 2 := by
    apply Finset.sum_congr rfl
    intro x _
    calc
      ∑ y, w x * K x y * r x ^ 2 =
          (w x * r x ^ 2) * ∑ y, K x y := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _
            ring
      _ = w x * r x ^ 2 := by rw [hrow x, mul_one]
  have hcross :
      ∑ x, ∑ y, w x * K x y * r x * s y =
        ∑ y, markovPushforward w K y * s y ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [show (∑ x, w x * K x y * r x * s y) =
        markovScoreCurrent w r K y * s y by
      unfold markovScoreCurrent
      rw [Finset.sum_mul]]
    rw [← hscore y]
    ring
  have hlast :
      ∑ x, ∑ y, w x * K x y * s y ^ 2 =
        ∑ y, markovPushforward w K y * s y ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [show (∑ x, w x * K x y * s y ^ 2) =
        markovPushforward w K y * s y ^ 2 by
      unfold markovPushforward
      rw [Finset.sum_mul]]
  unfold markovConditionalLoss
  rw [show (∑ x, ∑ y, w x * K x y * (r x - s y) ^ 2) =
      (∑ x, ∑ y, w x * K x y * r x ^ 2) -
      2 * (∑ x, ∑ y, w x * K x y * r x * s y) +
      (∑ x, ∑ y, w x * K x y * s y ^ 2) by
    calc
      (∑ x, ∑ y, w x * K x y * (r x - s y) ^ 2) =
          ∑ x, ∑ y, (w x * K x y * r x ^ 2 -
            2 * (w x * K x y * r x * s y) + w x * K x y * s y ^ 2) := by
              apply Finset.sum_congr rfl
              intro x _
              apply Finset.sum_congr rfl
              intro y _
              ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]]
  rw [hfirst, hcross, hlast]
  ring

/-- Positive Markov observation cannot increase Fisher second moment; the deficit is exactly the
conditional loss. -/
theorem markov_secondMoment_dataProcessing
    {w r : Fin n → ℝ} {K : Fin n → Fin m → ℝ} {s : Fin m → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hK : ∀ x y, 0 ≤ K x y)
    (hrow : ∀ x, ∑ y, K x y = 1)
    (hscore : ∀ y, markovPushforward w K y * s y = markovScoreCurrent w r K y) :
    ∑ y, markovPushforward w K y * s y ^ 2 ≤ ∑ x, w x * r x ^ 2 := by
  rw [markov_secondMoment_conservation hrow hscore]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun x _ =>
    Finset.sum_nonneg fun y _ => mul_nonneg (mul_nonneg (hw x) (hK x y)) (sq_nonneg _))

/-- A strict receiver amplification rules out every positive Markov score realization with the
declared source and receiver second moments. -/
theorem no_positiveMarkov_realization_of_strictAmplification
    {w r : Fin n → ℝ} {K : Fin n → Fin m → ℝ} {s : Fin m → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hK : ∀ x y, 0 ≤ K x y)
    (hrow : ∀ x, ∑ y, K x y = 1)
    (hscore : ∀ y, markovPushforward w K y * s y = markovScoreCurrent w r K y)
    (hamplifies : ∑ x, w x * r x ^ 2 <
      ∑ y, markovPushforward w K y * s y ^ 2) :
    False :=
  (not_lt_of_ge (markov_secondMoment_dataProcessing hw hK hrow hscore)) hamplifies

/-- The Fisher deficit is zero exactly when every positive kernel edge preserves the score. -/
theorem markovConditionalLoss_eq_zero_iff
    {w r : Fin n → ℝ} {K : Fin n → Fin m → ℝ} {s : Fin m → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hK : ∀ x y, 0 ≤ K x y) :
    markovConditionalLoss w r K s = 0 ↔
      ∀ x y, 0 < w x * K x y → r x = s y := by
  unfold markovConditionalLoss
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · constructor
    · intro hall x y hpos
      have hxy := hall x (Finset.mem_univ x)
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun y _ =>
        mul_nonneg (mul_nonneg (hw x) (hK x y)) (sq_nonneg _))] at hxy
      have hterm := hxy y (Finset.mem_univ y)
      have hcoeff : w x * K x y ≠ 0 := ne_of_gt hpos
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hterm).resolve_left hcoeff))
    · intro hedge x _
      apply Finset.sum_eq_zero
      intro y _
      by_cases hpos : 0 < w x * K x y
      · simp [hedge x y hpos]
      · have hzero : w x * K x y = 0 :=
          le_antisymm (le_of_not_gt hpos) (mul_nonneg (hw x) (hK x y))
        rw [hzero, zero_mul]
  · intro x _
    exact Finset.sum_nonneg fun y _ =>
      mul_nonneg (mul_nonneg (hw x) (hK x y)) (sq_nonneg _)

end MarkovFisher

end GaloisForLFunctions.HTGeometry
