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

section FiniteResponse

variable {n : ℕ}

/-- Mean score under the finite exponential tilt at time `t`. -/
noncomputable def finiteTiltScoreMean (w r : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ x, finiteExponentialTilt w r t x * r x

/-- Expectation of an observable under the finite exponential tilt. -/
noncomputable def finiteTiltExpectation (w r f : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ x, finiteExponentialTilt w r t x * f x

/-- Covariance of an observable with the score under the finite exponential tilt. -/
noncomputable def finiteTiltCovariance (w r f : Fin n → ℝ) (t : ℝ) : ℝ :=
  (∑ x, finiteExponentialTilt w r t x * f x * r x) -
    finiteTiltExpectation w r f t * finiteTiltScoreMean w r t

theorem finiteTiltCovariance_eq_centered {w r f : Fin n → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1) (t : ℝ) :
    finiteTiltCovariance w r f t =
      ∑ x, finiteExponentialTilt w r t x *
        (f x - finiteTiltExpectation w r f t) *
        (r x - finiteTiltScoreMean w r t) := by
  have hmass := finiteExponentialTilt_sum (r := r) hw hsum t
  unfold finiteTiltCovariance finiteTiltExpectation finiteTiltScoreMean
  rw [show (∑ x, finiteExponentialTilt w r t x *
      (f x - ∑ y, finiteExponentialTilt w r t y * f y) *
      (r x - ∑ y, finiteExponentialTilt w r t y * r y)) =
    (∑ x, finiteExponentialTilt w r t x * f x * r x) -
      (∑ y, finiteExponentialTilt w r t y * r y) *
        (∑ x, finiteExponentialTilt w r t x * f x) -
      (∑ y, finiteExponentialTilt w r t y * f y) *
        (∑ x, finiteExponentialTilt w r t x * r x) +
      (∑ y, finiteExponentialTilt w r t y * f y) *
        (∑ y, finiteExponentialTilt w r t y * r y) *
        (∑ x, finiteExponentialTilt w r t x) by
    calc
      _ = ∑ x, (finiteExponentialTilt w r t x * f x * r x -
          (∑ y, finiteExponentialTilt w r t y * r y) *
            (finiteExponentialTilt w r t x * f x) -
          (∑ y, finiteExponentialTilt w r t y * f y) *
            (finiteExponentialTilt w r t x * r x) +
          ((∑ y, finiteExponentialTilt w r t y * f y) *
            (∑ y, finiteExponentialTilt w r t y * r y)) *
            finiteExponentialTilt w r t x) := by
              apply Finset.sum_congr rfl
              intro x _
              ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
        simp only [← Finset.mul_sum]]
  rw [hmass]
  ring

/-- At every admitted time, the normalized exponential tilt differentiates by its centered score. -/
theorem hasDerivAt_finiteExponentialTilt {w r : Fin n → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1) (t : ℝ) (x : Fin n) :
    HasDerivAt (fun s => finiteExponentialTilt w r s x)
      (finiteExponentialTilt w r t x * (r x - finiteTiltScoreMean w r t)) t := by
  have hnum : HasDerivAt (fun s : ℝ => w x * Real.exp (s * r x))
      (w x * r x * Real.exp (t * r x)) t := by
    have hinner : HasDerivAt (fun s : ℝ => s * r x) (r x) t := by
      simpa using (hasDerivAt_id t).mul_const (r x)
    simpa [mul_assoc, mul_comm] using hinner.exp.const_mul (w x)
  have hden := hasDerivAt_finiteExpPartition w r t
  have hZ : finiteExpPartition w r t ≠ 0 := (finiteExpPartition_pos hw hsum t).ne'
  have hquot := hnum.div hden hZ
  have hmean : finiteTiltScoreMean w r t =
      (∑ x, w x * r x * Real.exp (t * r x)) / finiteExpPartition w r t := by
    unfold finiteTiltScoreMean finiteExponentialTilt
    calc
      ∑ x, w x * Real.exp (t * r x) / finiteExpPartition w r t * r x =
          ∑ x, (w x * r x * Real.exp (t * r x)) / finiteExpPartition w r t := by
            apply Finset.sum_congr rfl
            intro y _
            ring
      _ = _ := (Finset.sum_div Finset.univ
        (fun x => w x * r x * Real.exp (t * r x)) (finiteExpPartition w r t)).symm
  have hderivEq :
      (w x * r x * Real.exp (t * r x) * finiteExpPartition w r t -
        w x * Real.exp (t * r x) *
          (∑ x, w x * r x * Real.exp (t * r x))) /
          finiteExpPartition w r t ^ 2 =
        finiteExponentialTilt w r t x * (r x - finiteTiltScoreMean w r t) := by
    rw [hmean]
    unfold finiteExponentialTilt
    field_simp [hZ]
  rw [hderivEq] at hquot
  change HasDerivAt
    ((fun s : ℝ => w x * Real.exp (s * r x)) / finiteExpPartition w r)
    _ t
  exact hquot

/-- Observable response along a normalized exponential family is exactly covariance. -/
theorem hasDerivAt_finiteTiltExpectation {w r f : Fin n → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1) (t : ℝ) :
    HasDerivAt (finiteTiltExpectation w r f)
      (finiteTiltCovariance w r f t) t := by
  have hterm (x : Fin n) :=
    (hasDerivAt_finiteExponentialTilt (r := r) hw hsum t x).mul_const (f x)
  have hsumderiv := HasDerivAt.fun_sum (u := Finset.univ) (fun x _ => hterm x)
  have hderivEq :
      (∑ x, finiteExponentialTilt w r t x *
        (r x - finiteTiltScoreMean w r t) * f x) =
        finiteTiltCovariance w r f t := by
    unfold finiteTiltCovariance finiteTiltExpectation finiteTiltScoreMean
    rw [show (∑ x, finiteExponentialTilt w r t x *
      (r x - ∑ y, finiteExponentialTilt w r t y * r y) * f x) =
        (∑ x, finiteExponentialTilt w r t x * f x * r x) -
          (∑ y, finiteExponentialTilt w r t y * r y) *
            (∑ x, finiteExponentialTilt w r t x * f x) by
      calc
        _ = ∑ x, (finiteExponentialTilt w r t x * f x * r x -
          (∑ y, finiteExponentialTilt w r t y * r y) *
            (finiteExponentialTilt w r t x * f x)) := by
              apply Finset.sum_congr rfl
              intro x _
              ring
        _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]]
    ring
  rw [hderivEq] at hsumderiv
  change HasDerivAt (fun s => ∑ x, finiteExponentialTilt w r s x * f x) _ t
  exact hsumderiv

end FiniteResponse

section FiniteComplexGeneration

variable {n : ℕ}

/-- Finite complex-time partition germ. -/
noncomputable def finiteComplexPartition (w r : Fin n → ℝ) (z : ℂ) : ℂ :=
  ∑ x, (w x : ℂ) * Complex.exp ((r x : ℂ) * z)

/-- Imaginary-time characteristic reporter of the score law. -/
noncomputable def finitePhaseReporter (w r : Fin n → ℝ) (s : ℝ) : ℂ :=
  ∑ x, (w x : ℂ) * Complex.exp (Complex.I * (s * r x))

theorem finiteComplexPartition_ofReal (w r : Fin n → ℝ) (t : ℝ) :
    finiteComplexPartition w r (t : ℂ) = (finiteExpPartition w r t : ℂ) := by
  rw [finiteComplexPartition, finiteExpPartition, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  exact_mod_cast (mul_comm (r x) t)

theorem finiteComplexPartition_imaginary (w r : Fin n → ℝ) (s : ℝ) :
    finiteComplexPartition w r ((s : ℂ) * Complex.I) = finitePhaseReporter w r s := by
  unfold finiteComplexPartition finitePhaseReporter
  apply Finset.sum_congr rfl
  intro x _
  congr 2
  ring

/-- Every complex derivative is the corresponding exponential moment. -/
theorem iteratedDeriv_finiteComplexPartition (w r : Fin n → ℝ) (k : ℕ) (z : ℂ) :
    iteratedDeriv k (finiteComplexPartition w r) z =
      ∑ x, (w x : ℂ) * (r x : ℂ) ^ k * Complex.exp ((r x : ℂ) * z) := by
  change iteratedDeriv k
      (fun z : ℂ => ∑ x, (w x : ℂ) * Complex.exp ((r x : ℂ) * z)) z = _
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro x _
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_cexp_const_mul]
    ring
  · intro x _
    fun_prop

theorem iteratedDeriv_finiteComplexPartition_zero (w r : Fin n → ℝ) (k : ℕ) :
    iteratedDeriv k (finiteComplexPartition w r) 0 =
      ∑ x, (w x : ℂ) * (r x : ℂ) ^ k := by
  simpa using iteratedDeriv_finiteComplexPartition w r k 0

end FiniteComplexGeneration

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

/-- A Markov score current preserves the score mean. -/
theorem markov_scoreMean_conservation
    {w r : Fin n → ℝ} {K : Fin n → Fin m → ℝ} {s : Fin m → ℝ}
    (hrow : ∀ x, ∑ y, K x y = 1)
    (hscore : ∀ y, markovPushforward w K y * s y = markovScoreCurrent w r K y) :
    ∑ y, markovPushforward w K y * s y = ∑ x, w x * r x := by
  rw [Finset.sum_congr rfl (fun y _ => hscore y)]
  unfold markovScoreCurrent
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  calc
    ∑ y, w x * K x y * r x = (w x * r x) * ∑ y, K x y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = w x * r x := by rw [hrow x, mul_one]

theorem markov_scoreMean_zero
    {w r : Fin n → ℝ} {K : Fin n → Fin m → ℝ} {s : Fin m → ℝ}
    (hrow : ∀ x, ∑ y, K x y = 1)
    (hscore : ∀ y, markovPushforward w K y * s y = markovScoreCurrent w r K y)
    (hcentered : ∑ x, w x * r x = 0) :
    ∑ y, markovPushforward w K y * s y = 0 := by
  rw [markov_scoreMean_conservation hrow hscore, hcentered]

end MarkovFisher

section SummablyAdmittedMarkovFisher

variable {ι κ : Type*}

/-- Pushforward weight under a summably admitted Markov kernel. -/
noncomputable def countableMarkovPushforward
    (w : ι → ℝ) (K : ι → κ → ℝ) (y : κ) : ℝ :=
  ∑' x, w x * K x y

/-- Unnormalized pushed score current for a summably admitted Markov kernel. -/
noncomputable def countableMarkovScoreCurrent
    (w r : ι → ℝ) (K : ι → κ → ℝ) (y : κ) : ℝ :=
  ∑' x, w x * K x y * r x

/-- Conditional Fisher loss for a summably admitted Markov kernel. -/
noncomputable def countableMarkovConditionalLoss
    (w r : ι → ℝ) (K : ι → κ → ℝ) (s : κ → ℝ) : ℝ :=
  ∑' p : ι × κ, w p.1 * K p.1 p.2 * (r p.1 - s p.2) ^ 2

/-- Summably admitted Markov transport preserves the score mean. -/
theorem countableMarkov_scoreMean_conservation
    {w r : ι → ℝ} {K : ι → κ → ℝ} {s : κ → ℝ}
    (hrow : ∀ x, HasSum (K x) 1)
    (hscore : ∀ y, countableMarkovPushforward w K y * s y =
      countableMarkovScoreCurrent w r K y)
    (hjoint : Summable (fun p : ι × κ => w p.1 * K p.1 p.2 * r p.1)) :
    ∑' y, countableMarkovPushforward w K y * s y = ∑' x, w x * r x := by
  calc
    ∑' y, countableMarkovPushforward w K y * s y =
        ∑' y, countableMarkovScoreCurrent w r K y :=
      tsum_congr hscore
    _ = ∑' y, ∑' x, w x * K x y * r x := by
      rfl
    _ = ∑' x, ∑' y, w x * K x y * r x := hjoint.tsum_comm
    _ = ∑' x, w x * r x := by
      apply tsum_congr
      intro x
      have hs := (hrow x).mul_left (w x * r x)
      calc
        ∑' y, w x * K x y * r x = ∑' y, (w x * r x) * K x y := by
          apply tsum_congr
          intro y
          ring
        _ = w x * r x := by simpa using hs.tsum_eq

theorem countableMarkov_scoreMean_zero
    {w r : ι → ℝ} {K : ι → κ → ℝ} {s : κ → ℝ}
    (hrow : ∀ x, HasSum (K x) 1)
    (hscore : ∀ y, countableMarkovPushforward w K y * s y =
      countableMarkovScoreCurrent w r K y)
    (hjoint : Summable (fun p : ι × κ => w p.1 * K p.1 p.2 * r p.1))
    (hcentered : ∑' x, w x * r x = 0) :
    ∑' y, countableMarkovPushforward w K y * s y = 0 := by
  rw [countableMarkov_scoreMean_conservation hrow hscore hjoint, hcentered]

theorem summable_countableMarkovConditionalLoss
    {w r : ι → ℝ} {K : ι → κ → ℝ} {s : κ → ℝ}
    (hfirst : Summable (fun p : ι × κ => w p.1 * K p.1 p.2 * r p.1 ^ 2))
    (hcross : Summable (fun p : ι × κ =>
      w p.1 * K p.1 p.2 * r p.1 * s p.2))
    (hlast : Summable (fun p : ι × κ => w p.1 * K p.1 p.2 * s p.2 ^ 2)) :
    Summable (fun p : ι × κ =>
      w p.1 * K p.1 p.2 * (r p.1 - s p.2) ^ 2) := by
  refine ((hfirst.sub (hcross.mul_left 2)).add hlast).congr ?_
  intro p
  ring

/-- Zero countable Fisher loss is exactly score preservation on every positive kernel edge. -/
theorem countableMarkovConditionalLoss_eq_zero_iff
    {w r : ι → ℝ} {K : ι → κ → ℝ} {s : κ → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hK : ∀ x y, 0 ≤ K x y)
    (hLoss : Summable (fun p : ι × κ =>
      w p.1 * K p.1 p.2 * (r p.1 - s p.2) ^ 2)) :
    countableMarkovConditionalLoss w r K s = 0 ↔
      ∀ x y, 0 < w x * K x y → r x = s y := by
  rw [countableMarkovConditionalLoss]
  constructor
  · intro hzero x y hpos
    have hnonneg : ∀ p : ι × κ,
        0 ≤ w p.1 * K p.1 p.2 * (r p.1 - s p.2) ^ 2 := fun p =>
      mul_nonneg (mul_nonneg (hw p.1) (hK p.1 p.2)) (sq_nonneg _)
    have hle := hLoss.le_tsum (x, y) (fun p _ => hnonneg p)
    rw [hzero] at hle
    have hterm : w x * K x y * (r x - s y) ^ 2 = 0 :=
      le_antisymm hle (hnonneg (x, y))
    have hcoeff : w x * K x y ≠ 0 := ne_of_gt hpos
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hterm).resolve_left hcoeff))
  · intro hedge
    calc
      ∑' p : ι × κ, w p.1 * K p.1 p.2 * (r p.1 - s p.2) ^ 2 =
          ∑' _p : ι × κ, (0 : ℝ) := by
        apply tsum_congr
        intro p
        by_cases hpos : 0 < w p.1 * K p.1 p.2
        · simp [hedge p.1 p.2 hpos]
        · have hzero : w p.1 * K p.1 p.2 = 0 :=
            le_antisymm (le_of_not_gt hpos) (mul_nonneg (hw p.1) (hK p.1 p.2))
          rw [hzero, zero_mul]
      _ = 0 := tsum_zero

/-- Exact law of total second moment for a summably admitted Markov score transport. -/
theorem countableMarkov_secondMoment_conservation
    {w r : ι → ℝ} {K : ι → κ → ℝ} {s : κ → ℝ}
    (hrow : ∀ x, HasSum (K x) 1)
    (hscore : ∀ y, countableMarkovPushforward w K y * s y =
      countableMarkovScoreCurrent w r K y)
    (hfirst : Summable (fun p : ι × κ => w p.1 * K p.1 p.2 * r p.1 ^ 2))
    (hcross : Summable (fun p : ι × κ =>
      w p.1 * K p.1 p.2 * r p.1 * s p.2))
    (hlast : Summable (fun p : ι × κ => w p.1 * K p.1 p.2 * s p.2 ^ 2)) :
    ∑' x, w x * r x ^ 2 =
      ∑' y, countableMarkovPushforward w K y * s y ^ 2 +
        countableMarkovConditionalLoss w r K s := by
  let A : ι × κ → ℝ := fun p => w p.1 * K p.1 p.2 * r p.1 ^ 2
  let B : ι × κ → ℝ := fun p => w p.1 * K p.1 p.2 * r p.1 * s p.2
  let C : ι × κ → ℝ := fun p => w p.1 * K p.1 p.2 * s p.2 ^ 2
  have hA : Summable A := hfirst
  have hB : Summable B := hcross
  have hC : Summable C := hlast
  have hAtotal : ∑' p, A p = ∑' x, w x * r x ^ 2 := by
    rw [hA.tsum_prod]
    apply tsum_congr
    intro x
    have hs := (hrow x).mul_left (w x * r x ^ 2)
    calc
      ∑' y, A (x, y) = ∑' y, (w x * r x ^ 2) * K x y := by
        apply tsum_congr
        intro y
        simp only [A]
        ring
      _ = w x * r x ^ 2 := by simpa using hs.tsum_eq
  have hBtotal : ∑' p, B p =
      ∑' y, countableMarkovPushforward w K y * s y ^ 2 := by
    have hcomm : (∑' y, ∑' x, B (x, y)) = ∑' x, ∑' y, B (x, y) :=
      Summable.tsum_comm (f := fun x y => B (x, y)) hB
    calc
      ∑' p, B p = ∑' x, ∑' y, B (x, y) := hB.tsum_prod
      _ = ∑' y, ∑' x, B (x, y) := hcomm.symm
      _ = ∑' y, countableMarkovPushforward w K y * s y ^ 2 := by
        apply tsum_congr
        intro y
        calc
          ∑' x, B (x, y) = countableMarkovScoreCurrent w r K y * s y := by
            change (∑' x, (w x * K x y * r x) * s y) =
              (∑' x, w x * K x y * r x) * s y
            rw [tsum_mul_right]
          _ = countableMarkovPushforward w K y * s y ^ 2 := by
            rw [← hscore y]
            ring
  have hCtotal : ∑' p, C p =
      ∑' y, countableMarkovPushforward w K y * s y ^ 2 := by
    have hcomm : (∑' y, ∑' x, C (x, y)) = ∑' x, ∑' y, C (x, y) :=
      Summable.tsum_comm (f := fun x y => C (x, y)) hC
    calc
      ∑' p, C p = ∑' x, ∑' y, C (x, y) := hC.tsum_prod
      _ = ∑' y, ∑' x, C (x, y) := hcomm.symm
      _ = ∑' y, countableMarkovPushforward w K y * s y ^ 2 := by
        apply tsum_congr
        intro y
        change (∑' x, (w x * K x y) * s y ^ 2) =
          (∑' x, w x * K x y) * s y ^ 2
        rw [tsum_mul_right]
  have htwoB : Summable (fun p => 2 * B p) := hB.mul_left 2
  have hAB : Summable (fun p => A p - 2 * B p) := hA.sub htwoB
  have hLoss : countableMarkovConditionalLoss w r K s =
      (∑' p, A p) - 2 * (∑' p, B p) + ∑' p, C p := by
    rw [countableMarkovConditionalLoss]
    calc
      ∑' p : ι × κ, w p.1 * K p.1 p.2 * (r p.1 - s p.2) ^ 2 =
          ∑' p, ((A p - 2 * B p) + C p) := by
        apply tsum_congr
        intro p
        simp only [A, B, C]
        ring
      _ = (∑' p, (A p - 2 * B p)) + ∑' p, C p := hAB.tsum_add hC
      _ = ((∑' p, A p) - ∑' p, (2 * B p)) + ∑' p, C p := by
        rw [hA.tsum_sub htwoB]
      _ = (∑' p, A p) - 2 * (∑' p, B p) + ∑' p, C p := by
        rw [tsum_mul_left]
  calc
    ∑' x, w x * r x ^ 2 = ∑' p, A p := hAtotal.symm
    _ = (∑' y, countableMarkovPushforward w K y * s y ^ 2) +
        countableMarkovConditionalLoss w r K s := by
      rw [hLoss, hBtotal, hCtotal]
      ring

/-- Positive summably admitted Markov observation cannot increase Fisher second moment. -/
theorem countableMarkov_secondMoment_dataProcessing
    {w r : ι → ℝ} {K : ι → κ → ℝ} {s : κ → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hK : ∀ x y, 0 ≤ K x y)
    (hrow : ∀ x, HasSum (K x) 1)
    (hscore : ∀ y, countableMarkovPushforward w K y * s y =
      countableMarkovScoreCurrent w r K y)
    (hfirst : Summable (fun p : ι × κ => w p.1 * K p.1 p.2 * r p.1 ^ 2))
    (hcross : Summable (fun p : ι × κ =>
      w p.1 * K p.1 p.2 * r p.1 * s p.2))
    (hlast : Summable (fun p : ι × κ => w p.1 * K p.1 p.2 * s p.2 ^ 2)) :
    ∑' y, countableMarkovPushforward w K y * s y ^ 2 ≤
      ∑' x, w x * r x ^ 2 := by
  rw [countableMarkov_secondMoment_conservation hrow hscore hfirst hcross hlast]
  exact le_add_of_nonneg_right (tsum_nonneg fun p =>
    mul_nonneg (mul_nonneg (hw p.1) (hK p.1 p.2)) (sq_nonneg _))

/-- Strict receiver amplification excludes every summably admitted positive Markov realization. -/
theorem no_countablePositiveMarkov_realization_of_strictAmplification
    {w r : ι → ℝ} {K : ι → κ → ℝ} {s : κ → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hK : ∀ x y, 0 ≤ K x y)
    (hrow : ∀ x, HasSum (K x) 1)
    (hscore : ∀ y, countableMarkovPushforward w K y * s y =
      countableMarkovScoreCurrent w r K y)
    (hfirst : Summable (fun p : ι × κ => w p.1 * K p.1 p.2 * r p.1 ^ 2))
    (hcross : Summable (fun p : ι × κ =>
      w p.1 * K p.1 p.2 * r p.1 * s p.2))
    (hlast : Summable (fun p : ι × κ => w p.1 * K p.1 p.2 * s p.2 ^ 2))
    (hamplifies : (∑' x, w x * r x ^ 2) <
      ∑' y, countableMarkovPushforward w K y * s y ^ 2) :
    False :=
  (not_lt_of_ge (countableMarkov_secondMoment_dataProcessing
    hw hK hrow hscore hfirst hcross hlast)) hamplifies

/-- Equality in countable Fisher data processing is exactly edgewise score preservation. -/
theorem countableMarkov_secondMoment_eq_iff_scorePreserved
    {w r : ι → ℝ} {K : ι → κ → ℝ} {s : κ → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hK : ∀ x y, 0 ≤ K x y)
    (hrow : ∀ x, HasSum (K x) 1)
    (hscore : ∀ y, countableMarkovPushforward w K y * s y =
      countableMarkovScoreCurrent w r K y)
    (hfirst : Summable (fun p : ι × κ => w p.1 * K p.1 p.2 * r p.1 ^ 2))
    (hcross : Summable (fun p : ι × κ =>
      w p.1 * K p.1 p.2 * r p.1 * s p.2))
    (hlast : Summable (fun p : ι × κ => w p.1 * K p.1 p.2 * s p.2 ^ 2)) :
    (∑' y, countableMarkovPushforward w K y * s y ^ 2) =
        ∑' x, w x * r x ^ 2 ↔
      ∀ x y, 0 < w x * K x y → r x = s y := by
  have hcons := countableMarkov_secondMoment_conservation
    hrow hscore hfirst hcross hlast
  have hloss := countableMarkovConditionalLoss_eq_zero_iff hw hK
    (summable_countableMarkovConditionalLoss hfirst hcross hlast)
  constructor
  · intro heq
    apply hloss.mp
    linarith
  · intro hedge
    have hz := hloss.mpr hedge
    linarith

end SummablyAdmittedMarkovFisher

end GaloisForLFunctions.HTGeometry
