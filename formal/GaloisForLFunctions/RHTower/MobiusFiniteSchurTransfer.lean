import GaloisForLFunctions.Core
import GaloisForLFunctions.RHProofLab.EulerProductArithmetic
import GaloisForLFunctions.RHTower.FiniteSignedChannelCoisometry

open scoped BigOperators

noncomputable section

namespace RHTower

/-- The normalized two-point signed multiplier attached to a delay `h` with weight `q`. -/
def bernoulliSignedSchurFactor (q h : ℝ) (z : ℂ) : ℂ :=
  ((1 : ℂ) - (q : ℂ) * Complex.exp (-(h : ℂ) * z)) / ((1 : ℂ) + q)

theorem norm_bernoulliSignedSchurFactor_le_one
    {q h : ℝ} (hq : 0 ≤ q) (hh : 0 ≤ h) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖bernoulliSignedSchurFactor q h z‖ ≤ 1 := by
  have hexp : ‖Complex.exp (-(h : ℂ) * z)‖ ≤ 1 := by
    have hre : (-(h : ℂ) * z).re = -h * z.re := by
      simp [Complex.mul_re]
    rw [Complex.norm_exp, hre]
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hh hz]
  have hnum : ‖(1 : ℂ) - (q : ℂ) * Complex.exp (-(h : ℂ) * z)‖ ≤ 1 + q := by
    calc
      ‖(1 : ℂ) - (q : ℂ) * Complex.exp (-(h : ℂ) * z)‖
          ≤ ‖(1 : ℂ)‖ + ‖(q : ℂ) * Complex.exp (-(h : ℂ) * z)‖ := norm_sub_le _ _
      _ = 1 + q * ‖Complex.exp (-(h : ℂ) * z)‖ := by
        rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
      _ ≤ 1 + q := by
        have hmul := mul_le_mul_of_nonneg_left hexp hq
        nlinarith
  have hden : ‖(1 : ℂ) + q‖ = 1 + q := by
    have heq : (1 : ℂ) + q = ((1 + q : ℝ) : ℂ) := by push_cast; ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [bernoulliSignedSchurFactor, norm_div, hden]
  exact (div_le_one (by linarith)).2 hnum

/-- The positive Euler weight `p^{-sigma}`, written without real-power branch conventions. -/
def primeSchurWeight (sigma : ℝ) (p : Nat.Primes) : ℝ :=
  Real.exp (-sigma * Real.log (p : ℝ))

theorem primeSchurWeight_pos (sigma : ℝ) (p : Nat.Primes) :
    0 < primeSchurWeight sigma p := by
  exact Real.exp_pos _

theorem bernoulliSignedSchurFactor_prime_eq
    (sigma : ℝ) (p : Nat.Primes) (z : ℂ) :
    bernoulliSignedSchurFactor (primeSchurWeight sigma p) (Real.log (p : ℝ)) z =
      ((1 : ℂ) - Complex.exp
        (-((sigma : ℂ) + z) * (Real.log (p : ℝ) : ℂ))) /
      ((1 : ℂ) + Real.exp (-sigma * Real.log (p : ℝ))) := by
  rw [bernoulliSignedSchurFactor, primeSchurWeight, Complex.ofReal_exp]
  congr 2
  rw [← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The finite-prime signed transfer multiplier. -/
def finitePrimeSignedSchurTransfer (S : Finset Nat.Primes) (sigma : ℝ) (z : ℂ) : ℂ :=
  ∏ p ∈ S, bernoulliSignedSchurFactor
    (primeSchurWeight sigma p) (Real.log (p : ℝ)) z

/-- The signed squarefree character attached to a finite prime subset. -/
def finitePrimeSignedSquarefreeTerm (sigma : ℝ) (z : ℂ)
    (T : Finset Nat.Primes) : ℂ :=
  ∏ p ∈ T, -(primeSchurWeight sigma p : ℂ) *
    Complex.exp (-(Real.log (p : ℝ) : ℂ) * z)

/-- The positive Bernoulli normalization of a finite prime aperture. -/
def finitePrimeSignedSchurDenominator (S : Finset Nat.Primes) (sigma : ℝ) : ℂ :=
  ∏ p ∈ S, ((1 + primeSchurWeight sigma p : ℝ) : ℂ)

theorem finitePrimeSignedSchurTransfer_squarefreeExpansion
    (S : Finset Nat.Primes) (sigma : ℝ) (z : ℂ) :
    finitePrimeSignedSchurTransfer S sigma z =
      (∑ T ∈ S.powerset, finitePrimeSignedSquarefreeTerm sigma z T) /
        finitePrimeSignedSchurDenominator S sigma := by
  classical
  rw [finitePrimeSignedSchurTransfer]
  simp only [bernoulliSignedSchurFactor, Finset.prod_div_distrib]
  congr 1
  · simpa [GaloisForLFunctions.RHProofLab.finiteLocalEulerProduct,
      GaloisForLFunctions.RHProofLab.squarefreeMonomial,
      finitePrimeSignedSquarefreeTerm, sub_eq_add_neg] using
        (GaloisForLFunctions.RHProofLab.finiteLocalEulerProduct_subsetExpansion S
          (fun p : Nat.Primes => -(primeSchurWeight sigma p : ℂ) *
            Complex.exp (-(Real.log (p : ℝ) : ℂ) * z)))
  · simp [finitePrimeSignedSchurDenominator]

theorem norm_finitePrimeSignedSchurTransfer_le_one
    (S : Finset Nat.Primes) (sigma : ℝ)
    {z : ℂ} (hz : 0 ≤ z.re) :
    ‖finitePrimeSignedSchurTransfer S sigma z‖ ≤ 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [finitePrimeSignedSchurTransfer]
  | @insert p S hp ih =>
      have hpone : (1 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (Nat.Prime.one_lt p.2).le
      have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hpone
      have hlocal : ‖bernoulliSignedSchurFactor
          (primeSchurWeight sigma p) (Real.log (p : ℝ)) z‖ ≤ 1 :=
        norm_bernoulliSignedSchurFactor_le_one
          (primeSchurWeight_pos sigma p).le hlog hz
      rw [finitePrimeSignedSchurTransfer]
      simp only [Finset.prod_insert hp, norm_mul]
      calc
        _ ≤ 1 * 1 := mul_le_mul hlocal ih (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1

/-- The finite squarefree Bernoulli law underlying the signed Möbius channel. -/
def finitePrimeSquarefreeProbability (S : Finset Nat.Primes) (sigma : ℝ)
    (T : Finset Nat.Primes) : ℝ :=
  (∏ p ∈ T, primeSchurWeight sigma p) /
    ∏ p ∈ S, (1 + primeSchurWeight sigma p)

theorem finitePrimeSquarefreeProbability_nonneg
    (S : Finset Nat.Primes) (sigma : ℝ) (T : Finset Nat.Primes) :
    0 ≤ finitePrimeSquarefreeProbability S sigma T := by
  unfold finitePrimeSquarefreeProbability
  apply div_nonneg
  · exact Finset.prod_nonneg (fun p _ => (primeSchurWeight_pos sigma p).le)
  · exact (Finset.prod_pos (fun p _ => by
      linarith [primeSchurWeight_pos sigma p])).le

theorem sum_finitePrimeSquarefreeProbability
    (S : Finset Nat.Primes) (sigma : ℝ) :
    ∑ T ∈ S.powerset, finitePrimeSquarefreeProbability S sigma T = 1 := by
  classical
  let D : ℝ := ∏ p ∈ S, (1 + primeSchurWeight sigma p)
  have hD : D ≠ 0 := by
    exact ne_of_gt (Finset.prod_pos (fun p _ => by
      linarith [primeSchurWeight_pos sigma p]))
  rw [show (∑ T ∈ S.powerset, finitePrimeSquarefreeProbability S sigma T) =
      (∑ T ∈ S.powerset, ∏ p ∈ T, primeSchurWeight sigma p) / D by
    simp only [finitePrimeSquarefreeProbability, D, Finset.sum_div]]
  have hexp : (∑ T ∈ S.powerset, ∏ p ∈ T, primeSchurWeight sigma p) = D := by
    simpa [GaloisForLFunctions.RHProofLab.finiteLocalEulerProduct,
      GaloisForLFunctions.RHProofLab.squarefreeMonomial, D] using
      (GaloisForLFunctions.RHProofLab.finiteLocalEulerProduct_subsetExpansion S
        (primeSchurWeight sigma)).symm
  rw [hexp]
  change D / D = 1
  exact div_self hD

/-- The signed square-root amplitude on squarefree subsets; its sign is the finite Möbius sign. -/
def finitePrimeSquarefreeAmplitude (S : Finset Nat.Primes) (sigma : ℝ)
    (T : ↥S.powerset) : ℂ :=
  (((-1 : ℝ) ^ T.1.card *
    Real.sqrt (finitePrimeSquarefreeProbability S sigma T.1) : ℝ) : ℂ)

theorem norm_finitePrimeSquarefreeAmplitude_sq
    (S : Finset Nat.Primes) (sigma : ℝ) (T : ↥S.powerset) :
    ‖finitePrimeSquarefreeAmplitude S sigma T‖ ^ 2 =
      finitePrimeSquarefreeProbability S sigma T.1 := by
  have hP := finitePrimeSquarefreeProbability_nonneg S sigma T.1
  rw [finitePrimeSquarefreeAmplitude, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt hP]

theorem finitePrimeSquarefreeAmplitude_unit
    (S : Finset Nat.Primes) (sigma : ℝ) :
    ∑ T : ↥S.powerset, ‖finitePrimeSquarefreeAmplitude S sigma T‖ ^ 2 = 1 := by
  classical
  simp_rw [norm_finitePrimeSquarefreeAmplitude_sq]
  rw [Finset.univ_eq_attach, Finset.sum_attach]
  exact sum_finitePrimeSquarefreeProbability S sigma

/-- The finite squarefree Möbius channel is an exact coisometry. -/
theorem finitePrimeSquarefreeSynthesis_analysis
    (S : Finset Nat.Primes) (sigma : ℝ) (c : ℂ) :
    finiteSignedChannelSynthesis (finitePrimeSquarefreeAmplitude S sigma)
        (finiteSignedChannelAnalysis (finitePrimeSquarefreeAmplitude S sigma) c) = c :=
  finiteSignedChannelSynthesis_analysis
    (finitePrimeSquarefreeAmplitude_unit S sigma) c

/-- The arithmetic channel projection is genuinely idempotent at every finite prime aperture. -/
theorem finitePrimeSquarefreeProjection_idempotent
    (S : Finset Nat.Primes) (sigma : ℝ)
    (f : ↥S.powerset → ℂ) :
    finiteSignedChannelProjection (finitePrimeSquarefreeAmplitude S sigma)
        (finiteSignedChannelProjection (finitePrimeSquarefreeAmplitude S sigma) f) =
      finiteSignedChannelProjection (finitePrimeSquarefreeAmplitude S sigma) f :=
  finiteSignedChannelProjection_idempotent
    (finitePrimeSquarefreeAmplitude_unit S sigma) f

end RHTower
