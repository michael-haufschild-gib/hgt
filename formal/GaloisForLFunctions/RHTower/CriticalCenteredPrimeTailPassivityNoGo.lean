import GaloisForLFunctions.RHTower.CriticalCenteredPrimeTailEntireCarrier
import GaloisForLFunctions.HTGeometry.RealDirichletSeries

/-!
# Centered prime-tail passivity no-go

Exact `Λ-1` centering removes the pole but necessarily destroys Hilbert-space passivity.  On every
safe vertical line, the differentiated centered current is an absolutely convergent atomic Fourier
series.  Its atom at `n=6` has coefficient `-6^{-σ}`, since `6` is not a prime power.  Atomic
Bochner recovery then rules out positive definiteness on every safe line.

This is stronger than finding one negative test matrix: it identifies the immutable negative
spectral atom.  Any successful metric realization of the centered Route T current must therefore
retain an indefinite/Jordan channel or add a nontrivial positive completion before scalarization.
-/

open Complex Filter Topology LSeries ArithmeticFunction

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Real centered current coefficient: `Λ(n)-1` from `n=2` onward. -/
def centeredPrimeTailCurrentRealCoeff (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n - if 2 ≤ n then 1 else 0

/-- Safe-line atomic weight of the differentiated centered current. -/
def centeredPrimeTailCurrentFourierWeight (σ : ℝ) (n : ℕ) : ℝ :=
  centeredPrimeTailCurrentRealCoeff n * (n : ℝ) ^ (-σ)

/-- Dirichlet vertical frequency convention. -/
def centeredPrimeTailCurrentFourierFrequency (n : ℕ) : ℝ :=
  -Real.log n

/-- Atomic vertical trace of the centered current. -/
def centeredPrimeTailCurrentVerticalTrace (σ u : ℝ) : ℂ :=
  atomicFourierSeries (centeredPrimeTailCurrentFourierWeight σ)
    centeredPrimeTailCurrentFourierFrequency u

theorem abs_centeredPrimeTailCurrentRealCoeff_le (n : ℕ) :
    |centeredPrimeTailCurrentRealCoeff n| ≤ ArithmeticFunction.vonMangoldt n + 1 := by
  rw [centeredPrimeTailCurrentRealCoeff]
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  split_ifs
  · calc
      |ArithmeticFunction.vonMangoldt n - 1| ≤
          |ArithmeticFunction.vonMangoldt n| + |(1 : ℝ)| := abs_sub _ _
      _ = ArithmeticFunction.vonMangoldt n + 1 := by rw [abs_of_nonneg hΛ, abs_one]
  · simp [abs_of_nonneg hΛ]

theorem summable_abs_centeredPrimeTailCurrentFourierWeight
    {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n => |centeredPrimeTailCurrentFourierWeight σ n| := by
  have hΛ : Summable fun n : ℕ =>
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) :=
    GaloisForLFunctions.HTGeometry.summable_vonMangoldt_rpow hσ
  have h1 : Summable fun n : ℕ => (n : ℝ) ^ (-σ) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hmajor : Summable fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n + 1) * (n : ℝ) ^ (-σ) := by
    convert hΛ.add h1 using 1
    funext n
    ring
  apply Summable.of_nonneg_of_le (fun n => abs_nonneg _)
    (fun n => ?_) hmajor
  rw [centeredPrimeTailCurrentFourierWeight, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  exact mul_le_mul_of_nonneg_right (abs_centeredPrimeTailCurrentRealCoeff_le n)
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)

private theorem centeredPrimeTailCurrentFourierFrequency_ne_of_weight_ne
    (σ : ℝ) (q n : ℕ) (hnq : n ≠ q)
    (hnw : centeredPrimeTailCurrentFourierWeight σ n ≠ 0) :
    centeredPrimeTailCurrentFourierFrequency n ≠
      centeredPrimeTailCurrentFourierFrequency q := by
  have hn2 : 2 ≤ n := by
    by_contra hn
    have hnlt : n < 2 := Nat.lt_of_not_ge hn
    interval_cases n <;>
      simp [centeredPrimeTailCurrentFourierWeight, centeredPrimeTailCurrentRealCoeff] at hnw
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn2)
  unfold centeredPrimeTailCurrentFourierFrequency
  intro hneg
  have hlog : Real.log n = Real.log q := neg_injective hneg
  by_cases hq0 : q = 0
  · subst q
    simp only [Nat.cast_zero, Real.log_zero] at hlog
    have hnone : (1 : ℝ) < n := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn2)
    linarith [Real.log_pos hnone]
  · have hqpos : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq0
    have hcast : (n : ℝ) = (q : ℝ) := by
      calc
        (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hnpos).symm
        _ = Real.exp (Real.log q) := congrArg Real.exp hlog
        _ = (q : ℝ) := Real.exp_log hqpos
    exact hnq (by exact_mod_cast hcast)

private theorem not_isPrimePow_six : ¬ IsPrimePow 6 := by
  rw [Nat.not_isPrimePow_iff_nontrivial_of_two_le (by norm_num)]
  exact ⟨2, Nat.mem_primeFactors.mpr ⟨Nat.prime_two, by norm_num, by norm_num⟩,
    3, Nat.mem_primeFactors.mpr ⟨Nat.prime_three, by norm_num, by norm_num⟩, by norm_num⟩

private theorem vonMangoldt_six : ArithmeticFunction.vonMangoldt 6 = 0 :=
  ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr not_isPrimePow_six

/-- The composite non-prime-power atom `n=6` is strictly negative on every real vertical line. -/
theorem centeredPrimeTailCurrentFourierWeight_six_neg (σ : ℝ) :
    centeredPrimeTailCurrentFourierWeight σ 6 < 0 := by
  rw [centeredPrimeTailCurrentFourierWeight, centeredPrimeTailCurrentRealCoeff,
    vonMangoldt_six, if_pos (by norm_num)]
  have hpow : 0 < ((6 : ℕ) : ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by norm_num) _
  simpa only [zero_sub, neg_mul, one_mul] using neg_lt_zero.mpr hpow

/-- The atomic trace is literally the safe centered-current Dirichlet series. -/
theorem centeredPrimeTailCurrentVerticalTrace_eq_LSeries
    (σ u : ℝ) :
    centeredPrimeTailCurrentVerticalTrace σ u =
      LSeries
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) - zetaTailDirichletCoeff n)
        ((σ : ℂ) + (u : ℂ) * I) := by
  unfold centeredPrimeTailCurrentVerticalTrace atomicFourierSeries LSeries
  apply tsum_congr
  intro n
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [LSeries.term_zero, centeredPrimeTailCurrentFourierWeight,
      centeredPrimeTailCurrentRealCoeff, centeredPrimeTailCurrentFourierFrequency]
  · rw [LSeries.term_of_ne_zero hn0]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hscalar :
        (((n : ℝ) ^ (-σ) : ℝ) : ℂ) *
            realFourierCharacter (-Real.log n) u =
          1 / (n : ℂ) ^ ((σ : ℂ) + (u : ℂ) * I) := by
      rw [Real.rpow_def_of_pos hnpos, Complex.ofReal_exp, realFourierCharacter]
      rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn0)]
      rw [one_div, ← Complex.exp_neg, ← Complex.exp_add]
      congr 1
      have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) :=
        (Complex.ofReal_log hnpos.le).symm
      rw [hlog]
      push_cast
      ring
    rw [centeredPrimeTailCurrentFourierWeight,
      centeredPrimeTailCurrentFourierFrequency]
    have hcoeff :
        ((centeredPrimeTailCurrentRealCoeff n : ℝ) : ℂ) =
          (ArithmeticFunction.vonMangoldt n : ℂ) - zetaTailDirichletCoeff n := by
      rw [centeredPrimeTailCurrentRealCoeff, zetaTailDirichletCoeff]
      split_ifs <;> push_cast <;> ring
    rw [Complex.ofReal_mul, hcoeff, mul_assoc, hscalar]
    simp only [one_mul, div_eq_mul_inv]

/-- Safe atomic trace equals the pole-cancelled meromorphic current. -/
theorem centeredPrimeTailCurrentVerticalTrace_eq_continuation
    {σ : ℝ} (hσ : 1 < σ) (u : ℝ) :
    centeredPrimeTailCurrentVerticalTrace σ u =
      -centeredPrimeTailCurrentContinuation ((σ : ℂ) + (u : ℂ) * I) := by
  let s : ℂ := (σ : ℂ) + (u : ℂ) * I
  have hs : 1 < s.re := by simpa [s] using hσ
  rw [centeredPrimeTailCurrentVerticalTrace_eq_LSeries σ]
  have hcoeff : LSeries.logMul centeredPrimeTailEulerCoeff =
      fun n => (ArithmeticFunction.vonMangoldt n : ℂ) - zetaTailDirichletCoeff n := by
    funext n
    exact logMul_centeredPrimeTailEulerCoeff n
  rw [← hcoeff, LSeries_logMul_centeredPrimeTailEulerCoeff_eq hs,
    ← infinitePrimeFlux_eq_vonMangoldtLSeries hs, infinitePrimeFlux]
  rw [centeredPrimeTailCurrentContinuation_eq hs]
  ring

/-- **C47 passivity no-go.** Exact pole-cancelling centering is never positive definite, even on
safe lines of absolute convergence. -/
theorem not_positiveDefiniteOnReal_centeredPrimeTailCurrentVerticalTrace
    {σ : ℝ} (hσ : 1 < σ) :
    ¬ PositiveDefiniteOnReal (centeredPrimeTailCurrentVerticalTrace σ) := by
  intro hpd
  have hnonneg : 0 ≤ centeredPrimeTailCurrentFourierWeight σ 6 :=
    atomicFourierSeries_weight_nonnegative_of_positiveDefinite
      (summable_abs_centeredPrimeTailCurrentFourierWeight hσ)
      (centeredPrimeTailCurrentFourierFrequency_ne_of_weight_ne σ)
      hpd 6
  linarith [centeredPrimeTailCurrentFourierWeight_six_neg σ]

/-- Consequently the safe vertical centered source, which is the negative derivative of the
centered Euler primitive, is not positive definite. -/
theorem not_positiveDefiniteOnReal_neg_centeredPrimeTailCurrentContinuation_vertical
    {σ : ℝ} (hσ : 1 < σ) :
    ¬ PositiveDefiniteOnReal
      (fun u : ℝ => -centeredPrimeTailCurrentContinuation ((σ : ℂ) + (u : ℂ) * I)) := by
  rw [show (fun u : ℝ =>
      -centeredPrimeTailCurrentContinuation ((σ : ℂ) + (u : ℂ) * I)) =
      centeredPrimeTailCurrentVerticalTrace σ by
    funext u
    exact (centeredPrimeTailCurrentVerticalTrace_eq_continuation hσ u).symm]
  exact not_positiveDefiniteOnReal_centeredPrimeTailCurrentVerticalTrace hσ

end

end RHTower
