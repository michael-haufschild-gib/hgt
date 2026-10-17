import GaloisForLFunctions.RHTower.XiGaussianHeatTwoPrimeSampling
import GaloisForLFunctions.RHTower.XiGaussianHeatPrimeChirpReceiver
import GaloisForLFunctions.RHTower.PrimeTailSeedHurwitzReflection

/-!
# Two sampled arithmetic source forms detect the Hurwitz reflection residual

On the grid `t = (2K+1+n)h`, the polar correction is the rank-one moment
sequence `2 exp(h/4)^(2K+1+n)`. Removing its polynomial evaluation direction
leaves the literal archimedean-minus-prime form. Two prime-log grids retain
the complete RH criterion on these pole hyperplanes, at arbitrary finite
starting offsets. No derivatives of the arithmetic source are needed.
-/

open Complex Polynomial

namespace RHTower

noncomputable section

/-- The literal archimedean-minus-prime source, without the polar correction. -/
def xiPrimeArchHeatGridMoment (h : ℝ) (K n : ℕ) : ℝ :=
  let t : ℝ := (2 * K + 1 + n : ℕ) * h
  (gaussianArchCriticalC t - gaussianPrimeChirpC t).re / Real.pi

/-- Polynomial coordinate of the omitted polar exponential on a heat grid. -/
def xiHeatGridPole (h : ℝ) : ℝ := Real.exp (h / 4)

/-- The exact arithmetic source differs from sampled heat by one geometric atom. -/
theorem xiPrimeArchHeatGridMoment_eq {h : ℝ} (hh : 0 < h) (K n : ℕ) :
    xiPrimeArchHeatGridMoment h K n = xiHeatGridMoment h K n -
      2 * xiHeatGridPole h ^ (2 * K + 1 + n) := by
  let t : ℝ := (2 * K + 1 + n : ℕ) * h
  have ht : 0 < t := by dsimp [t]; positivity
  have harg : -(t : ℂ) * xiMassArchPole ^ 2 = ((t / 4 : ℝ) : ℂ) := by
    rw [xiMassArchPole]
    push_cast
    ring_nf
    rw [I_sq]
    ring
  have hpole : (gaussianArchPoleC t).re = 2 * Real.pi * Real.exp (t / 4) := by
    rw [gaussianArchPoleC, harg]
    simp [Complex.exp_re]
  have hsource := congrArg Complex.re (pi_mul_xiGaussianHeatTraceC_ofReal ht)
  have htrace : (xiGaussianHeatTraceC (t : ℂ)).re = xiGaussianHeatTraceReal t := rfl
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.add_re, Complex.sub_re, htrace, hpole] at hsource
  have hexp : Real.exp (t / 4) = xiHeatGridPole h ^ (2 * K + 1 + n) := by
    rw [xiHeatGridPole, ← Real.exp_nat_mul]
    congr 1
    dsimp [t]
    ring
  rw [hexp] at hsource
  change (gaussianArchCriticalC t - gaussianPrimeChirpC t).re / Real.pi =
    xiGaussianHeatTraceReal t - 2 * xiHeatGridPole h ^ (2 * K + 1 + n)
  rw [Complex.sub_re, div_eq_iff Real.pi_ne_zero]
  linarith

/-- The entire source discrepancy is one polynomial evaluation, at every rank. -/
theorem momentFunctional_xiPrimeArchHeatGridMoment {h : ℝ} (hh : 0 < h)
    (K : ℕ) (p : ℝ[X]) :
    HTGeometry.momentFunctional (xiPrimeArchHeatGridMoment h K) p =
      HTGeometry.momentFunctional (xiHeatGridMoment h K) p -
        2 * xiHeatGridPole h ^ (2 * K + 1) * p.eval (xiHeatGridPole h) := by
  rw [HTGeometry.momentFunctional_eq_support_sum,
    HTGeometry.momentFunctional_eq_support_sum, Polynomial.eval_eq_sum,
    Polynomial.sum_def, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [xiPrimeArchHeatGridMoment_eq hh, pow_add]
  ring

/-- The arithmetic and heat square forms agree exactly on the pole hyperplane. -/
theorem momentFunctional_xiPrimeArchHeatGridMoment_square_of_pole_zero
    {h : ℝ} (hh : 0 < h) (K : ℕ) (p : ℝ[X])
    (hp : p.eval (xiHeatGridPole h) = 0) :
    HTGeometry.momentFunctional (xiPrimeArchHeatGridMoment h K) (p ^ 2) =
      HTGeometry.momentFunctional (xiHeatGridMoment h K) (p ^ 2) := by
  rw [momentFunctional_xiPrimeArchHeatGridMoment hh, Polynomial.eval_pow, hp]
  simp

/-- All-degree source positivity on the single explicit pole hyperplane. -/
def XiPrimeArchHeatGridNonnegative (h : ℝ) (K : ℕ) : Prop :=
  ∀ p : ℝ[X], p.eval (xiHeatGridPole h) = 0 →
    0 ≤ HTGeometry.momentFunctional (xiPrimeArchHeatGridMoment h K) (p ^ 2)

/-- Removing the pole direction cannot hide any nonreal heat sampling node. -/
theorem xiGaussianHeatTerm_im_eq_zero_of_sourceGrid_nonnegative
    {h : ℝ} (hh : 0 < h) (K : ℕ) (hpos : XiPrimeArchHeatGridNonnegative h K) :
    ∀ q : XiZeroCopy, (xiGaussianHeatTerm h q).im = 0 := by
  let a : ℝ[X] := X - C (xiHeatGridPole h)
  apply traceHankel_nonnegative_on_principalIdeal_implies_real
    (xiGaussianHeatTerm h) (xiGaussianHeatTerm_ne_zero h)
    (fun {_} hr => finite_setOf_le_norm_xiGaussianHeatTerm hh hr)
    (summable_xiGaussianHeatTerm hh) (X ^ K * a)
  · intro q hq
    rw [evalRealPolynomial_mul]
    apply mul_ne_zero
    · simpa [evalRealPolynomial] using pow_ne_zero K (xiGaussianHeatTerm_ne_zero h q)
    · have heval : evalRealPolynomial a (xiGaussianHeatTerm h q) =
          xiGaussianHeatTerm h q - (xiHeatGridPole h : ℂ) := by
        simp [a, evalRealPolynomial]
      rw [heval]
      intro heq
      have him := congrArg Complex.im heq
      exact hq (by simpa using him)
  · intro p
    have hp : (a * p).eval (xiHeatGridPole h) = 0 := by simp [a]
    have hnonneg := hpos (a * p) hp
    rw [momentFunctional_xiPrimeArchHeatGridMoment_square_of_pole_zero hh K _ hp,
      momentFunctional_xiHeatGridMoment_square hh] at hnonneg
    simpa only [mul_assoc] using hnonneg

/-- RH supplies the complete arithmetic source sign after exact polar cancellation. -/
theorem xiPrimeArchHeatGridNonnegative_of_rh (hRH : RiemannHypothesis)
    {h : ℝ} (hh : 0 < h) (K : ℕ) : XiPrimeArchHeatGridNonnegative h K := by
  intro p hp
  rw [momentFunctional_xiPrimeArchHeatGridMoment_square_of_pole_zero hh K p hp]
  exact (completeHankelCone_iff_momentFunctional_square_nonnegative _).mp
    (completeHankelCone_xiHeatGridMoment_of_rh hRH hh K) p

/-- Two literal prime-log source grids characterize RH on their pole hyperplanes. -/
theorem riemannHypothesis_iff_two_prime_sourceGrid {p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) (K L : ℕ) :
    RiemannHypothesis ↔
      XiPrimeArchHeatGridNonnegative (Real.log p) K ∧
      XiPrimeArchHeatGridNonnegative (Real.log r) L := by
  have hp0 : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hr0 : 0 < Real.log r := Real.log_pos (by exact_mod_cast hr.one_lt)
  constructor
  · intro hRH
    exact ⟨xiPrimeArchHeatGridNonnegative_of_rh hRH hp0 K,
      xiPrimeArchHeatGridNonnegative_of_rh hRH hr0 L⟩
  · rintro ⟨h₁, h₂⟩
    by_contra hRH
    obtain ⟨q, hq⟩ := exists_spectralSq_im_pos_of_not_riemannHypothesis hRH
    have hw := im_eq_zero_of_two_prime_exp_real hp hr hpr (xiSpectralPoint q ^ 2)
      (xiGaussianHeatTerm_im_eq_zero_of_sourceGrid_nonnegative hp0 K h₁ q)
      (xiGaussianHeatTerm_im_eq_zero_of_sourceGrid_nonnegative hr0 L h₂ q)
    exact (ne_of_gt hq) hw

/-- A fixed pair of arithmetic heat grids suffices, after any finite prefixes. -/
theorem riemannHypothesis_iff_two_three_sourceGrid (K L : ℕ) :
    RiemannHypothesis ↔
      XiPrimeArchHeatGridNonnegative (Real.log 2) K ∧
      XiPrimeArchHeatGridNonnegative (Real.log 3) L :=
  riemannHypothesis_iff_two_prime_sourceGrid Nat.prime_two Nat.prime_three (by omega) K L

/-- Exact transport from two sampled prime--Gamma forms to the literal HJ residual. -/
theorem hurwitzReflectionResidual_iff_two_three_sourceGrid (K L : ℕ) :
    XiPrimeTailSeedTwoReflectionResidualVanishes ↔
      XiPrimeArchHeatGridNonnegative (Real.log 2) K ∧
      XiPrimeArchHeatGridNonnegative (Real.log 3) L := by
  rw [xiPrimeTailSeedTwoReflectionResidualVanishes_iff_riemannHypothesis,
    riemannHypothesis_iff_two_three_sourceGrid K L]

end

end RHTower
