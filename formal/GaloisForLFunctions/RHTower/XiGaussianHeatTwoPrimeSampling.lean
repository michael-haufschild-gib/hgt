import GaloisForLFunctions.RHTower.XiGaussianHeatTraceCriterion
import GaloisForLFunctions.RHTower.PrimeLogIncommensuratePhaseClock
import GaloisForLFunctions.RHTower.CompleteHankelSignCone

/-!
# Two prime-log sampling grids for the actual Xi heat trace

The Hankel moments here are values of the heat trace on an arithmetic grid,
not its derivatives at one time. Each grid tests the compact spectral
coordinates `exp (-h z_q²)`. Positivity forces these coordinates to be real,
but one grid can alias their imaginary frequencies. The logarithmic grids
of two distinct primes remove that ambiguity. Every odd starting offset is
allowed, so deleting an arbitrary finite prefix loses no information.
-/

open Complex Polynomial Filter Topology

namespace RHTower

noncomputable section

/-- Heat values on one positive arithmetic grid after an odd starting offset. -/
def xiHeatGridMoment (h : ℝ) (K n : ℕ) : ℝ :=
  xiGaussianHeatTraceReal ((2 * K + 1 + n : ℕ) * h)

theorem xiGaussianHeatTerm_ne_zero (h : ℝ) (q : XiZeroCopy) :
    xiGaussianHeatTerm h q ≠ 0 :=
  Complex.exp_ne_zero _

/-- Powers of a sampled exponential are exactly later heat values. -/
theorem xiGaussianHeatTerm_pow (h : ℝ) (n : ℕ) (q : XiZeroCopy) :
    xiGaussianHeatTerm h q ^ n = xiGaussianHeatTerm ((n : ℝ) * h) q := by
  rw [xiGaussianHeatTerm, xiGaussianHeatTerm, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Exponential heat coordinates accumulate only at zero. -/
theorem finite_setOf_le_norm_xiGaussianHeatTerm {h : ℝ} (hh : 0 < h)
    {r : ℝ} (hr : 0 < r) :
    {q : XiZeroCopy | r ≤ ‖xiGaussianHeatTerm h q‖}.Finite := by
  have hev := (Metric.tendsto_nhds.mp
    (summable_xiGaussianHeatTerm hh).tendsto_cofinite_zero) r hr
  rw [Filter.eventually_cofinite] at hev
  simpa only [dist_zero_right, not_lt] using hev

theorem evalRealPolynomial_eq_support_sum (p : ℝ[X]) (z : ℂ) :
    evalRealPolynomial p z = ∑ k ∈ p.support, (p.coeff k : ℂ) * z ^ k := by
  simp only [evalRealPolynomial, Polynomial.eval_map, Polynomial.eval₂_eq_sum,
    Polynomial.sum_def, Complex.coe_algebraMap]

/-- Exact source identity: sampled moments are the exponential-coordinate trace. -/
theorem momentFunctional_xiHeatGridMoment {h : ℝ} (hh : 0 < h)
    (K : ℕ) (p : ℝ[X]) :
    HTGeometry.momentFunctional (xiHeatGridMoment h K) p =
      (∑' q : XiZeroCopy, xiGaussianHeatTerm h q ^ (2 * K + 1) *
        evalRealPolynomial p (xiGaussianHeatTerm h q)).re := by
  have hterm (q : XiZeroCopy) :
      xiGaussianHeatTerm h q ^ (2 * K + 1) *
          evalRealPolynomial p (xiGaussianHeatTerm h q) =
        ∑ k ∈ p.support, (p.coeff k : ℂ) *
          xiGaussianHeatTerm ((2 * K + 1 + k : ℕ) * h) q := by
    rw [evalRealPolynomial_eq_support_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← xiGaussianHeatTerm_pow]
    ring
  have hsum (k : ℕ) : Summable (fun q : XiZeroCopy =>
      (p.coeff k : ℂ) * xiGaussianHeatTerm ((2 * K + 1 + k : ℕ) * h) q) :=
    (summable_xiGaussianHeatTerm (by positivity)).mul_left _
  rw [tsum_congr hterm, Summable.tsum_finsetSum (fun k _ => hsum k),
    Complex.re_sum, HTGeometry.momentFunctional_eq_support_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [tsum_mul_left]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rfl

/-- An odd offset is exactly restriction of the trace-Hankel form to `X^K`. -/
theorem momentFunctional_xiHeatGridMoment_square {h : ℝ} (hh : 0 < h)
    (K : ℕ) (p : ℝ[X]) :
    HTGeometry.momentFunctional (xiHeatGridMoment h K) (p ^ 2) =
      (∑' q : XiZeroCopy, xiGaussianHeatTerm h q *
        evalRealPolynomial (X ^ K * p) (xiGaussianHeatTerm h q) ^ 2).re := by
  rw [momentFunctional_xiHeatGridMoment hh]
  congr 1
  apply tsum_congr
  intro q
  simp only [evalRealPolynomial_pow, evalRealPolynomial_mul]
  have hx : evalRealPolynomial X (xiGaussianHeatTerm h q) =
      xiGaussianHeatTerm h q := by simp [evalRealPolynomial]
  rw [hx]
  ring

/-- Positivity on a single grid forces reality of every sampled exponential. -/
theorem xiGaussianHeatTerm_im_eq_zero_of_grid_nonnegative {h : ℝ} (hh : 0 < h)
    (K : ℕ) (hpos : CompleteHankelCone (xiHeatGridMoment h K)) :
    ∀ q : XiZeroCopy, (xiGaussianHeatTerm h q).im = 0 := by
  apply traceHankel_nonnegative_on_principalIdeal_implies_real
    (xiGaussianHeatTerm h) (xiGaussianHeatTerm_ne_zero h)
    (fun {_} hr => finite_setOf_le_norm_xiGaussianHeatTerm hh hr)
    (summable_xiGaussianHeatTerm hh) (X ^ K)
  · intro q _
    simpa [evalRealPolynomial] using pow_ne_zero K (xiGaussianHeatTerm_ne_zero h q)
  · intro p
    rw [← momentFunctional_xiHeatGridMoment_square hh K p]
    exact (completeHankelCone_iff_momentFunctional_square_nonnegative _).mp hpos p

/-- A real exponential sample fixes the doubled imaginary phase clock. -/
theorem phaseClockValue_of_exp_neg_mul_im_eq_zero (h : ℝ) (w : ℂ)
    (hw : (Complex.exp (-(h : ℂ) * w)).im = 0) :
    HTGeometry.phaseClockValue h (-2 * w.im) = HTGeometry.phaseClockValue h 0 := by
  have heq : Complex.exp (-(h : ℂ) * w) =
      Complex.exp (-(h : ℂ) * (starRingEnd ℂ) w) := by
    simpa only [← Complex.exp_conj, map_mul, map_neg, Complex.conj_ofReal]
      using (Complex.conj_eq_iff_im.mpr hw).symm
  have harg : ((h * (-2 * w.im) : ℝ) : ℂ) * I =
      -(h : ℂ) * w - (-(h : ℂ) * (starRingEnd ℂ) w) := by
    apply Complex.ext
    · simp [Complex.mul_re]
    · simp [Complex.mul_im]
      ring
  simp only [HTGeometry.phaseClockValue, mul_zero, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero]
  rw [harg, Complex.exp_sub, heq, div_self (Complex.exp_ne_zero _)]

/-- Two distinct prime grids remove every exponential alias of a frequency. -/
theorem im_eq_zero_of_two_prime_exp_real {p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) (w : ℂ)
    (h₁ : (Complex.exp (-(Real.log p : ℂ) * w)).im = 0)
    (h₂ : (Complex.exp (-(Real.log r : ℂ) * w)).im = 0) : w.im = 0 := by
  have hpair : primeLogPhaseClockPair p r (-2 * w.im) =
      primeLogPhaseClockPair p r 0 := Prod.ext
    (phaseClockValue_of_exp_neg_mul_im_eq_zero _ _ h₁)
    (phaseClockValue_of_exp_neg_mul_im_eq_zero _ _ h₂)
  have ht := primeLogPhaseClockPair_injective hp hr hpr hpair
  linarith

/-- Under RH every sampled heat Hankel form is a positive weighted square sum. -/
theorem completeHankelCone_xiHeatGridMoment_of_rh (hRH : RiemannHypothesis)
    {h : ℝ} (hh : 0 < h) (K : ℕ) : CompleteHankelCone (xiHeatGridMoment h K) := by
  rw [completeHankelCone_iff_momentFunctional_square_nonnegative]
  intro p
  rw [momentFunctional_xiHeatGridMoment hh]
  have hnode (q : XiZeroCopy) : xiGaussianHeatTerm h q =
      (Real.exp (-h * (xiSpectralPoint q).re ^ 2) : ℂ) := by
    obtain ⟨x, hz⟩ := xiSpectralPoint_real_of_rh hRH q
    rw [xiGaussianHeatTerm, hz]
    simp only [Complex.ofReal_re, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_pow]
  have hterm (q : XiZeroCopy) :
      xiGaussianHeatTerm h q ^ (2 * K + 1) *
          evalRealPolynomial (p ^ 2) (xiGaussianHeatTerm h q) =
        ((Real.exp (-h * (xiSpectralPoint q).re ^ 2) ^ (2 * K + 1) *
          p.eval (Real.exp (-h * (xiSpectralPoint q).re ^ 2)) ^ 2 : ℝ) : ℂ) := by
    rw [hnode, evalRealPolynomial_ofReal, Polynomial.eval_pow]
    push_cast
    rfl
  rw [tsum_congr hterm, ← Complex.ofReal_tsum, Complex.ofReal_re]
  exact tsum_nonneg fun q => mul_nonneg (by positivity) (sq_nonneg _)

/-- Two prime-log grids, with independently deleted finite prefixes, characterize RH. -/
theorem riemannHypothesis_iff_two_prime_heatGrid {p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) (K L : ℕ) :
    RiemannHypothesis ↔
      CompleteHankelCone (xiHeatGridMoment (Real.log p) K) ∧
      CompleteHankelCone (xiHeatGridMoment (Real.log r) L) := by
  have hp0 : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hr0 : 0 < Real.log r := Real.log_pos (by exact_mod_cast hr.one_lt)
  constructor
  · intro hRH
    exact ⟨completeHankelCone_xiHeatGridMoment_of_rh hRH hp0 K,
      completeHankelCone_xiHeatGridMoment_of_rh hRH hr0 L⟩
  · rintro ⟨h₁, h₂⟩
    by_contra hRH
    obtain ⟨q, hq⟩ := exists_spectralSq_im_pos_of_not_riemannHypothesis hRH
    have hw := im_eq_zero_of_two_prime_exp_real hp hr hpr (xiSpectralPoint q ^ 2)
      (xiGaussianHeatTerm_im_eq_zero_of_grid_nonnegative hp0 K h₁ q)
      (xiGaussianHeatTerm_im_eq_zero_of_grid_nonnegative hr0 L h₂ q)
    exact (ne_of_gt hq) hw

/-- The fixed prime pair `(2,3)` suffices at every pair of finite starting offsets. -/
theorem riemannHypothesis_iff_two_three_heatGrid (K L : ℕ) :
    RiemannHypothesis ↔
      CompleteHankelCone (xiHeatGridMoment (Real.log 2) K) ∧
      CompleteHankelCone (xiHeatGridMoment (Real.log 3) L) :=
  riemannHypothesis_iff_two_prime_heatGrid Nat.prime_two Nat.prime_three (by omega) K L

end

end RHTower
