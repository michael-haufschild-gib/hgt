import GaloisForLFunctions.RHTower.XiMassTwoRapiditySourceOrderNoGo
import GaloisForLFunctions.RHTower.XiMassTwoRapiditySaddlePolarity

/-!
# Positive stationary `2 × 3` prime cell

For positive mass coefficient, the literal prime weights and correlation amplitude
are positive real scalars.  The timelike `2 × 3` stationary phase tends to zero
from above as the common mass grows.  Hence that labelled stationary cell is
eventually positive in real part.  A cancellation of the full covariance must
therefore involve other labelled cells or nonstationary regions.
-/

namespace RHTower

noncomputable section

/-- A genuinely prime literal rapidity weight has positive real part at positive mass. -/
theorem xiMassCriticalPrimeConeRapidityWeight_re_pos_of_prime {a : ℝ} (ha : 0 < a) {n : ℕ}
    (hn : (n + 2).Prime) :
    0 < (xiMassCriticalPrimeConeRapidityWeight a n).re := by
  unfold xiMassCriticalPrimeConeRapidityWeight
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [ArithmeticFunction.vonMangoldt_apply_prime hn]
  have hlog : 0 < Real.log ((n + 2 : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hn.one_lt
  have hcast : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by norm_num
  rw [hcast] at hlog ⊢
  positivity

private theorem xiMassCriticalPrimeConeRapidityWeight_eq_ofReal (a : ℝ) (n : ℕ) :
    xiMassCriticalPrimeConeRapidityWeight a n =
      ((ArithmeticFunction.vonMangoldt (n + 2) *
        Real.exp (-Real.log ((n : ℝ) + 2) / 2) * a : ℝ) : ℂ) := by
  unfold xiMassCriticalPrimeConeRapidityWeight
  push_cast
  ring

private theorem xiMassTwoRapidityCorrelationAmplitude_eq_ofReal (a sigma t s : ℝ) :
    xiMassTwoRapidityCorrelationAmplitude a sigma t s =
      ((Real.cosh t * Real.exp (-(a * sigma) * Real.cosh t) *
        Real.cosh s * Real.exp (-(a * sigma) * Real.cosh s) : ℝ) : ℂ) := rfl

/-- The real part of a literal labelled covariance term is its positive scalar factor times
the cosine of its correlation phase. -/
theorem xiMassCriticalPrimeConeTwoRapidityTerm_re_eq
    (a sigma u : ℝ) (i j : ℕ) (t s : ℝ) :
    (xiMassCriticalPrimeConeTwoRapidityTerm a sigma u i j t s).re =
      (xiMassCriticalPrimeConeRapidityWeight a i).re *
        (xiMassCriticalPrimeConeRapidityWeight a j).re *
          (xiMassTwoRapidityCorrelationAmplitude a sigma t s).re *
            Real.cos (a * xiMassTwoRapidityCorrelationPhase u
              (Real.log ((i : ℝ) + 2)) (Real.log ((j : ℝ) + 2)) t s) := by
  unfold xiMassCriticalPrimeConeTwoRapidityTerm
  rw [xiMassCriticalPrimeConeRapidityWeight_eq_ofReal,
    xiMassCriticalPrimeConeRapidityWeight_eq_ofReal,
    xiMassTwoRapidityCorrelationAmplitude_eq_ofReal]
  simp only [Complex.conj_ofReal, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul, add_zero]
  rw [show -(Complex.I *
      ((a * xiMassTwoRapidityCorrelationPhase u (Real.log ((i : ℝ) + 2))
        (Real.log ((j : ℝ) + 2)) t s : ℝ) : ℂ)) =
        ((-(a * xiMassTwoRapidityCorrelationPhase u (Real.log ((i : ℝ) + 2))
          (Real.log ((j : ℝ) + 2)) t s) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re]
  rw [Real.cos_neg]

/-- At sufficiently deep common mass, the stationary literal `2 × 3` cell has positive real
part.  This is pointwise in the stationary pair, not a claim about the integrated covariance. -/
theorem xiMassCriticalPrimeCone_two_three_timelike_stationary_term_re_pos
    {a sigma u : ℝ} (ha : 0 < a) (hu : 0 < u)
    (hlog2 : 0 ≤ Real.log 2) (hlog3 : 0 ≤ Real.log 3)
    (h23 : Real.log 2 < Real.log 3)
    (h2u : Real.log 2 < u) (h3u : Real.log 3 < u)
    (hdeep : 2 * Real.log 3 ≤ u)
    (hphase : a * (2 * (Real.log 3) ^ (2 : ℕ) / u) < Real.pi / 2) :
    0 < (xiMassCriticalPrimeConeTwoRapidityTerm a sigma u 0 1
      (-timelikeRapidity u (Real.log 2))
      (-timelikeRapidity u (Real.log 3))).re := by
  have hPhi :
      0 < xiMassTwoRapidityCorrelationPhase u (Real.log 2) (Real.log 3)
        (-timelikeRapidity u (Real.log 2)) (-timelikeRapidity u (Real.log 3)) :=
    xiMassTwoRapidityCorrelationPhase_at_timelike_stationary_pos hu hlog2 hlog3 h2u h3u h23
  have hPhi_le :
      xiMassTwoRapidityCorrelationPhase u (Real.log 2) (Real.log 3)
        (-timelikeRapidity u (Real.log 2)) (-timelikeRapidity u (Real.log 3)) ≤
        2 * (Real.log 3) ^ (2 : ℕ) / u :=
    xiMassTwoRapidityCorrelationPhase_at_timelike_stationary_le
      hu hlog2 hlog3 h2u h3u h23 hdeep
  have hcos : 0 < Real.cos (a * xiMassTwoRapidityCorrelationPhase u
      (Real.log 2) (Real.log 3)
      (-timelikeRapidity u (Real.log 2)) (-timelikeRapidity u (Real.log 3))) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [Real.pi_pos, mul_pos ha hPhi]
    · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hPhi_le ha.le) hphase
  rw [xiMassCriticalPrimeConeTwoRapidityTerm_re_eq]
  norm_num
  exact mul_pos (mul_pos
    (mul_pos (xiMassCriticalPrimeConeRapidityWeight_re_pos_of_prime ha (by norm_num))
      (xiMassCriticalPrimeConeRapidityWeight_re_pos_of_prime ha (by norm_num)))
    (xiMassTwoRapidityCorrelationAmplitude_re_pos a sigma _ _)) hcos

/-- **Cofinal stationary-cell positivity.**  For every positive mass coefficient, the literal
timelike `2 × 3` stationary cell has positive real part at all sufficiently large common masses. -/
theorem eventually_xiMassCriticalPrimeCone_two_three_timelike_stationary_term_re_pos
    {a sigma : ℝ} (ha : 0 < a) :
    ∀ᶠ u : ℝ in Filter.atTop,
      0 < (xiMassCriticalPrimeConeTwoRapidityTerm a sigma u 0 1
        (-timelikeRapidity u (Real.log 2))
        (-timelikeRapidity u (Real.log 3))).re := by
  have hsmall : Filter.Tendsto
      (fun u : ℝ => (2 * a * (Real.log 3) ^ (2 : ℕ)) / u)
      Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  have hphase : ∀ᶠ u : ℝ in Filter.atTop,
      a * (2 * (Real.log 3) ^ (2 : ℕ) / u) < Real.pi / 2 := by
    have h := hsmall.eventually (Iio_mem_nhds (half_pos Real.pi_pos))
    filter_upwards [h] with u hu
    simpa only [← mul_div_assoc, mul_assoc, mul_left_comm, mul_comm] using hu
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h23 : Real.log 2 < Real.log 3 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [Filter.eventually_gt_atTop (2 * Real.log 3),
    Filter.eventually_gt_atTop (Real.log 3), hphase] with u hdeep h3u hphase
  exact xiMassCriticalPrimeCone_two_three_timelike_stationary_term_re_pos ha
    (lt_trans (Real.log_pos (by norm_num)) h3u) hlog2 hlog3 h23
    (h23.trans h3u) h3u hdeep.le hphase

end

end RHTower
