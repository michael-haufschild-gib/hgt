import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Elementary Gamma-type growth bounds for Mellin tails

The building block for order-one growth estimates of completed zeta functions: the tail integral
`∫_{1}^{∞} t^a e^{-π t} dt` admits the explicit bound `(2a²+9)^a + 1`, whose logarithm has the
Hadamard shape `O((1+a)·log(2+a))`.  The proof is elementary: below `t = 2a²+9` the power factor
is bounded by its endpoint; above it, `log t ≤ 2√t` and `16a² ≤ π²t` force `t^a ≤ e^{πt/2}`, so
half the exponential absorbs the power.  No Stirling asymptotics are used.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- **The pointwise Gamma-type bound.**  For `t ≥ 1` and `a ≥ 0`, the integrand `t^a e^{-πt}` is
dominated by its endpoint value below `t = 2a²+9` and by the half-exponential above it. -/
theorem rpow_mul_exp_neg_pi_le {a t : ℝ} (ha : 0 ≤ a) (ht : 1 ≤ t) :
    t ^ a * Real.exp (-Real.pi * t) ≤
      (2 * a ^ 2 + 9) ^ a * Real.exp (-Real.pi * t) +
        Real.exp (-(Real.pi / 2) * t) := by
  by_cases hM : t ≤ 2 * a ^ 2 + 9
  · have h1 : t ^ a ≤ (2 * a ^ 2 + 9) ^ a :=
      Real.rpow_le_rpow (by linarith) hM ha
    have h2 : (0 : ℝ) ≤ Real.exp (-(Real.pi / 2) * t) := (Real.exp_pos _).le
    have h3 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-Real.pi * t)).le
    linarith
  · have hMt : 2 * a ^ 2 + 9 < t := not_le.mp hM
    have htpos : (0 : ℝ) < t := by linarith
    have hkey : t ^ a ≤ Real.exp (Real.pi / 2 * t) := by
      rw [Real.rpow_def_of_pos htpos]
      apply Real.exp_le_exp.mpr
      have hlog : Real.log t ≤ 2 * Real.sqrt t := by
        have hs : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 :=
          Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr htpos)
        rw [Real.log_sqrt htpos.le] at hs
        linarith
      have hpi2 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
      have hprod : (0 : ℝ) ≤ (Real.pi ^ 2 - 9) * t := mul_nonneg (by linarith) htpos.le
      have hsq : 16 * a ^ 2 ≤ Real.pi ^ 2 * t := by nlinarith [sq_nonneg a]
      have h4a : 4 * a ≤ Real.pi * Real.sqrt t := by
        have h1 : (4 * a) ^ 2 ≤ (Real.pi * Real.sqrt t) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt htpos.le]
          nlinarith
        have h2 : Real.sqrt ((4 * a) ^ 2) ≤ Real.sqrt ((Real.pi * Real.sqrt t) ^ 2) :=
          Real.sqrt_le_sqrt h1
        rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at h2
      calc Real.log t * a = a * Real.log t := mul_comm _ _
        _ ≤ a * (2 * Real.sqrt t) :=
            mul_le_mul_of_nonneg_left hlog ha
        _ = 4 * a * Real.sqrt t / 2 := by ring
        _ ≤ Real.pi * Real.sqrt t * Real.sqrt t / 2 := by
            have := mul_le_mul_of_nonneg_right h4a (Real.sqrt_nonneg t)
            linarith
        _ = Real.pi / 2 * t := by
            rw [mul_assoc, Real.mul_self_sqrt htpos.le]
            ring
    have hconc : t ^ a * Real.exp (-Real.pi * t) ≤ Real.exp (-(Real.pi / 2) * t) := by
      calc t ^ a * Real.exp (-Real.pi * t) ≤
          Real.exp (Real.pi / 2 * t) * Real.exp (-Real.pi * t) :=
            mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le
        _ = Real.exp (-(Real.pi / 2) * t) := by
            rw [← Real.exp_add]
            ring_nf
    have hfirst : (0 : ℝ) ≤ (2 * a ^ 2 + 9) ^ a * Real.exp (-Real.pi * t) := by positivity
    linarith

/-- The Gamma-type tail integrand is integrable on `(1, ∞)`. -/
theorem integrableOn_rpow_mul_exp_neg_pi {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun t : ℝ => t ^ a * Real.exp (-Real.pi * t)) (Ioi 1) := by
  have hmaj : IntegrableOn (fun t : ℝ =>
      (2 * a ^ 2 + 9) ^ a * Real.exp (-Real.pi * t) +
        Real.exp (-(Real.pi / 2) * t)) (Ioi 1) :=
    ((exp_neg_integrableOn_Ioi 1 Real.pi_pos).const_mul ((2 * a ^ 2 + 9) ^ a)).add
      (exp_neg_integrableOn_Ioi 1 (half_pos Real.pi_pos))
  apply hmaj.mono'
  · apply ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    apply ContinuousOn.mul ?_ (Real.continuous_exp.comp (by fun_prop)).continuousOn
    intro t ht
    exact (Real.continuousAt_rpow_const t a
      (Or.inl (ne_of_gt (lt_trans zero_lt_one (mem_Ioi.mp ht))))).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) ≤ t := le_of_lt (mem_Ioi.mp ht)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg (by linarith) a) (Real.exp_pos _).le)]
    exact rpow_mul_exp_neg_pi_le ha ht1

/-- **The Gamma-type tail bound.**  `∫_{1}^{∞} t^a e^{-πt} dt ≤ (2a²+9)^a + 1`: an explicit
order-one Hadamard-shape bound with no Stirling input. -/
theorem integral_rpow_mul_exp_neg_pi_le {a : ℝ} (ha : 0 ≤ a) :
    ∫ t in Ioi (1 : ℝ), t ^ a * Real.exp (-Real.pi * t) ≤ (2 * a ^ 2 + 9) ^ a + 1 := by
  have hint₁ : IntegrableOn (fun t : ℝ =>
      (2 * a ^ 2 + 9) ^ a * Real.exp (-Real.pi * t)) (Ioi 1) :=
    (exp_neg_integrableOn_Ioi 1 Real.pi_pos).const_mul _
  have hint₂ : IntegrableOn (fun t : ℝ => Real.exp (-(Real.pi / 2) * t)) (Ioi 1) :=
    exp_neg_integrableOn_Ioi 1 (half_pos Real.pi_pos)
  have hstep : ∫ t in Ioi (1 : ℝ), t ^ a * Real.exp (-Real.pi * t) ≤
      ∫ t in Ioi (1 : ℝ), ((2 * a ^ 2 + 9) ^ a * Real.exp (-Real.pi * t) +
        Real.exp (-(Real.pi / 2) * t)) :=
    setIntegral_mono_on (integrableOn_rpow_mul_exp_neg_pi ha) (hint₁.add hint₂)
      measurableSet_Ioi (fun t ht => rpow_mul_exp_neg_pi_le ha (le_of_lt (mem_Ioi.mp ht)))
  have hexp : ∀ c : ℝ, 1 ≤ c → 0 < c →
      ∫ t in Ioi (1 : ℝ), Real.exp (-c * t) ≤ 1 := by
    intro c hc hcpos
    have hmono : ∫ t in Ioi (1 : ℝ), Real.exp (-c * t) ≤
        ∫ t in Ioi (1 : ℝ), Real.exp (-t) := by
      have hint₃ : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 1) := by
        have := exp_neg_integrableOn_Ioi (1 : ℝ) one_pos
        simpa only [neg_one_mul] using this
      refine setIntegral_mono_on (exp_neg_integrableOn_Ioi 1 hcpos) hint₃
        measurableSet_Ioi (fun t ht => ?_)
      apply Real.exp_le_exp.mpr
      have ht1 : (1 : ℝ) ≤ t := le_of_lt (mem_Ioi.mp ht)
      nlinarith
    rw [integral_exp_neg_Ioi 1] at hmono
    calc ∫ t in Ioi (1 : ℝ), Real.exp (-c * t) ≤ Real.exp (-1) := hmono
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  rw [integral_add hint₁ hint₂, integral_const_mul] at hstep
  have h1 : ∫ t in Ioi (1 : ℝ), Real.exp (-Real.pi * t) ≤ 1 :=
    hexp Real.pi (by linarith [Real.pi_gt_three]) Real.pi_pos
  have h2 : ∫ t in Ioi (1 : ℝ), Real.exp (-(Real.pi / 2) * t) ≤ 1 :=
    hexp (Real.pi / 2) (by linarith [Real.pi_gt_three]) (half_pos Real.pi_pos)
  have hMpos : (0 : ℝ) ≤ (2 * a ^ 2 + 9) ^ a := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 hMpos]

/-- The logarithm of the Gamma-type tail bound has the Hadamard shape: it is at most
`(1 + a) * (1 + 3 * log (3 + a))`. -/
theorem log_gammaTail_bound_le {a : ℝ} (ha : 0 ≤ a) :
    Real.log ((2 * a ^ 2 + 9) ^ a + 1) ≤ (1 + a) * (1 + 3 * Real.log (3 + a)) := by
  have hMpos : (0 : ℝ) < 2 * a ^ 2 + 9 := by positivity
  have hcube : 2 * a ^ 2 + 9 ≤ (3 + a) ^ 3 := by nlinarith [sq_nonneg a]
  have hbase : (1 : ℝ) ≤ (3 + a) ^ 3 := by nlinarith [sq_nonneg a]
  have hx1 : (1 : ℝ) ≤ ((3 + a) ^ 3) ^ a := by
    calc (1 : ℝ) = (1 : ℝ) ^ a := (Real.one_rpow a).symm
      _ ≤ ((3 + a) ^ 3) ^ a := Real.rpow_le_rpow zero_le_one hbase ha
  have hrpow : (2 * a ^ 2 + 9) ^ a ≤ ((3 + a) ^ 3) ^ a :=
    Real.rpow_le_rpow hMpos.le hcube ha
  have hchain : Real.log ((2 * a ^ 2 + 9) ^ a + 1) ≤
      Real.log (2 * ((3 + a) ^ 3) ^ a) := by
    apply Real.log_le_log (by positivity)
    linarith
  rw [Real.log_mul (by norm_num) (by positivity),
    Real.log_rpow (by positivity), Real.log_pow] at hchain
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogpos : (0 : ℝ) ≤ Real.log (3 + a) := Real.log_nonneg (by linarith)
  calc Real.log ((2 * a ^ 2 + 9) ^ a + 1) ≤
      Real.log 2 + a * ((3 : ℕ) * Real.log (3 + a)) := hchain
    _ ≤ (1 + a) * (1 + 3 * Real.log (3 + a)) := by
        push_cast
        nlinarith

end GaloisForLFunctions.HTGeometry
