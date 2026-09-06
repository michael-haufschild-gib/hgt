import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The sharp constant of the exponential-pole diagonal entry

The self entry of the fixed exponential-pole Weil matrix at aperture `a` is

`A(a) = κ·2sinh a − e^a + (1−2a)e^{−a} + B₁(a) − 2e^a E_M(2a) + 2e^{−a}ψ(e^{2a})`,

with `κ = −γ − log 2π`, `E_M(t) = Σ_{2≤n≤e^t} Λ(n)/n − t`, `ψ` Chebyshev's function, and the
exponentially weighted Gamma boundary mass

`B₁(s) = (e^s/2)∫_0^{2s} e^{−t} L(2t) dt + e^{−s}∫_0^{2s} e^{t}(L(t) − L(2t)/2) dt`,
`L(t) = −log(1 − e^{−t})`.

The first integral has the closed antiderivative `G(e^{−t})` with
`G(u) = (u−1)log(1−u) + (u+1)log(1+u) − 2u`, `G'(u) = log(1−u²)`, `G(1) = 2log 2 − 2`, so
`B₁(s) = (1 − log 2)e^s + O(s e^{−s})`.  Consequently

`A(a) = (2 + γ − log 4π)e^a − 2e^a(E_M(2a) + γ) + 2e^{−a}(ψ(e^{2a}) − e^{2a}) + r(a)`,
`|r(a)| ≤ (10a + 20)e^{−a}` for `a ≥ 1`.

Everything here is elementary real analysis over Mathlib; the identification of the explicit
expression with the corpus's pole matrix entry is a separate bridge.  No zero data, RH premise, or
numerical input enters.
-/

open Real MeasureTheory intervalIntegral Set Filter Topology

namespace RHTower

noncomputable section

/-- The Gamma boundary logarithm `L(t) = −log(1 − e^{−t})`. -/
def poleBoundaryLog (t : ℝ) : ℝ := -Real.log (1 - Real.exp (-t))

theorem poleBoundaryLog_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ poleBoundaryLog t := by
  unfold poleBoundaryLog
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  exact neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith [Real.exp_pos (-t)]))

theorem poleBoundaryLog_two_mul_le {t : ℝ} (ht : 0 ≤ t) :
    poleBoundaryLog (2 * t) ≤ poleBoundaryLog t := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp
  unfold poleBoundaryLog
  have hp : 0 < 1 - Real.exp (-t) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have he : Real.exp (-(2 * t)) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
  exact neg_le_neg (Real.log_le_log hp (by linarith))

/-- `L(t) ≤ 2e^{−t}` once `e^{−t} ≤ 1/2`. -/
theorem poleBoundaryLog_le_two_mul_exp_neg {t : ℝ} (ht : Real.exp (-t) ≤ 1 / 2) :
    poleBoundaryLog t ≤ 2 * Real.exp (-t) := by
  unfold poleBoundaryLog
  have hxpos := Real.exp_pos (-t)
  have hpos : 0 < 1 - Real.exp (-t) := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have : (1 - Real.exp (-t))⁻¹ - 1 ≤ 2 * Real.exp (-t) := by
    rw [inv_eq_one_div, div_sub_one hpos.ne', div_le_iff₀ hpos]
    nlinarith
  linarith

/-- `L(t) ≤ log(1+t) − log t` for `t > 0`, from `e^{−t} ≤ 1/(1+t)`. -/
theorem poleBoundaryLog_le_log_one_add_sub_log {t : ℝ} (ht : 0 < t) :
    poleBoundaryLog t ≤ Real.log (1 + t) - Real.log t := by
  unfold poleBoundaryLog
  have h1 := Real.add_one_le_exp t
  have hexp : Real.exp (-t) ≤ 1 / (1 + t) := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos t) (by linarith)]
    linarith
  have h2 : t / (1 + t) ≤ 1 - Real.exp (-t) := by
    have : 1 - 1 / (1 + t) = t / (1 + t) := by field_simp; ring
    linarith
  have hpos : 0 < t / (1 + t) := by positivity
  have := Real.log_le_log hpos h2
  rw [Real.log_div ht.ne' (by linarith)] at this
  linarith

theorem measurable_poleBoundaryLog : Measurable poleBoundaryLog := by
  unfold poleBoundaryLog
  fun_prop

/-- Interval integrability of `L` across its logarithmic endpoint. -/
theorem intervalIntegrable_poleBoundaryLog {T : ℝ} (hT : 0 < T) :
    IntervalIntegrable poleBoundaryLog volume 0 T := by
  have hdom : IntervalIntegrable (fun t : ℝ => Real.log (1 + T) + |Real.log t|) volume 0 T :=
    intervalIntegrable_const.add intervalIntegrable_log'.abs
  refine hdom.mono_fun measurable_poleBoundaryLog.aestronglyMeasurable ?_
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
  refine Filter.Eventually.of_forall fun t ht => ?_
  rw [uIoc_of_le hT.le] at ht
  have ht0 : 0 < t := ht.1
  have hL := poleBoundaryLog_nonneg ht0.le
  have hlT : 0 ≤ Real.log (1 + T) := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hL,
    abs_of_nonneg (add_nonneg hlT (abs_nonneg _))]
  have h1 := poleBoundaryLog_le_log_one_add_sub_log ht0
  have h2 : Real.log (1 + t) ≤ Real.log (1 + T) := Real.log_le_log (by linarith) (by linarith [ht.2])
  have h3 : -Real.log t ≤ |Real.log t| := neg_le_abs _
  linarith

/-- `∫_0^T L ≤ T + 1`. -/
theorem integral_poleBoundaryLog_le {T : ℝ} (hT : 0 < T) :
    (∫ t in 0..T, poleBoundaryLog t) ≤ T + 1 := by
  have hL := intervalIntegrable_poleBoundaryLog hT
  have hg : IntervalIntegrable (fun t : ℝ => Real.log (1 + t) - Real.log t) volume 0 T := by
    have h1 : IntervalIntegrable (fun t : ℝ => Real.log (1 + t)) volume 0 T := by
      have := (intervalIntegrable_log' (a := 1) (b := 1 + T)).comp_add_right 1
      simpa [add_comm] using this
    exact h1.sub intervalIntegrable_log'
  have hmono : (∫ t in 0..T, poleBoundaryLog t) ≤
      ∫ t in 0..T, (Real.log (1 + t) - Real.log t) := by
    apply intervalIntegral.integral_mono_on hT.le hL hg
    intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | ht0
    · simp [poleBoundaryLog]
    · exact poleBoundaryLog_le_log_one_add_sub_log ht0
  have hval : (∫ t in 0..T, (Real.log (1 + t) - Real.log t)) =
      (1 + T) * Real.log (1 + T) - T * Real.log T := by
    have h1 : (∫ t in 0..T, Real.log (1 + t)) = (1 + T) * Real.log (1 + T) - T := by
      have := intervalIntegral.integral_comp_add_right (a := 0) (b := T) Real.log 1
      simp only [zero_add] at this
      rw [show (fun t : ℝ => Real.log (1 + t)) = fun t => Real.log (t + 1) by
        funext t; rw [add_comm]]
      rw [this, integral_log]
      simp
      ring
    have h2 : (∫ t in 0..T, Real.log t) = T * Real.log T - T := by
      rw [integral_log]; simp
    rw [intervalIntegral.integral_sub (by
        have := (intervalIntegrable_log' (a := 1) (b := 1 + T)).comp_add_right 1
        simpa [add_comm] using this) intervalIntegrable_log', h1, h2]
    ring
  rw [hval] at hmono
  -- `(1+T)log(1+T) − T log T = log(1+T) + T(log(1+T) − log T) ≤ T + 1`
  have hlogT : Real.log (1 + T) ≤ T := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + T by linarith); linarith
  have hratio : Real.log (1 + T) - Real.log T ≤ 1 / T := by
    rw [← Real.log_div (by linarith) hT.ne']
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < (1 + T) / T by positivity)
    have e : (1 + T) / T - 1 = 1 / T := by field_simp; ring
    linarith
  have : T * (Real.log (1 + T) - Real.log T) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hratio hT.le
    rw [mul_one_div, div_self hT.ne'] at this
    exact this
  nlinarith

/-- `G(u) = (u−1)log(1−u) + (u+1)log(1+u) − 2u`, with `G'(u) = log(1−u²)` on `(0,1)`. -/
def poleSelfKernelPrimitive (u : ℝ) : ℝ :=
  (u - 1) * Real.log (1 - u) + (u + 1) * Real.log (1 + u) - 2 * u

theorem hasDerivAt_poleSelfKernelPrimitive {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt poleSelfKernelPrimitive (Real.log (1 - u ^ 2)) u := by
  have h1 : HasDerivAt (fun u : ℝ => 1 - u) (-1) u := by
    simpa using (hasDerivAt_id u).const_sub (1 : ℝ)
  have h2 : HasDerivAt (fun u : ℝ => 1 + u) 1 u := by
    simpa using (hasDerivAt_id u).const_add (1 : ℝ)
  have hl1 : HasDerivAt (fun u : ℝ => Real.log (1 - u)) ((-1) / (1 - u)) u :=
    h1.log (by linarith)
  have hl2 : HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + u)) u :=
    h2.log (by linarith)
  have hA : HasDerivAt (fun u : ℝ => (u - 1) * Real.log (1 - u))
      (1 * Real.log (1 - u) + (u - 1) * ((-1) / (1 - u))) u :=
    ((hasDerivAt_id u).sub_const 1).mul hl1
  have hB : HasDerivAt (fun u : ℝ => (u + 1) * Real.log (1 + u))
      (1 * Real.log (1 + u) + (u + 1) * (1 / (1 + u))) u :=
    ((hasDerivAt_id u).add_const 1).mul hl2
  have hC : HasDerivAt (fun u : ℝ => 2 * u) 2 u := by
    simpa using (hasDerivAt_id u).const_mul (2 : ℝ)
  have key : poleSelfKernelPrimitive =
      fun u => (u - 1) * Real.log (1 - u) + (u + 1) * Real.log (1 + u) - 2 * u := rfl
  rw [key]
  have hne1 : (1 - u) ≠ 0 := by linarith
  have hne2 : (1 + u) ≠ 0 := by linarith
  refine ((hA.add hB).sub hC).congr_deriv ?_
  rw [show (1 : ℝ) - u ^ 2 = (1 - u) * (1 + u) by ring, Real.log_mul hne1 hne2]
  field_simp
  ring

/-- `F(t) = G(e^{−t})`, an antiderivative of `e^{−t} L(2t)` on `(0,∞)`. -/
def poleSelfKernelAntiderivative (t : ℝ) : ℝ := poleSelfKernelPrimitive (Real.exp (-t))

theorem hasDerivAt_poleSelfKernelAntiderivative {t : ℝ} (ht : 0 < t) :
    HasDerivAt poleSelfKernelAntiderivative (Real.exp (-t) * poleBoundaryLog (2 * t)) t := by
  have hu : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) t := by
    have := ((hasDerivAt_id t).neg).exp
    exact this.congr_deriv (by simp)
  have hG := hasDerivAt_poleSelfKernelPrimitive (Real.exp_pos (-t))
    (Real.exp_lt_one_iff.mpr (by linarith))
  have hcomp := hG.comp t hu
  have key : poleSelfKernelAntiderivative = poleSelfKernelPrimitive ∘ fun t => Real.exp (-t) := rfl
  rw [key]
  refine hcomp.congr_deriv ?_
  unfold poleBoundaryLog
  rw [show Real.exp (-(2 * t)) = Real.exp (-t) ^ 2 by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf]
  ring

theorem continuous_poleSelfKernelAntiderivative : Continuous poleSelfKernelAntiderivative := by
  have key : poleSelfKernelAntiderivative = fun t =>
      -((1 - Real.exp (-t)) * Real.log (1 - Real.exp (-t))) +
        (Real.exp (-t) + 1) * Real.log (1 + Real.exp (-t)) - 2 * Real.exp (-t) := by
    funext t
    unfold poleSelfKernelAntiderivative poleSelfKernelPrimitive
    ring
  rw [key]
  have he : Continuous fun t : ℝ => Real.exp (-t) := Real.continuous_exp.comp continuous_neg
  have h1 : Continuous fun t : ℝ => (1 - Real.exp (-t)) * Real.log (1 - Real.exp (-t)) :=
    Real.continuous_mul_log.comp (continuous_const.sub he)
  have h2 : Continuous fun t : ℝ => Real.log (1 + Real.exp (-t)) :=
    (continuous_const.add he).log (fun t => by
      show (1 : ℝ) + Real.exp (-t) ≠ 0
      positivity)
  exact (h1.neg.add ((he.add continuous_const).mul h2)).sub (continuous_const.mul he)

theorem poleSelfKernelAntiderivative_zero :
    poleSelfKernelAntiderivative 0 = 2 * Real.log 2 - 2 := by
  unfold poleSelfKernelAntiderivative poleSelfKernelPrimitive
  simp only [neg_zero, Real.exp_zero, sub_self, zero_mul, zero_add]
  norm_num

/-- Closed form: `∫_0^{2s} e^{−t} L(2t) dt = F(2s) − (2 log 2 − 2)`. -/
theorem integral_exp_neg_mul_poleBoundaryLog_two_mul {s : ℝ} (hs : 0 < s) :
    (∫ t in 0..2 * s, Real.exp (-t) * poleBoundaryLog (2 * t)) =
      poleSelfKernelAntiderivative (2 * s) - (2 * Real.log 2 - 2) := by
  have hL2 : IntervalIntegrable (fun t => poleBoundaryLog (2 * t)) volume 0 (2 * s) := by
    have h := (intervalIntegrable_poleBoundaryLog (show 0 < 4 * s by linarith)).comp_mul_left
      (c := 2)
    rw [show (0:ℝ) / 2 = 0 by norm_num, show 4 * s / 2 = 2 * s by ring] at h
    exact h
  have hint : IntervalIntegrable (fun t => Real.exp (-t) * poleBoundaryLog (2 * t))
      volume 0 (2 * s) :=
    hL2.continuousOn_mul (Real.continuous_exp.comp continuous_neg).continuousOn
  have ha : Tendsto poleSelfKernelAntiderivative (𝓝[>] 0) (𝓝 (2 * Real.log 2 - 2)) := by
    have := continuous_poleSelfKernelAntiderivative.tendsto 0
    rw [poleSelfKernelAntiderivative_zero] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have hb : Tendsto poleSelfKernelAntiderivative (𝓝[<] (2 * s))
      (𝓝 (poleSelfKernelAntiderivative (2 * s))) :=
    tendsto_nhdsWithin_of_tendsto_nhds (continuous_poleSelfKernelAntiderivative.tendsto _)
  exact integral_eq_sub_of_hasDerivAt_of_tendsto (by linarith)
    (fun x hx => hasDerivAt_poleSelfKernelAntiderivative hx.1) hint ha hb

/-- `|G(u)| ≤ 6u` on `[0, 1/2]`. -/
theorem abs_poleSelfKernelPrimitive_le {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    |poleSelfKernelPrimitive u| ≤ 6 * u := by
  unfold poleSelfKernelPrimitive
  have hpos : 0 < 1 - u := by linarith
  have hl1a : Real.log (1 - u) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hl1b : -(2 * u) ≤ Real.log (1 - u) := by
    have h := Real.one_sub_inv_le_log_of_pos hpos
    have hinv : (1 - u)⁻¹ ≤ 1 + 2 * u := by
      rw [inv_le_iff_one_le_mul₀ hpos]
      nlinarith
    linarith
  have hl2a : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
  have hl2b : Real.log (1 + u) ≤ u := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + u by linarith)
    linarith
  have hA1 : 0 ≤ (u - 1) * Real.log (1 - u) := by nlinarith
  have hA2 : (u - 1) * Real.log (1 - u) ≤ 2 * u := by nlinarith
  have hB1 : 0 ≤ (u + 1) * Real.log (1 + u) := by nlinarith
  have hB2 : (u + 1) * Real.log (1 + u) ≤ 3 / 2 * u := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith

/-- Pointwise bound `e^t L(t) ≤ 2 L(t) + 2` on the nonnegative ray. -/
theorem exp_mul_poleBoundaryLog_le {t : ℝ} (ht : 0 ≤ t) :
    Real.exp t * poleBoundaryLog t ≤ 2 * poleBoundaryLog t + 2 := by
  have hL := poleBoundaryLog_nonneg ht
  rcases le_or_gt (Real.exp t) 2 with h2 | h2
  · nlinarith
  · have hx : Real.exp (-t) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos t) (by norm_num)]
      linarith
    have hL2 := poleBoundaryLog_le_two_mul_exp_neg hx
    have hprod : Real.exp t * Real.exp (-t) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have : Real.exp t * poleBoundaryLog t ≤ 2 := by
      calc Real.exp t * poleBoundaryLog t ≤ Real.exp t * (2 * Real.exp (-t)) :=
            mul_le_mul_of_nonneg_left hL2 (Real.exp_pos t).le
        _ = 2 := by rw [mul_left_comm, hprod, mul_one]
    linarith

/-- The exponentially weighted difference integral `J(s)`. -/
def poleSelfDifferenceIntegral (s : ℝ) : ℝ :=
  ∫ t in 0..2 * s, Real.exp t * (poleBoundaryLog t - poleBoundaryLog (2 * t) / 2)

theorem poleSelfDifferenceIntegral_bounds {s : ℝ} (hs : 0 < s) :
    0 ≤ poleSelfDifferenceIntegral s ∧ poleSelfDifferenceIntegral s ≤ 8 * s + 2 := by
  unfold poleSelfDifferenceIntegral
  have hL := intervalIntegrable_poleBoundaryLog (show 0 < 2 * s by linarith)
  have hL2 : IntervalIntegrable (fun t => poleBoundaryLog (2 * t)) volume 0 (2 * s) := by
    have h := (intervalIntegrable_poleBoundaryLog (show 0 < 4 * s by linarith)).comp_mul_left
      (c := 2)
    rw [show (0:ℝ) / 2 = 0 by norm_num, show 4 * s / 2 = 2 * s by ring] at h
    exact h
  have hec : ContinuousOn Real.exp (uIcc 0 (2 * s)) := Real.continuous_exp.continuousOn
  have hint : IntervalIntegrable (fun t => Real.exp t *
      (poleBoundaryLog t - poleBoundaryLog (2 * t) / 2)) volume 0 (2 * s) :=
    ((hL.sub (hL2.const_mul (1 / 2))).continuousOn_mul hec).congr
      (fun t _ => by
        show Real.exp t * (poleBoundaryLog t - 1 / 2 * poleBoundaryLog (2 * t)) =
          Real.exp t * (poleBoundaryLog t - poleBoundaryLog (2 * t) / 2)
        ring)
  have hint2 : IntervalIntegrable (fun t => 2 * poleBoundaryLog t + 2) volume 0 (2 * s) :=
    (hL.const_mul 2).add intervalIntegrable_const
  constructor
  · apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    have h1 := poleBoundaryLog_two_mul_le ht.1
    have h2 := poleBoundaryLog_nonneg ht.1
    have := Real.exp_pos t
    nlinarith
  · calc (∫ t in 0..2 * s, Real.exp t * (poleBoundaryLog t - poleBoundaryLog (2 * t) / 2))
        ≤ ∫ t in 0..2 * s, (2 * poleBoundaryLog t + 2) := by
          apply intervalIntegral.integral_mono_on (by linarith) hint hint2
          intro t ht
          have h1 := poleBoundaryLog_nonneg (show 0 ≤ 2 * t by linarith [ht.1])
          have h3 := exp_mul_poleBoundaryLog_le ht.1
          have := Real.exp_pos t
          nlinarith
      _ = 2 * (∫ t in 0..2 * s, poleBoundaryLog t) + 2 * (2 * s) := by
          rw [intervalIntegral.integral_add (hL.const_mul 2) intervalIntegrable_const,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
          simp only [smul_eq_mul, sub_zero]
          ring
      _ ≤ 8 * s + 2 := by
          have := integral_poleBoundaryLog_le (show 0 < 2 * s by linarith)
          linarith

/-- The exponentially weighted Gamma boundary mass in its fixed-endpoint primitive form. -/
def poleSelfBoundaryPrimitive (s : ℝ) : ℝ :=
  Real.exp s / 2 * (∫ t in 0..2 * s, Real.exp (-t) * poleBoundaryLog (2 * t)) +
    Real.exp (-s) * ∫ t in 0..2 * s,
      Real.exp t * (poleBoundaryLog t - poleBoundaryLog (2 * t) / 2)

/-- Exact decomposition `B₁(s) = (1 − log 2)e^s + (e^s/2)F(2s) + e^{−s}J(s)`. -/
theorem poleSelfBoundaryPrimitive_eq {s : ℝ} (hs : 0 < s) :
    poleSelfBoundaryPrimitive s = (1 - Real.log 2) * Real.exp s +
      Real.exp s / 2 * poleSelfKernelAntiderivative (2 * s) +
      Real.exp (-s) * poleSelfDifferenceIntegral s := by
  unfold poleSelfBoundaryPrimitive poleSelfDifferenceIntegral
  rw [integral_exp_neg_mul_poleBoundaryLog_two_mul hs]
  ring

/-- `|B₁(s) − (1 − log 2)e^s| ≤ (8s + 5)e^{−s}` for `s ≥ 1`. -/
theorem abs_poleSelfBoundaryPrimitive_sub_le {s : ℝ} (hs : 1 ≤ s) :
    |poleSelfBoundaryPrimitive s - (1 - Real.log 2) * Real.exp s| ≤
      (8 * s + 5) * Real.exp (-s) := by
  rw [poleSelfBoundaryPrimitive_eq (by linarith)]
  have hes := Real.exp_pos s
  have hens := Real.exp_pos (-s)
  have hprod : Real.exp s * Real.exp (-s) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hu0 : 0 ≤ Real.exp (-(2 * s)) := (Real.exp_pos _).le
  have hu : Real.exp (-(2 * s)) ≤ 1 / 2 := by
    have h1 : Real.exp (-(2 * s)) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-2) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]
      have := Real.add_one_le_exp (2 : ℝ)
      linarith
    linarith
  have hF : |poleSelfKernelAntiderivative (2 * s)| ≤ 6 * Real.exp (-(2 * s)) :=
    abs_poleSelfKernelPrimitive_le hu0 hu
  have he2 : Real.exp (-(2 * s)) = Real.exp (-s) * Real.exp (-s) := by
    rw [← Real.exp_add]; ring_nf
  have hFe : Real.exp s / 2 * |poleSelfKernelAntiderivative (2 * s)| ≤ 3 * Real.exp (-s) := by
    have h := mul_le_mul_of_nonneg_left hF (show 0 ≤ Real.exp s / 2 by positivity)
    rw [he2] at h
    calc Real.exp s / 2 * |poleSelfKernelAntiderivative (2 * s)|
        ≤ Real.exp s / 2 * (6 * (Real.exp (-s) * Real.exp (-s))) := h
      _ = 3 * Real.exp (-s) := by nlinarith [hprod]
  obtain ⟨hJ0, hJ⟩ := poleSelfDifferenceIntegral_bounds (show 0 < s by linarith)
  have hJ' : Real.exp (-s) * poleSelfDifferenceIntegral s ≤ (8 * s + 2) * Real.exp (-s) := by
    nlinarith [mul_le_mul_of_nonneg_left hJ hens.le]
  have hJ'' : 0 ≤ Real.exp (-s) * poleSelfDifferenceIntegral s := mul_nonneg hens.le hJ0
  calc |(1 - Real.log 2) * Real.exp s + Real.exp s / 2 * poleSelfKernelAntiderivative (2 * s) +
          Real.exp (-s) * poleSelfDifferenceIntegral s - (1 - Real.log 2) * Real.exp s|
      = |Real.exp s / 2 * poleSelfKernelAntiderivative (2 * s) +
          Real.exp (-s) * poleSelfDifferenceIntegral s| := by ring_nf
    _ ≤ |Real.exp s / 2 * poleSelfKernelAntiderivative (2 * s)| +
          |Real.exp (-s) * poleSelfDifferenceIntegral s| := abs_add_le _ _
    _ ≤ 3 * Real.exp (-s) + (8 * s + 2) * Real.exp (-s) := by
        gcongr
        · rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < Real.exp s / 2)]
          exact hFe
        · rw [abs_of_nonneg hJ'']
          exact hJ'
    _ = (8 * s + 5) * Real.exp (-s) := by ring

/-! ## The diagonal entry -/

/-- Cumulative reciprocal von Mangoldt sum `Σ_{2≤n≤X} Λ(n)/n`. -/
def reciprocalMangoldtCumulative (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n / n

/-- Reciprocal Mangoldt error `E_M(t) = Σ_{2≤n≤e^t} Λ(n)/n − t`. -/
def reciprocalMangoldtError (t : ℝ) : ℝ := reciprocalMangoldtCumulative (Real.exp t) - t

/-- The explicit diagonal entry of the fixed exponential-pole Weil matrix. -/
def poleDiagonalExplicit (a : ℝ) : ℝ :=
  (-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)) * (2 * Real.sinh a) -
    Real.exp a + (1 - 2 * a) * Real.exp (-a) + poleSelfBoundaryPrimitive a -
    2 * Real.exp a * reciprocalMangoldtError (2 * a) +
    2 * Real.exp (-a) * Chebyshev.psi (Real.exp (2 * a))

/-- The sharp constant `2 + γ − log 4π` (on paper `Σ_ρ 1/(ρ(1−ρ))`). -/
def poleSharpConstant : ℝ := 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)

/-- Remainder after the sharp main term and the two prime errors. -/
def poleDiagonalRemainder (s : ℝ) : ℝ :=
  (1 - 2 * s - (-Real.eulerMascheroniConstant - Real.log (2 * Real.pi))) * Real.exp (-s) +
    (poleSelfBoundaryPrimitive s - (1 - Real.log 2) * Real.exp s)

/-- **Exact constant-level decomposition of the diagonal entry.** -/
theorem poleDiagonalExplicit_eq_sharp (a : ℝ) :
    poleDiagonalExplicit a =
      poleSharpConstant * Real.exp a -
        2 * Real.exp a * (reciprocalMangoldtError (2 * a) + Real.eulerMascheroniConstant) +
        2 * Real.exp (-a) * (Chebyshev.psi (Real.exp (2 * a)) - Real.exp (2 * a)) +
        poleDiagonalRemainder a := by
  unfold poleDiagonalExplicit poleSharpConstant poleDiagonalRemainder
  have h4 : Real.log (4 * Real.pi) = Real.log 2 + Real.log (2 * Real.pi) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    ring_nf
  have h2a : Real.exp (2 * a) = Real.exp a * Real.exp a := by
    rw [← Real.exp_add]; ring_nf
  have hprod : Real.exp a * Real.exp (-a) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [h4, Real.sinh_eq, h2a]
  have := Real.exp_pos a
  have hn := Real.exp_pos (-a)
  nlinarith [hprod]

/-- `|r(s)| ≤ (10s + 20)e^{−s}` for `s ≥ 1`. -/
theorem abs_poleDiagonalRemainder_le {s : ℝ} (hs : 1 ≤ s) :
    |poleDiagonalRemainder s| ≤ (10 * s + 20) * Real.exp (-s) := by
  unfold poleDiagonalRemainder
  have hγ1 := Real.one_half_lt_eulerMascheroniConstant
  have hγ2 := Real.eulerMascheroniConstant_lt_two_thirds
  have hpi1 := Real.pi_gt_three
  have hpi2 := Real.pi_le_four
  have hlogpi : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hlogpi' : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith)
  have hens := Real.exp_pos (-s)
  have hlin : |(1 - 2 * s - (-Real.eulerMascheroniConstant - Real.log (2 * Real.pi))) *
      Real.exp (-s)| ≤ (2 * s + 9) * Real.exp (-s) := by
    rw [abs_mul, abs_of_pos hens]
    apply mul_le_mul_of_nonneg_right _ hens.le
    rw [abs_le]
    constructor <;> linarith
  have hB := abs_poleSelfBoundaryPrimitive_sub_le hs
  calc |(1 - 2 * s - (-Real.eulerMascheroniConstant - Real.log (2 * Real.pi))) * Real.exp (-s) +
          (poleSelfBoundaryPrimitive s - (1 - Real.log 2) * Real.exp s)|
      ≤ |(1 - 2 * s - (-Real.eulerMascheroniConstant - Real.log (2 * Real.pi))) * Real.exp (-s)| +
          |poleSelfBoundaryPrimitive s - (1 - Real.log 2) * Real.exp s| := abs_add_le _ _
    _ ≤ (2 * s + 9) * Real.exp (-s) + (8 * s + 5) * Real.exp (-s) := by gcongr
    _ ≤ (10 * s + 20) * Real.exp (-s) := by nlinarith

/-- **Sharp asymptotic form of the diagonal entry**: the distance of `A(a)e^{−a}` from
`2 + γ − log 4π` is controlled by the two prime errors and an exponentially small term. -/
theorem abs_poleDiagonalExplicit_div_exp_sub_sharp_le {a : ℝ} (ha : 1 ≤ a) :
    |poleDiagonalExplicit a / Real.exp a - poleSharpConstant| ≤
      2 * |reciprocalMangoldtError (2 * a) + Real.eulerMascheroniConstant| +
        2 * Real.exp (-(2 * a)) * |Chebyshev.psi (Real.exp (2 * a)) - Real.exp (2 * a)| +
        (10 * a + 20) * Real.exp (-(2 * a)) := by
  have hes := Real.exp_pos a
  have hr := abs_poleDiagonalRemainder_le ha
  have h2 : Real.exp (-(2 * a)) * Real.exp a = Real.exp (-a) := by
    rw [← Real.exp_add]; ring_nf
  have hkey : poleDiagonalExplicit a / Real.exp a - poleSharpConstant =
      -(2 * (reciprocalMangoldtError (2 * a) + Real.eulerMascheroniConstant)) +
        2 * Real.exp (-(2 * a)) * (Chebyshev.psi (Real.exp (2 * a)) - Real.exp (2 * a)) +
        poleDiagonalRemainder a / Real.exp a := by
    rw [poleDiagonalExplicit_eq_sharp a]
    have h3 : Real.exp (-a) = Real.exp (-(2 * a)) * Real.exp a := h2.symm
    rw [h3]
    field_simp
    ring
  rw [hkey]
  have hrem : |poleDiagonalRemainder a / Real.exp a| ≤ (10 * a + 20) * Real.exp (-(2 * a)) := by
    rw [abs_div, abs_of_pos hes, div_le_iff₀ hes]
    calc |poleDiagonalRemainder a| ≤ (10 * a + 20) * Real.exp (-a) := hr
      _ = (10 * a + 20) * Real.exp (-(2 * a)) * Real.exp a := by rw [mul_assoc, h2]
  calc |-(2 * (reciprocalMangoldtError (2 * a) + Real.eulerMascheroniConstant)) +
          2 * Real.exp (-(2 * a)) * (Chebyshev.psi (Real.exp (2 * a)) - Real.exp (2 * a)) +
          poleDiagonalRemainder a / Real.exp a|
      ≤ |-(2 * (reciprocalMangoldtError (2 * a) + Real.eulerMascheroniConstant))| +
          |2 * Real.exp (-(2 * a)) * (Chebyshev.psi (Real.exp (2 * a)) - Real.exp (2 * a))| +
          |poleDiagonalRemainder a / Real.exp a| := abs_add_three _ _ _
    _ ≤ 2 * |reciprocalMangoldtError (2 * a) + Real.eulerMascheroniConstant| +
          2 * Real.exp (-(2 * a)) * |Chebyshev.psi (Real.exp (2 * a)) - Real.exp (2 * a)| +
          (10 * a + 20) * Real.exp (-(2 * a)) := by
        gcongr
        · rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        · rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2),
            abs_of_pos (Real.exp_pos _)]

end

end RHTower
