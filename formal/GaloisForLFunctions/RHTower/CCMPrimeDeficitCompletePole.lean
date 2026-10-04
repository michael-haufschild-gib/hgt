import GaloisForLFunctions.RHTower.CCMPrimeDeficitDivisorQuadrature
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import GaloisForLFunctions.RHTower.CCMPrimeDeficitDivisorSourceEntry

/-!
# Complete exponential pole of the actual divisor source

The complete force/floor quadrature gives `H(T) = exp(T) * (c*T+d) + R(T)`
with one globally polynomial remainder. Its negative-time values retain
all causal boundary terms. The full signed finite form has exactly the
pole `exp(T) * ((c*T+d)*m0^2 - 2*c*m0*m1)`.

Thus harmonic-neutral packets remove the entire exponential contribution,
including with moving labels beyond the square-root horizon. The uniform
remainder estimate retains the square of absolute coefficient mass; no
native arithmetic energy bound is claimed.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped BigOperators
namespace RHTower

private def poleForce (t : ℝ) : ℝ :=
  ccmPrimeDeficitDilationForce t - (Real.eulerMascheroniConstant + 1) * Real.exp t

private def poleFloor (t : ℝ) : ℝ := Int.fract (Real.exp t)

private def forceBudget : ℝ := 2 + |Real.log (2 * Real.pi) / 2|

private theorem forceBudget_nonneg : 0 ≤ forceBudget := by
  unfold forceBudget
  positivity

private theorem force_local {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable poleForce volume 0 T :=
  (intervalIntegrable_ccmPrimeDeficitDilationForce hT).sub
    ((Real.continuous_exp.const_mul _).intervalIntegrable 0 T)

private theorem force_bound {t : ℝ} (ht : 0 ≤ t) :
    |poleForce t| ≤ forceBudget * (t + 1) := by
  have h := abs_ccmPrimeDeficitDilationForce_centered_le ht
  have hs := abs_sub (poleForce t + Real.log (2 * Real.pi) / 2)
    (Real.log (2 * Real.pi) / 2)
  rw [add_sub_cancel_right] at hs
  change |poleForce t + Real.log (2 * Real.pi) / 2| ≤ t / 2 + 2 at h
  have hb := mul_nonneg ht (abs_nonneg (Real.log (2 * Real.pi) / 2))
  unfold forceBudget
  nlinarith only [h, hs, hb, ht]

private theorem floor_local {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable poleFloor volume 0 T := by
  change IntervalIntegrable (fun s => Int.fract (Real.exp s)) volume 0 T
  simpa only [one_mul] using
    intervalIntegrable_reverse_mul_fract_exp (fun _ => (1 : ℝ)) intervalIntegrable_const hT

private theorem floor_bound {t : ℝ} (ht : 0 ≤ t) : |poleFloor t| ≤ 1 * (t + 1) := by
  rw [poleFloor, abs_of_nonneg (Int.fract_nonneg _)]
  linarith only [Int.fract_lt_one (Real.exp t), ht]

private def poleEnvelope (B t : ℝ) : ℝ := B * Real.exp (-t) * (t + 1)

private theorem envelope_derivative (B t : ℝ) :
    HasDerivAt (fun t : ℝ => -(B * Real.exp (-t) * (t + 2))) (poleEnvelope B t) t := by
  convert! (((((hasDerivAt_id t).neg).exp).const_mul B).mul
    ((hasDerivAt_id t).add_const 2)).neg using 1
  simp only [id_eq, Pi.neg_apply, poleEnvelope]
  ring

private theorem envelope_tendsto (B : ℝ) :
    Tendsto (fun t : ℝ => -(B * Real.exp (-t) * (t + 2))) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).add
    ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).mul_const 2)
  have h' : Tendsto (fun t : ℝ => Real.exp (-t) * (t + 2)) atTop (𝓝 0) := by
    simpa only [pow_one, pow_zero, one_mul, zero_mul, mul_zero, zero_add,
      mul_add, add_mul, mul_comm] using h
  convert (h'.const_mul B).neg using 1 <;> simp [mul_assoc]

private theorem envelope_integrable {B T : ℝ} (hB : 0 ≤ B) (hT : 0 ≤ T) :
    IntegrableOn (poleEnvelope B) (Ioi T) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun t _ => envelope_derivative B t)
    (fun t ht => by dsimp only [poleEnvelope]; have : 0 ≤ t := hT.trans ht.le; positivity)
    (envelope_tendsto B)

private theorem envelope_tail {B T : ℝ} (hB : 0 ≤ B) (hT : 0 ≤ T) :
    (∫ t in Ioi T, poleEnvelope B t) = B * Real.exp (-T) * (T + 2) := by
  simpa only [zero_sub, neg_neg] using
    integral_Ioi_of_hasDerivAt_of_nonneg' (fun t _ => envelope_derivative B t)
      (fun t ht => by dsimp only [poleEnvelope]; have : 0 ≤ t := hT.trans ht.le; positivity)
      (envelope_tendsto B)

private theorem weighted_integrable (g : ℝ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hloc : ∀ T, 0 ≤ T → IntervalIntegrable g volume 0 T)
    (hb : ∀ t, 0 ≤ t → |g t| ≤ B * (t + 1)) :
    IntegrableOn (fun t => Real.exp (-t) * g t) (Ioi (0 : ℝ)) := by
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (2 * B) 0
    (b := fun b : ℝ => b) (l := atTop) ?_ tendsto_id ?_
  · intro b
    have hi := (hloc (max 0 b) (le_max_left 0 b)).continuousOn_mul
      (show ContinuousOn (fun t : ℝ => Real.exp (-t)) (uIcc 0 (max 0 b)) by fun_prop)
    exact hi.1.mono_set (fun t ht => ⟨ht.1, ht.2.trans (le_max_right 0 b)⟩)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with b hb0
    have hi := (hloc b hb0).continuousOn_mul
      (show ContinuousOn (fun t : ℝ => Real.exp (-t)) (uIcc 0 b) by fun_prop)
    have he : IntervalIntegrable (poleEnvelope B) volume 0 b := by
      exact (show Continuous (poleEnvelope B) by unfold poleEnvelope; fun_prop).intervalIntegrable 0 b
    calc
      _ ≤ ∫ t in (0 : ℝ)..b, poleEnvelope B t := by
        apply intervalIntegral.integral_mono_on hb0 hi.norm he
        intro t ht
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact (mul_le_mul_of_nonneg_left (hb t ht.1) (Real.exp_pos _).le).trans_eq (by
          unfold poleEnvelope; ring)
      _ = 2 * B - B * Real.exp (-b) * (b + 2) := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => envelope_derivative B t) he]
        simp only [neg_zero, Real.exp_zero, zero_add, mul_one]
        ring
      _ ≤ _ := by have : 0 ≤ B * Real.exp (-b) * (b + 2) := by positivity
                  linarith only [this]

private theorem weighted_tail_bound (g : ℝ → ℝ) {B T : ℝ} (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hb : ∀ t, 0 ≤ t → |g t| ≤ B * (t + 1)) :
    |∫ t in Ioi T, Real.exp (-t) * g t| ≤ B * Real.exp (-T) * (T + 2) := by
  have h := norm_integral_le_of_norm_le (f := fun t => Real.exp (-t) * g t)
    (envelope_integrable hB hT) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul_of_nonneg_left (hb t (hT.trans ht.le)) (Real.exp_pos _).le).trans_eq (by
        unfold poleEnvelope; ring))
  rw [Real.norm_eq_abs, envelope_tail hB hT] at h
  exact h

/-- Constant coefficient of the complete exponential pole, retaining both
weighted force and fractional-part work. -/
def ccmPrimeDeficitDivisorPoleConstant : ℝ :=
  (∫ t in Ioi (0 : ℝ), Real.exp (-t) * poleForce t) -
    (Real.eulerMascheroniConstant + 1) *
      ∫ t in Ioi (0 : ℝ), Real.exp (-t) * poleFloor t

/-- The actual source after subtracting its whole exponential-affine pole. -/
def ccmPrimeDeficitDivisorPoleRemainder (T : ℝ) : ℝ :=
  ccmPrimeDeficitDivisorSource T - Real.exp T *
    ((Real.eulerMascheroniConstant + 1) * T + ccmPrimeDeficitDivisorPoleConstant)

private theorem source_quadrature {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitDivisorSource T =
      Real.exp T * (∫ t in (0 : ℝ)..T, Real.exp (-t) * ccmPrimeDeficitDilationForce t) -
        ∫ s in (0 : ℝ)..T, ccmPrimeDeficitDilationForce (T - s) * poleFloor s := by
  rw [← logarithmicDilationSum_dilationSource_eq_divisorSource]
  have heq : logarithmicDilationSum ccmPrimeDeficitDilationSource T =
      logarithmicDilationSum (fun u => ∫ t in (0 : ℝ)..u, ccmPrimeDeficitDilationForce t) T := by
    unfold logarithmicDilationSum logarithmicWeightedDilation
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hlog : Real.log n ≤ T := (Real.log_le_iff_le_exp hnpos).mpr
      ((Nat.le_floor_iff (Real.exp_pos T).le).mp (Finset.mem_Icc.mp hn).2)
    dsimp only
    rw [integral_ccmPrimeDeficitDilationForce (sub_nonneg.mpr hlog)]
  rw [heq]
  exact logarithmicDilationSum_primitive_quadrature _
    (intervalIntegrable_ccmPrimeDeficitDilationForce hT) hT

private theorem remainder_eq_tails {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitDivisorPoleRemainder T =
      -Real.exp T * (∫ t in Ioi T, Real.exp (-t) * poleForce t) +
        (Real.eulerMascheroniConstant + 1) * Real.exp T *
          (∫ t in Ioi T, Real.exp (-t) * poleFloor t) -
            ∫ s in (0 : ℝ)..T, poleForce (T - s) * poleFloor s := by
  let c := Real.eulerMascheroniConstant + 1
  have hgi := weighted_integrable poleForce forceBudget_nonneg (fun _ => force_local)
    (fun _ => force_bound)
  have hji := weighted_integrable poleFloor zero_le_one (fun _ => floor_local)
    (fun _ => floor_bound)
  have hg := intervalIntegral.integral_interval_add_Ioi hgi (hgi.mono_set (Ioi_subset_Ioi hT))
  have hj := intervalIntegral.integral_interval_add_Ioi hji (hji.mono_set (Ioi_subset_Ioi hT))
  have hgloc := (force_local hT).continuousOn_mul
    (show ContinuousOn (fun t : ℝ => Real.exp (-t)) (uIcc 0 T) by fun_prop)
  have hjloc := (floor_local hT).continuousOn_mul
    (show ContinuousOn (fun t : ℝ => Real.exp (-t)) (uIcc 0 T) by fun_prop)
  have hmain : (∫ t in (0 : ℝ)..T, Real.exp (-t) * ccmPrimeDeficitDilationForce t) =
      c * T + ∫ t in (0 : ℝ)..T, Real.exp (-t) * poleForce t := by
    have hp (t : ℝ) : Real.exp (-t) * ccmPrimeDeficitDilationForce t =
        c + Real.exp (-t) * poleForce t := by
      have he : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
      dsimp only [poleForce, c]
      linear_combination (Real.eulerMascheroniConstant + 1) * he
    simp_rw [hp]
    rw [intervalIntegral.integral_add intervalIntegrable_const hgloc,
      intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  have hfloor : (∫ s in (0 : ℝ)..T, ccmPrimeDeficitDilationForce (T - s) * poleFloor s) =
      c * Real.exp T * (∫ s in (0 : ℝ)..T, Real.exp (-s) * poleFloor s) +
        ∫ s in (0 : ℝ)..T, poleForce (T - s) * poleFloor s := by
    have hp (s : ℝ) : ccmPrimeDeficitDilationForce (T - s) * poleFloor s =
        c * Real.exp T * (Real.exp (-s) * poleFloor s) + poleForce (T - s) * poleFloor s := by
      have he : Real.exp (T - s) = Real.exp T * Real.exp (-s) := by
        rw [← Real.exp_add]; congr 1
      dsimp only [poleForce, c]
      rw [he]
      ring
    have hfloc : IntervalIntegrable (fun s => poleForce (T - s) * poleFloor s) volume 0 T :=
      intervalIntegrable_reverse_mul_fract_exp _ (force_local hT) hT
    simp_rw [hp]
    rw [intervalIntegral.integral_add (hjloc.const_mul (c * Real.exp T)) hfloc,
      intervalIntegral.integral_const_mul]
  rw [ccmPrimeDeficitDivisorPoleRemainder, source_quadrature hT, hmain, hfloor]
  unfold ccmPrimeDeficitDivisorPoleConstant
  change _ = _
  linear_combination Real.exp T * hg - c * Real.exp T * hj

private theorem floor_work_bound {T : ℝ} (hT : 0 ≤ T) :
    |∫ s in (0 : ℝ)..T, poleForce (T - s) * poleFloor s| ≤
      forceBudget * (T ^ 2 / 2 + T) := by
  have hi := intervalIntegrable_reverse_mul_fract_exp _ (force_local hT) hT
  have hb : IntervalIntegrable (fun s : ℝ => forceBudget * (T - s + 1)) volume 0 T := by
    apply Continuous.intervalIntegrable; fun_prop
  have hd (s : ℝ) : HasDerivAt
      (fun s : ℝ => forceBudget * ((T + 1) * s - s ^ 2 / 2))
        (forceBudget * (T - s + 1)) s := by
    convert! ((((hasDerivAt_id s).const_mul (T + 1)).sub
      (((hasDerivAt_id s).pow 2).div_const 2)).const_mul forceBudget) using 1
    simp only [id_eq]; ring
  calc
    _ ≤ ∫ s in (0 : ℝ)..T, |poleForce (T - s) * poleFloor s| :=
      intervalIntegral.abs_integral_le_integral_abs hT
    _ ≤ ∫ s in (0 : ℝ)..T, forceBudget * (T - s + 1) := by
      apply intervalIntegral.integral_mono_on hT hi.abs hb
      intro s hs
      rw [abs_mul]
      change |poleForce (T - s)| * |poleFloor s| ≤ _
      have hj : |poleFloor s| ≤ 1 := by
        rw [poleFloor, abs_of_nonneg (Int.fract_nonneg _)]
        exact (Int.fract_lt_one _).le
      simpa only [mul_one] using mul_le_mul (force_bound (sub_nonneg.mpr hs.2)) hj
        (abs_nonneg _) (mul_nonneg forceBudget_nonneg (by linarith only [hs.2]))
    _ = _ := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hb]
      ring

private theorem remainder_bound {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeDeficitDivisorPoleRemainder T| ≤
      (forceBudget + |Real.eulerMascheroniConstant + 1|) * (T + 2) +
        forceBudget * (T ^ 2 / 2 + T) := by
  have he : Real.exp T * Real.exp (-T) = 1 := by rw [← Real.exp_add]; simp
  have hg := weighted_tail_bound poleForce forceBudget_nonneg hT (fun _ => force_bound)
  have hj := weighted_tail_bound poleFloor zero_le_one hT (fun _ => floor_bound)
  have hgf : |(-Real.exp T) * (∫ t in Ioi T, Real.exp (-t) * poleForce t)| ≤
      forceBudget * (T + 2) := by
    rw [abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp T * (forceBudget * Real.exp (-T) * (T + 2)) :=
        mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le
      _ = _ := by linear_combination forceBudget * (T + 2) * he
  have hjf : |(Real.eulerMascheroniConstant + 1) * Real.exp T *
      (∫ t in Ioi T, Real.exp (-t) * poleFloor t)| ≤
        |Real.eulerMascheroniConstant + 1| * (T + 2) := by
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ |Real.eulerMascheroniConstant + 1| * Real.exp T *
          (1 * Real.exp (-T) * (T + 2)) :=
        mul_le_mul_of_nonneg_left hj (by positivity)
      _ = _ := by linear_combination |Real.eulerMascheroniConstant + 1| * (T + 2) * he
  rw [remainder_eq_tails hT]
  exact ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    ((add_le_add (add_le_add hgf hjf) (floor_work_bound hT)).trans_eq (by ring))

/-- One global polynomial envelope after removal of both exponential
coefficients. No Möbius cancellation estimate is a premise. -/
theorem ccmPrimeDeficitDivisorPoleRemainder_polynomial_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T →
      |ccmPrimeDeficitDivisorPoleRemainder T| ≤ C * (T + 1) ^ 2 := by
  let C := 4 * (forceBudget + |Real.eulerMascheroniConstant + 1| + 1)
  have hB := forceBudget_nonneg
  have hc := abs_nonneg (Real.eulerMascheroniConstant + 1)
  refine ⟨C, by dsimp only [C]; positivity, fun T hT => (remainder_bound hT).trans ?_⟩
  dsimp only [C]
  have h1 := mul_nonneg hB hT
  have h2 := mul_nonneg hc hT
  have h3 := mul_nonneg hB (sq_nonneg T)
  have h4 := mul_nonneg hc (sq_nonneg T)
  nlinarith only [hT, hB, hc, h1, h2, h3, h4, sq_nonneg T]

private theorem remainder_nonpos {t : ℝ} (ht : t ≤ 0) :
    |ccmPrimeDeficitDivisorPoleRemainder t| ≤
      |Real.eulerMascheroniConstant + 1| + |ccmPrimeDeficitDivisorPoleConstant| := by
  have he1 : Real.exp t ≤ 1 := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr ht
  have he : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  have het : Real.exp t * |t| ≤ 1 := by
    rw [abs_of_nonpos ht]
    have hb : -t ≤ Real.exp (-t) := by linarith only [Real.add_one_le_exp (-t)]
    have hm := mul_le_mul_of_nonneg_left hb (Real.exp_pos t).le
    rwa [he] at hm
  rw [ccmPrimeDeficitDivisorPoleRemainder, ccmPrimeDeficitDivisorSource_of_nonpos ht,
    zero_sub, abs_neg, abs_mul, abs_of_pos (Real.exp_pos t)]
  calc
    _ ≤ Real.exp t * (|Real.eulerMascheroniConstant + 1| * |t| +
        |ccmPrimeDeficitDivisorPoleConstant|) := by
      exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans_eq (by rw [abs_mul]))
        (Real.exp_pos t).le
    _ = |Real.eulerMascheroniConstant + 1| * (Real.exp t * |t|) +
        |ccmPrimeDeficitDivisorPoleConstant| * Real.exp t := by ring
    _ ≤ _ := by
      simpa only [mul_one] using add_le_add
        (mul_le_mul_of_nonneg_left het (abs_nonneg _))
        (mul_le_mul_of_nonneg_left he1 (abs_nonneg _))

/-- The same remainder controls every causal boundary pair, including
negative shifted times. The constant is independent of packet or cutoff. -/
theorem ccmPrimeDeficitDivisorPoleRemainder_global_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      |ccmPrimeDeficitDivisorPoleRemainder t| ≤ C * (max t 0 + 1) ^ 2 := by
  obtain ⟨B, hB, hb⟩ := ccmPrimeDeficitDivisorPoleRemainder_polynomial_bound
  let K := |Real.eulerMascheroniConstant + 1| + |ccmPrimeDeficitDivisorPoleConstant|
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨B + K, by positivity, fun t => ?_⟩
  rcases le_total 0 t with ht | ht
  · rw [max_eq_left ht]
    exact (hb t ht).trans (mul_le_mul_of_nonneg_right (by linarith only [hK]) (sq_nonneg _))
  · rw [max_eq_right ht]
    simp only [zero_add, one_pow, mul_one]
    exact (remainder_nonpos ht).trans (by dsimp only [K]; linarith only [hB])

/-- Exact rank-two pole of the complete finite signed source form.
All pairs, including pairs outside the causal horizon, are retained in
the actual remainder. No separation or fixed-cutoff premise is imposed. -/
theorem ccmPrimeDeficitDivisorSource_finite_pair_eq_complete_pole
    {ι : Type*} (S : Finset ι) (v u : ι → ℝ) (T : ℝ) :
    (∑ i ∈ S, ∑ j ∈ S, v i * v j * ccmPrimeDeficitDivisorSource (T - u i - u j)) =
      Real.exp T *
        (((Real.eulerMascheroniConstant + 1) * T + ccmPrimeDeficitDivisorPoleConstant) *
          (∑ i ∈ S, v i * Real.exp (-u i)) ^ 2 -
            2 * (Real.eulerMascheroniConstant + 1) * (∑ i ∈ S, v i * Real.exp (-u i)) *
              (∑ i ∈ S, v i * u i * Real.exp (-u i))) +
        ∑ i ∈ S, ∑ j ∈ S, v i * v j * ccmPrimeDeficitDivisorPoleRemainder (T - u i - u j) := by
  let c := Real.eulerMascheroniConstant + 1
  let d := ccmPrimeDeficitDivisorPoleConstant
  let a := fun i => v i * Real.exp (-u i)
  let b := fun i => v i * u i * Real.exp (-u i)
  have hp (i j : ι) : v i * v j * ccmPrimeDeficitDivisorSource (T - u i - u j) =
      Real.exp T * (c * T + d) * a i * a j - Real.exp T * c * b i * a j -
        Real.exp T * c * a i * b j +
          v i * v j * ccmPrimeDeficitDivisorPoleRemainder (T - u i - u j) := by
    have he : Real.exp (T - u i - u j) =
        Real.exp T * Real.exp (-u i) * Real.exp (-u j) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
    dsimp only [a, b, c, d, ccmPrimeDeficitDivisorPoleRemainder]
    rw [he]
    ring
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul]
  dsimp only [a, b, c, d]
  ring

/-- A uniform bound for the complete remainder matrix, valid for
arbitrary moving nonnegative shifts and arbitrary real signs. The
coefficient mass is retained; this is not a native energy estimate. -/
theorem ccmPrimeDeficitDivisorSource_finite_pair_remainder_bound {ι : Type*} :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ι) (v u : ι → ℝ) (T : ℝ),
      0 ≤ T → (∀ i ∈ S, 0 ≤ u i) →
      |∑ i ∈ S, ∑ j ∈ S, v i * v j * ccmPrimeDeficitDivisorPoleRemainder (T - u i - u j)| ≤
        C * (T + 1) ^ 2 * (∑ i ∈ S, |v i|) ^ 2 := by
  obtain ⟨C, hC, hc⟩ := ccmPrimeDeficitDivisorPoleRemainder_global_bound
  refine ⟨C, hC, fun S v u T hT hu => ?_⟩
  have hp (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S) :
      |v i * v j * ccmPrimeDeficitDivisorPoleRemainder (T - u i - u j)| ≤
        |v i| * |v j| * (C * (T + 1) ^ 2) := by
    have ht : max (T - u i - u j) 0 ≤ T :=
      max_le (by linarith only [hu i hi, hu j hj]) hT
    have hr : |ccmPrimeDeficitDivisorPoleRemainder (T - u i - u j)| ≤ C * (T + 1) ^ 2 := by
      refine (hc _).trans ?_
      gcongr
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left hr (by positivity)
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S,
        |v i * v j * ccmPrimeDeficitDivisorPoleRemainder (T - u i - u j)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, |v i| * |v j| * (C * (T + 1) ^ 2) :=
      Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hp i hi j hj))
    _ = _ := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      ring

/-- Harmonic neutrality removes the entire exponential pole for every
adaptive finite packet, even when labels cross the half-horizon. -/
theorem ccmPrimeDeficitDivisorSource_harmonic_neutral_bound {ι : Type*} :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ι) (v u : ι → ℝ) (T : ℝ),
      0 ≤ T → (∀ i ∈ S, 0 ≤ u i) → (∑ i ∈ S, v i * Real.exp (-u i)) = 0 →
      |∑ i ∈ S, ∑ j ∈ S, v i * v j * ccmPrimeDeficitDivisorSource (T - u i - u j)| ≤
        C * (T + 1) ^ 2 * (∑ i ∈ S, |v i|) ^ 2 := by
  obtain ⟨C, hC, hc⟩ := ccmPrimeDeficitDivisorSource_finite_pair_remainder_bound (ι := ι)
  refine ⟨C, hC, fun S v u T hT hu hm => ?_⟩
  rw [ccmPrimeDeficitDivisorSource_finite_pair_eq_complete_pole, hm]
  simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, sub_zero, zero_add] using hc S v u T hT hu

end RHTower
