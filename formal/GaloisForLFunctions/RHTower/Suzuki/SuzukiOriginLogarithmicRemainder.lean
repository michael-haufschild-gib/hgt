import GaloisForLFunctions.RHTower.Suzuki.SuzukiExplicitScrewRegularKernel
import Mathlib.Analysis.Calculus.LHopital

/-!
# Suzuki's logarithmic origin remainder

Equation (2.2) of Suzuki, *A Hilbert space associated with the Weil distribution and the
Riemann hypothesis* (arXiv:2606.09096), separates the universal origin singularity of the
Riemann screw function:

```text
g(t) = (1/2)|t| log |t| + A|t| + sum_{n <= exp |t|} Lambda(n)/sqrt(n)
         (|t| - log n) + r(t),
A = (log(2 pi) - psi(2))/2.
```

This module defines the literal remainder `r` from the prime--Lerch formula and proves that
identity.  More importantly for the small-aperture argument, it resolves the apparent pole in
the classical curvature

```text
r''(t) = -screwRegularKernel(t) - 1/(2t),  t > 0,
```

proving its exact limit `-7/4` at the origin.  The even continuous extension is therefore bounded
on a neighbourhood of zero.  These are unconditional analytic facts about the source function;
no Riemann-hypothesis or spectral premise occurs.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology Set

/-! ## Twice-renormalized kernel limit -/

private def originLimitExpFiveHalf (t : ℝ) : ℝ :=
  Real.exp (-(5 / 2 : ℝ) * t)

private def originLimitExpTwo (t : ℝ) : ℝ := Real.exp (-2 * t)

private def originLimitNumerator (t : ℝ) : ℝ :=
  2 * t * originLimitExpFiveHalf t - (1 - originLimitExpTwo t)

private def originLimitDenominator (t : ℝ) : ℝ :=
  2 * t * (1 - originLimitExpTwo t)

private def originLimitNumeratorOne (t : ℝ) : ℝ :=
  2 * originLimitExpFiveHalf t - 5 * t * originLimitExpFiveHalf t -
    2 * originLimitExpTwo t

private def originLimitDenominatorOne (t : ℝ) : ℝ :=
  2 * (1 - originLimitExpTwo t) + 4 * t * originLimitExpTwo t

private def originLimitNumeratorTwo (t : ℝ) : ℝ :=
  -10 * originLimitExpFiveHalf t + (25 / 2) * t * originLimitExpFiveHalf t +
    4 * originLimitExpTwo t

private def originLimitDenominatorTwo (t : ℝ) : ℝ :=
  8 * originLimitExpTwo t - 8 * t * originLimitExpTwo t

private theorem hasDerivAt_originLimitNumerator (t : ℝ) :
    HasDerivAt originLimitNumerator (originLimitNumeratorOne t) t := by
  have h5 : HasDerivAt originLimitExpFiveHalf
      (originLimitExpFiveHalf t * (-(5 / 2 : ℝ))) t := by
    unfold originLimitExpFiveHalf
    convert (hasDerivAt_const_mul (x := t) (-(5 / 2 : ℝ))).exp using 1
  have h2 : HasDerivAt originLimitExpTwo (originLimitExpTwo t * (-2 : ℝ)) t := by
    unfold originLimitExpTwo
    exact (hasDerivAt_const_mul (x := t) (-2 : ℝ)).exp
  unfold originLimitNumerator originLimitNumeratorOne
  convert (((hasDerivAt_id' t).const_mul 2).mul h5).sub
    ((hasDerivAt_const t 1).sub h2) using 1
  all_goals first | rfl | ring

private theorem hasDerivAt_originLimitDenominator (t : ℝ) :
    HasDerivAt originLimitDenominator (originLimitDenominatorOne t) t := by
  have h2 : HasDerivAt originLimitExpTwo (originLimitExpTwo t * (-2 : ℝ)) t := by
    unfold originLimitExpTwo
    exact (hasDerivAt_const_mul (x := t) (-2 : ℝ)).exp
  unfold originLimitDenominator originLimitDenominatorOne
  convert ((hasDerivAt_id' t).const_mul 2).mul
    ((hasDerivAt_const t 1).sub h2) using 1
  all_goals try rfl
  simp only [Pi.sub_apply]
  ring

private theorem hasDerivAt_originLimitNumeratorOne (t : ℝ) :
    HasDerivAt originLimitNumeratorOne (originLimitNumeratorTwo t) t := by
  have h5 : HasDerivAt originLimitExpFiveHalf
      (originLimitExpFiveHalf t * (-(5 / 2 : ℝ))) t := by
    unfold originLimitExpFiveHalf
    convert (hasDerivAt_const_mul (x := t) (-(5 / 2 : ℝ))).exp using 1
  have h2 : HasDerivAt originLimitExpTwo (originLimitExpTwo t * (-2 : ℝ)) t := by
    unfold originLimitExpTwo
    exact (hasDerivAt_const_mul (x := t) (-2 : ℝ)).exp
  unfold originLimitNumeratorOne originLimitNumeratorTwo
  convert ((h5.const_mul 2).sub (((hasDerivAt_id' t).const_mul 5).mul h5)).sub
    (h2.const_mul 2) using 1
  all_goals first | rfl | ring

private theorem hasDerivAt_originLimitDenominatorOne (t : ℝ) :
    HasDerivAt originLimitDenominatorOne (originLimitDenominatorTwo t) t := by
  have h2 : HasDerivAt originLimitExpTwo (originLimitExpTwo t * (-2 : ℝ)) t := by
    unfold originLimitExpTwo
    exact (hasDerivAt_const_mul (x := t) (-2 : ℝ)).exp
  unfold originLimitDenominatorOne originLimitDenominatorTwo
  convert (((hasDerivAt_const t 1).sub h2).const_mul 2).add
    (((hasDerivAt_id' t).const_mul 4).mul h2) using 1
  all_goals first | rfl | ring

private theorem tendsto_originLimitNumeratorTwo :
    Tendsto originLimitNumeratorTwo (𝓝[>] 0) (𝓝 (-6)) := by
  have h : Continuous originLimitNumeratorTwo := by
    unfold originLimitNumeratorTwo originLimitExpFiveHalf originLimitExpTwo
    fun_prop
  have ht : Tendsto originLimitNumeratorTwo (𝓝 (0 : ℝ))
      (𝓝 (originLimitNumeratorTwo 0)) := h.continuousAt
  have ht0 : Tendsto originLimitNumeratorTwo (𝓝 (0 : ℝ)) (𝓝 (-6)) := by
    convert ht using 1
    all_goals norm_num [originLimitNumeratorTwo, originLimitExpFiveHalf, originLimitExpTwo]
  exact tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi 0) ht0

private theorem tendsto_originLimitDenominatorTwo :
    Tendsto originLimitDenominatorTwo (𝓝[>] 0) (𝓝 8) := by
  have h : Continuous originLimitDenominatorTwo := by
    unfold originLimitDenominatorTwo originLimitExpTwo
    fun_prop
  have ht : Tendsto originLimitDenominatorTwo (𝓝 (0 : ℝ))
      (𝓝 (originLimitDenominatorTwo 0)) := h.continuousAt
  have ht0 : Tendsto originLimitDenominatorTwo (𝓝 (0 : ℝ)) (𝓝 8) := by
    simpa [originLimitDenominatorTwo, originLimitExpTwo] using ht
  exact tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi 0) ht0

private theorem tendsto_originLimitNumeratorOne :
    Tendsto originLimitNumeratorOne (𝓝[>] 0) (𝓝 0) := by
  have h : Continuous originLimitNumeratorOne := by
    unfold originLimitNumeratorOne originLimitExpFiveHalf originLimitExpTwo
    fun_prop
  have ht : Tendsto originLimitNumeratorOne (𝓝 (0 : ℝ))
      (𝓝 (originLimitNumeratorOne 0)) := h.continuousAt
  have ht0 : Tendsto originLimitNumeratorOne (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa [originLimitNumeratorOne, originLimitExpFiveHalf, originLimitExpTwo] using ht
  exact tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi 0) ht0

private theorem tendsto_originLimitDenominatorOne :
    Tendsto originLimitDenominatorOne (𝓝[>] 0) (𝓝 0) := by
  have h : Continuous originLimitDenominatorOne := by
    unfold originLimitDenominatorOne originLimitExpTwo
    fun_prop
  have ht : Tendsto originLimitDenominatorOne (𝓝 (0 : ℝ))
      (𝓝 (originLimitDenominatorOne 0)) := h.continuousAt
  have ht0 : Tendsto originLimitDenominatorOne (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa [originLimitDenominatorOne, originLimitExpTwo] using ht
  exact tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi 0) ht0

private theorem tendsto_originLimitNumerator :
    Tendsto originLimitNumerator (𝓝[>] 0) (𝓝 0) := by
  have h : Continuous originLimitNumerator := by
    unfold originLimitNumerator originLimitExpFiveHalf originLimitExpTwo
    fun_prop
  have ht : Tendsto originLimitNumerator (𝓝 (0 : ℝ))
      (𝓝 (originLimitNumerator 0)) := h.continuousAt
  have ht0 : Tendsto originLimitNumerator (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa [originLimitNumerator, originLimitExpFiveHalf, originLimitExpTwo] using ht
  exact tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi 0) ht0

private theorem tendsto_originLimitDenominator :
    Tendsto originLimitDenominator (𝓝[>] 0) (𝓝 0) := by
  have h : Continuous originLimitDenominator := by
    unfold originLimitDenominator originLimitExpTwo
    fun_prop
  have ht : Tendsto originLimitDenominator (𝓝 (0 : ℝ))
      (𝓝 (originLimitDenominator 0)) := h.continuousAt
  have ht0 : Tendsto originLimitDenominator (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa [originLimitDenominator, originLimitExpTwo] using ht
  exact tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi 0) ht0

private theorem eventually_originLimitDenominatorTwo_ne :
    ∀ᶠ t in 𝓝[>] 0, originLimitDenominatorTwo t ≠ 0 :=
  tendsto_originLimitDenominatorTwo.eventually_ne (by norm_num)

private theorem eventually_originLimitDenominatorOne_ne :
    ∀ᶠ t in 𝓝[>] 0, originLimitDenominatorOne t ≠ 0 := by
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := ht
  unfold originLimitDenominatorOne originLimitExpTwo
  have h₁ : 0 < 1 - Real.exp (-(2 * t)) := one_sub_exp_neg_two_mul_pos htpos
  have h₁' : 0 < 1 - Real.exp (-2 * t) := by
    convert h₁ using 1
    ring
  exact ne_of_gt (add_pos (mul_pos (by norm_num) h₁')
    (mul_pos (mul_pos (by norm_num) htpos) (Real.exp_pos _)))

private theorem tendsto_originLimitRatio :
    Tendsto (fun t => originLimitNumerator t / originLimitDenominator t)
      (𝓝[>] 0) (𝓝 (-3 / 4 : ℝ)) := by
  have hsecond : Tendsto
      (fun t => originLimitNumeratorTwo t / originLimitDenominatorTwo t)
      (𝓝[>] 0) (𝓝 (-3 / 4 : ℝ)) := by
    change Tendsto (originLimitNumeratorTwo / originLimitDenominatorTwo)
      (𝓝[>] 0) (𝓝 (-3 / 4 : ℝ))
    have h := tendsto_originLimitNumeratorTwo.div tendsto_originLimitDenominatorTwo
      (by norm_num : (8 : ℝ) ≠ 0)
    norm_num at h
    convert h using 1
    all_goals ring
  have hfirst : Tendsto
      (fun t => originLimitNumeratorOne t / originLimitDenominatorOne t)
      (𝓝[>] 0) (𝓝 (-3 / 4 : ℝ)) :=
    HasDerivAt.lhopital_zero_nhdsGT
      (Eventually.of_forall hasDerivAt_originLimitNumeratorOne)
      (Eventually.of_forall hasDerivAt_originLimitDenominatorOne)
      eventually_originLimitDenominatorTwo_ne
      tendsto_originLimitNumeratorOne tendsto_originLimitDenominatorOne hsecond
  exact HasDerivAt.lhopital_zero_nhdsGT
    (Eventually.of_forall hasDerivAt_originLimitNumerator)
    (Eventually.of_forall hasDerivAt_originLimitDenominator)
    eventually_originLimitDenominatorOne_ne
    tendsto_originLimitNumerator tendsto_originLimitDenominator hfirst

private theorem originCurvature_eq_limitRatio {t : ℝ} (ht : 0 < t) :
    -screwRegularKernel t - 1 / (2 * t) =
      -Real.exp (t / 2) + originLimitNumerator t / originLimitDenominator t := by
  have ht0 : t ≠ 0 := ht.ne'
  have hE : 1 - Real.exp (-(2 * t)) ≠ 0 :=
    (one_sub_exp_neg_two_mul_pos ht).ne'
  have hquot : originLimitNumerator t / originLimitDenominator t =
      Real.exp (-(5 * t / 2)) / (1 - Real.exp (-(2 * t))) - 1 / (2 * t) := by
    unfold originLimitNumerator originLimitDenominator originLimitExpFiveHalf originLimitExpTwo
    field_simp [ht0, hE]
  rw [hquot, screwRegularKernel]
  ring

/-- The exact removable-singularity value of Suzuki's logarithmically renormalized regular
curvature. -/
theorem tendsto_suzukiOriginRemainderCurvature :
    Tendsto (fun t => -screwRegularKernel t - 1 / (2 * t))
      (𝓝[>] 0) (𝓝 (-7 / 4 : ℝ)) := by
  have hrepr : (fun t => -screwRegularKernel t - 1 / (2 * t)) =ᶠ[𝓝[>] 0]
      fun t => -Real.exp (t / 2) +
        originLimitNumerator t / originLimitDenominator t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact originCurvature_eq_limitRatio ht
  apply Tendsto.congr' hrepr.symm
  have hexp : Tendsto (fun t : ℝ => -Real.exp (t / 2)) (𝓝[>] 0) (𝓝 (-1)) := by
    have h : Continuous (fun t : ℝ => -Real.exp (t / 2)) := by fun_prop
    have ht : Tendsto (fun t : ℝ => -Real.exp (t / 2)) (𝓝 (0 : ℝ))
        (𝓝 ((fun t : ℝ => -Real.exp (t / 2)) 0)) := h.continuousAt
    rw [show (fun t : ℝ => -Real.exp (t / 2)) 0 = (-1 : ℝ) by norm_num] at ht
    exact tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi 0) ht
  convert hexp.add tendsto_originLimitRatio using 1
  all_goals norm_num

/-! ## Continuous curvature extension -/

/-- Even continuous extension of the classical second derivative of Suzuki's origin remainder. -/
def suzukiOriginRemainderCurvature (t : ℝ) : ℝ :=
  if t = 0 then (-7 / 4 : ℝ)
  else -screwRegularKernel |t| - 1 / (2 * |t|)

@[simp] theorem suzukiOriginRemainderCurvature_zero :
    suzukiOriginRemainderCurvature 0 = -7 / 4 := by
  simp [suzukiOriginRemainderCurvature]

theorem suzukiOriginRemainderCurvature_of_ne {t : ℝ} (ht : t ≠ 0) :
    suzukiOriginRemainderCurvature t =
      -screwRegularKernel |t| - 1 / (2 * |t|) := by
  simp [suzukiOriginRemainderCurvature, ht]

theorem tendsto_suzukiOriginRemainderCurvature_nhdsNE :
    Tendsto suzukiOriginRemainderCurvature (𝓝[≠] 0) (𝓝 (-7 / 4 : ℝ)) := by
  have h := tendsto_suzukiOriginRemainderCurvature.comp tendsto_abs_nhdsNE_zero
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (suzukiOriginRemainderCurvature_of_ne ht).symm

theorem continuousAt_suzukiOriginRemainderCurvature_zero :
    ContinuousAt suzukiOriginRemainderCurvature 0 := by
  rw [continuousAt_iff_punctured_nhds]
  simpa using tendsto_suzukiOriginRemainderCurvature_nhdsNE

theorem continuousAt_suzukiOriginRemainderCurvature_of_ne {t : ℝ} (ht : t ≠ 0) :
    ContinuousAt suzukiOriginRemainderCurvature t := by
  have habspos : 0 < |t| := abs_pos.mpr ht
  have habs0 : |t| ≠ 0 := habspos.ne'
  have hden : 1 - Real.exp (-(2 * |t|)) ≠ 0 :=
    (one_sub_exp_neg_two_mul_pos habspos).ne'
  have hK : ContinuousAt (fun x : ℝ => screwRegularKernel |x|) t := by
    unfold screwRegularKernel
    apply ContinuousAt.sub
    · fun_prop
    · exact (by fun_prop :
          ContinuousAt (fun x : ℝ => Real.exp (-(5 * |x| / 2))) t).div
        (by fun_prop :
          ContinuousAt (fun x : ℝ => 1 - Real.exp (-(2 * |x|))) t) hden
  have hfree : ContinuousAt (fun x : ℝ => 1 / (2 * |x|)) t := by
    exact (by fun_prop : ContinuousAt (fun _ : ℝ => (1 : ℝ)) t).div
      (by fun_prop : ContinuousAt (fun x : ℝ => 2 * |x|) t)
      (mul_ne_zero (by norm_num) habs0)
  have hformula : ContinuousAt
      (fun x : ℝ => -screwRegularKernel |x| - 1 / (2 * |x|)) t := hK.neg.sub hfree
  apply hformula.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds ht] with x hx
  exact suzukiOriginRemainderCurvature_of_ne hx

/-- Suzuki's renormalized archimedean curvature is continuous across the origin. -/
theorem continuous_suzukiOriginRemainderCurvature :
    Continuous suzukiOriginRemainderCurvature := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t = 0
  · simpa [ht] using continuousAt_suzukiOriginRemainderCurvature_zero
  · exact continuousAt_suzukiOriginRemainderCurvature_of_ne ht

/-- Uniform local curvature bound required by the scaled `O(a)` form estimate. -/
theorem exists_suzukiOriginRemainderCurvature_bound :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ t : ℝ, |t| ≤ 1 → |suzukiOriginRemainderCurvature t| ≤ M := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := suzukiOriginRemainderCurvature)
    continuous_suzukiOriginRemainderCurvature.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht
  rw [← Real.norm_eq_abs]
  exact (hC t ((abs_le).mp ht)).trans (le_max_left _ _)

/-! ## Literal source remainder and equation (2.2) -/

/-- Suzuki's coefficient `A = (log(2 pi) - psi(2))/2` in equation (2.2). -/
def suzukiOriginLinearCoeff : ℝ :=
  (Real.log (2 * Real.pi) - (Complex.digamma 2).re) / 2

/-- Positive-ray remainder after removing the universal logarithm, linear coefficient, and prime
hinges from the literal prime--Lerch screw function. -/
def suzukiOriginRemainderPos (t : ℝ) : ℝ :=
  -4 * (Real.exp (t / 2) + Real.exp (-(t / 2)) - 2)
    - screwLinearCoeff / 2 * t - screwLerchConst + screwLerchTail t
    - (1 / 2 : ℝ) * t * Real.log t - suzukiOriginLinearCoeff * t

/-- Even Suzuki origin remainder. -/
def suzukiOriginRemainder (t : ℝ) : ℝ := suzukiOriginRemainderPos |t|

/-- Literal even screw function used in Suzuki's equation (2.2). -/
def suzukiSourceScrew (t : ℝ) : ℝ :=
  screwFn screwLinearCoeff screwLerchConst |t|

/-- Suzuki 2026, equation (2.2), as an exact identity of the source functions. -/
theorem suzuki_equation_two_two (t : ℝ) :
    suzukiSourceScrew t =
      (1 / 2 : ℝ) * |t| * Real.log |t| + suzukiOriginLinearCoeff * |t| +
        screwPrimeSum |t| + suzukiOriginRemainder t := by
  unfold suzukiSourceScrew suzukiOriginRemainder suzukiOriginRemainderPos screwFn
  ring

@[simp] theorem suzukiOriginRemainder_neg (t : ℝ) :
    suzukiOriginRemainder (-t) = suzukiOriginRemainder t := by
  simp [suzukiOriginRemainder]

private def suzukiOriginRemainderPosOne (t : ℝ) : ℝ :=
  -2 * Real.exp (t / 2) + 2 * Real.exp (-(t / 2)) - screwLinearCoeff / 2 +
    screwLerchTail₁ t - (1 / 2 : ℝ) * (Real.log t + 1) - suzukiOriginLinearCoeff

private theorem hasDerivAt_suzukiOriginRemainderPos {t : ℝ} (ht : 0 < t) :
    HasDerivAt suzukiOriginRemainderPos (suzukiOriginRemainderPosOne t) t := by
  have hlin : HasDerivAt (fun x : ℝ => screwLinearCoeff / 2 * x)
      (screwLinearCoeff / 2) t := by
    simpa using (hasDerivAt_id' t).const_mul (screwLinearCoeff / 2)
  have htlog : HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * x * Real.log x)
      ((1 / 2 : ℝ) * (Real.log t + 1)) t := by
    simpa only [Pi.mul_apply, one_mul, mul_inv_cancel₀ ht.ne', mul_add, mul_one, mul_assoc] using
      ((hasDerivAt_id' t).mul (Real.hasDerivAt_log ht.ne')).const_mul (1 / 2 : ℝ)
  have hA : HasDerivAt (fun x : ℝ => suzukiOriginLinearCoeff * x)
      suzukiOriginLinearCoeff t := by
    simpa using (hasDerivAt_id' t).const_mul suzukiOriginLinearCoeff
  unfold suzukiOriginRemainderPos suzukiOriginRemainderPosOne
  convert (((((hasDerivAt_screwExpBlock t).sub hlin).sub_const screwLerchConst).add
    (hasDerivAt_screwLerchTail ht)).sub htlog).sub hA using 1
  all_goals rfl

private theorem hasDerivAt_suzukiOriginRemainderPosOne {t : ℝ} (ht : 0 < t) :
    HasDerivAt suzukiOriginRemainderPosOne
      (-screwRegularKernel t - 1 / (2 * t)) t := by
  have hExp : HasDerivAt
      (fun x : ℝ => -2 * Real.exp (x / 2) + 2 * Real.exp (-(x / 2)))
      (-(Real.exp (t / 2) + Real.exp (-(t / 2)))) t := by
    convert ((hasDerivAt_exp_half t).const_mul (-2 : ℝ)).add
      ((hasDerivAt_exp_neg_half t).const_mul 2) using 1
    all_goals first | rfl | ring
  have hlog : HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * (Real.log x + 1))
      (1 / (2 * t)) t := by
    convert ((Real.hasDerivAt_log ht.ne').add_const 1).const_mul (1 / 2 : ℝ) using 1
    all_goals try rfl
    field_simp [ht.ne']
  have hraw : HasDerivAt suzukiOriginRemainderPosOne
      (-(Real.exp (t / 2) + Real.exp (-(t / 2))) + screwLerchTail₂ t -
        1 / (2 * t)) t := by
    unfold suzukiOriginRemainderPosOne
    convert ((((hExp.sub_const (screwLinearCoeff / 2)).add
      (hasDerivAt_screwLerchTail₁ ht)).sub hlog).sub_const suzukiOriginLinearCoeff) using 1
    all_goals rfl
  convert hraw using 1
  rw [screwRegularKernel_eq_tailForm ht, screwLerchTail₂_eq ht]
  ring

/-- On the positive ray, the literal remainder in Suzuki's equation (2.2) has the continuous
renormalized regular curvature above. -/
theorem iteratedDeriv_two_suzukiOriginRemainderPos {t : ℝ} (ht : 0 < t) :
    iteratedDeriv 2 suzukiOriginRemainderPos t = suzukiOriginRemainderCurvature t := by
  have hEq : deriv suzukiOriginRemainderPos =ᶠ[𝓝 t] suzukiOriginRemainderPosOne := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (hasDerivAt_suzukiOriginRemainderPos hs).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hEq.deriv_eq,
    (hasDerivAt_suzukiOriginRemainderPosOne ht).deriv,
    suzukiOriginRemainderCurvature_of_ne ht.ne']
  rw [abs_of_pos ht]

end GaloisForLFunctions.RHTower
