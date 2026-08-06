import GaloisForLFunctions.RHTower.MertensPrimeWindowWeakConvergence

/-!
# Mertens' second theorem with its constant

Abel summation of the prime log-density against `1 / log t` turns Mertens' first theorem into

```text
∑_{p ≤ N} 1/p = log log N + M + o(1),
```

with the explicit constant

```text
M = 1 - log log 2 + ∫_2^∞ (∑_{p ≤ t} (log p)/p - log t) / (t log² t) dt.
```

The error integral converges because the Mertens error is bounded and `∫_2^∞ dt/(t log² t)` is
finite.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The prime reciprocal sum -/

/-- The prime reciprocal weight `1/p` at primes, zero elsewhere. -/
def primeRecipWeight (n : ℕ) : ℝ := if n.Prime then ((n : ℝ))⁻¹ else 0

/-- The prime reciprocal sum `∑_{p ≤ N} 1/p`. -/
def primeRecipSum (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 0 N, primeRecipWeight n

private def invLog (t : ℝ) : ℝ := (Real.log t)⁻¹

private def invLogDeriv (t : ℝ) : ℝ := -(t * Real.log t ^ 2)⁻¹

private theorem hasDerivAt_invLog {t : ℝ} (ht : 1 < t) :
    HasDerivAt invLog (invLogDeriv t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have h := (Real.hasDerivAt_log ht0).inv hlog
  have heq : -t⁻¹ / Real.log t ^ 2 = invLogDeriv t := by
    rw [invLogDeriv]
    field_simp
  rw [← heq]
  exact h

private theorem continuousAt_invLogDeriv {t : ℝ} (ht : 1 < t) :
    ContinuousAt invLogDeriv t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hden : ContinuousAt (fun x : ℝ => x * Real.log x ^ 2) t :=
    continuousAt_id.mul ((Real.continuousAt_log ht0).pow 2)
  exact (hden.inv₀ (by positivity)).neg

private theorem primeRecipWeight_eq (n : ℕ) :
    primeRecipWeight n = invLog n * mertensPrimeWeight n := by
  rw [primeRecipWeight, mertensPrimeWeight]
  by_cases hp : n.Prime
  · have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hp.one_lt
    have hlog : Real.log (n : ℝ) ≠ 0 := (Real.log_pos hn1).ne'
    rw [if_pos hp, if_pos hp, invLog]
    field_simp
  · rw [if_neg hp, if_neg hp, mul_zero]

/-! ## Abel summation -/

private theorem primeRecipSum_abel {N : ℕ} (hN : 2 ≤ N) :
    primeRecipSum N =
      mertensPrimeWeightSum N / Real.log N -
        ∫ t in Ioc (2 : ℝ) N, invLogDeriv t * mertensPrimeWeightSum ⌊t⌋₊ := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hdiff : ∀ t ∈ Icc ((2 : ℕ) : ℝ) ((N : ℕ) : ℝ), DifferentiableAt ℝ invLog t := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := by exact_mod_cast ht.1
    exact (hasDerivAt_invLog (by linarith)).differentiableAt
  have hcontDeriv : ContinuousOn (deriv invLog) (Icc ((2 : ℕ) : ℝ) ((N : ℕ) : ℝ)) := by
    have hcont : ContinuousOn invLogDeriv (Icc ((2 : ℕ) : ℝ) ((N : ℕ) : ℝ)) := by
      intro t ht
      have ht2 : (2 : ℝ) ≤ t := by exact_mod_cast ht.1
      exact (continuousAt_invLogDeriv (by linarith)).continuousWithinAt
    refine hcont.congr fun t ht => ?_
    have ht2 : (2 : ℝ) ≤ t := by exact_mod_cast ht.1
    exact (hasDerivAt_invLog (by linarith)).deriv
  have hint : IntegrableOn (deriv invLog) (Icc ((2 : ℕ) : ℝ) ((N : ℕ) : ℝ)) :=
    hcontDeriv.integrableOn_Icc
  have hab := sum_mul_eq_sub_sub_integral_mul' mertensPrimeWeight (n := 2) (m := N) hN hdiff hint
  have hsplit : primeRecipSum N =
      invLog 2 * mertensPrimeWeight 2 +
        ∑ k ∈ Finset.Ioc 2 N, invLog k * mertensPrimeWeight k := by
    rw [primeRecipSum, show Finset.Icc 0 N = Finset.Icc 0 2 ∪ Finset.Ioc 2 N by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
        omega,
      Finset.sum_union (by
        rw [Finset.disjoint_left]
        intro a ha hb
        simp only [Finset.mem_Icc] at ha
        simp only [Finset.mem_Ioc] at hb
        omega)]
    congr 1
    · rw [show Finset.Icc 0 2 = ({0, 1, 2} : Finset ℕ) by decide]
      have hl2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
      norm_num [primeRecipWeight, mertensPrimeWeight, invLog]
      field_simp
    · exact Finset.sum_congr rfl fun n _ => primeRecipWeight_eq n
  have hlowsum : ∑ k ∈ Finset.Icc 0 2, mertensPrimeWeight k = Real.log 2 / 2 := by
    rw [show Finset.Icc 0 2 = ({0, 1, 2} : Finset ℕ) by decide]
    norm_num [mertensPrimeWeight]
  have hlowweight : mertensPrimeWeight 2 = Real.log 2 / 2 := by
    norm_num [mertensPrimeWeight]
  have hcong : (∫ t in Ioc ((2 : ℕ) : ℝ) ((N : ℕ) : ℝ),
      deriv invLog t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mertensPrimeWeight k) =
      ∫ t in Ioc (2 : ℝ) (N : ℝ), invLogDeriv t * mertensPrimeWeightSum ⌊t⌋₊ := by
    push_cast
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have ht2 : (2 : ℝ) < t := ht.1
    rw [(hasDerivAt_invLog (by linarith)).deriv, mertensPrimeWeightSum]
  have hinvN : invLog (N : ℝ) = (Real.log (N : ℝ))⁻¹ := rfl
  push_cast at hab hcong
  rw [hsplit, hab, hcong, hlowsum, hlowweight, hinvN, mertensPrimeWeightSum]
  field_simp
  ring

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology MeasureTheory Set
open scoped BigOperators

/-! ## Splitting off the Mertens error -/

/-- The Mertens floor error `∑_{p ≤ ⌊t⌋} (log p)/p - log t`. -/
def mertensFloorError (t : ℝ) : ℝ := mertensPrimeWeightSum ⌊t⌋₊ - Real.log t

theorem abs_mertensFloorError_le {t : ℝ} (ht : 2 ≤ t) :
    |mertensFloorError t| ≤ mertensPrimeWindowBound + 1 :=
  abs_mertensPrimeWeightSum_floor_sub_log_le ht

private theorem measurable_mertensFloorError : Measurable mertensFloorError := by
  have h1 : Measurable (fun t : ℝ => mertensPrimeWeightSum ⌊t⌋₊) :=
    (measurable_from_top (f := mertensPrimeWeightSum)).comp Nat.measurable_floor
  exact h1.sub Real.measurable_log

/-- The weight `1/(t log² t)` against which the Mertens error is integrated. -/
def mertensErrorWeight (t : ℝ) : ℝ := (t * Real.log t ^ 2)⁻¹

private theorem hasDerivAt_negInvLog {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun x : ℝ => -invLog x) (mertensErrorWeight t) t := by
  have h := (hasDerivAt_invLog ht).neg
  rw [invLogDeriv, neg_neg] at h
  rw [mertensErrorWeight]
  exact h

theorem mertensErrorWeight_nonneg {t : ℝ} (ht : 1 < t) : 0 ≤ mertensErrorWeight t := by
  have hlog : 0 < Real.log t := Real.log_pos ht
  rw [mertensErrorWeight]
  positivity

theorem integrableOn_mertensErrorWeight : IntegrableOn mertensErrorWeight (Ioi (2 : ℝ)) := by
  have hcont : ContinuousWithinAt (fun x : ℝ => -invLog x) (Ici (2 : ℝ)) 2 := by
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have : ContinuousAt (fun x : ℝ => -invLog x) 2 := by
      unfold invLog
      exact ((Real.continuousAt_log (by norm_num)).inv₀ hlog2).neg
    exact this.continuousWithinAt
  have hderiv : ∀ x ∈ Ioi (2 : ℝ), HasDerivAt (fun y : ℝ => -invLog y) (mertensErrorWeight x) x :=
    fun x hx => hasDerivAt_negInvLog (by linarith [hx.out])
  have hnn : ∀ x ∈ Ioi (2 : ℝ), 0 ≤ mertensErrorWeight x :=
    fun x hx => mertensErrorWeight_nonneg (by linarith [hx.out])
  have hlim : Tendsto (fun x : ℝ => -invLog x) atTop (nhds 0) := by
    have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
    have : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (nhds 0) :=
      hlog.inv_tendsto_atTop
    simpa [invLog] using this.neg
  exact integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnn hlim

theorem integrableOn_mertensFloorError_mul_mertensErrorWeight :
    IntegrableOn (fun t : ℝ => mertensFloorError t * mertensErrorWeight t) (Ioi (2 : ℝ)) := by
  have hmajor : IntegrableOn
      (fun t : ℝ => (mertensPrimeWindowBound + 1) * mertensErrorWeight t) (Ioi (2 : ℝ)) :=
    integrableOn_mertensErrorWeight.const_mul _
  have hmeas : AEStronglyMeasurable (fun t : ℝ => mertensFloorError t * mertensErrorWeight t)
      (volume.restrict (Ioi (2 : ℝ))) := by
    have hinv : Measurable mertensErrorWeight := by
      unfold mertensErrorWeight
      fun_prop
    exact (measurable_mertensFloorError.mul hinv).aestronglyMeasurable
  refine Integrable.mono hmajor hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht2 : (2 : ℝ) < t := ht
  have hnn := mertensErrorWeight_nonneg (by linarith : (1 : ℝ) < t)
  have hD : 0 ≤ mertensPrimeWindowBound + 1 := by linarith [mertensPrimeWindowBound_nonneg]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hD hnn)]
  exact mul_le_mul_of_nonneg_right (abs_mertensFloorError_le ht2.le) hnn

/-! ## The main logarithmic integral -/

private theorem integral_invLogMul {N : ℕ} (hN : 2 ≤ N) :
    (∫ t in Ioc (2 : ℝ) (N : ℝ), (t * Real.log t)⁻¹) =
      Real.log (Real.log N) - Real.log (Real.log 2) := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hderiv : ∀ t ∈ uIcc (2 : ℝ) (N : ℝ),
      HasDerivAt (fun x : ℝ => Real.log (Real.log x)) (t * Real.log t)⁻¹ t := by
    intro t ht
    rw [uIcc_of_le hNr] at ht
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have ht0 : t ≠ 0 := by linarith
    have hlog : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
    have h := (Real.hasDerivAt_log ht0).log hlog
    rw [show t⁻¹ / Real.log t = (t * Real.log t)⁻¹ by rw [mul_inv, div_eq_mul_inv]] at h
    exact h
  have hcont : ContinuousOn (fun t : ℝ => (t * Real.log t)⁻¹) (uIcc (2 : ℝ) (N : ℝ)) := by
    rw [uIcc_of_le hNr]
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have ht0 : t ≠ 0 := by linarith
    have hlog : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
    exact ((continuousAt_id.mul (Real.continuousAt_log ht0)).inv₀
      (mul_ne_zero ht0 hlog)).continuousWithinAt
  rw [← intervalIntegral.integral_of_le hNr,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology MeasureTheory Set
open scoped BigOperators

/-! ## Mertens' second theorem -/

/-- The Mertens constant of the prime reciprocal sum. -/
def mertensSecondConstant : ℝ :=
  1 - Real.log (Real.log 2) + ∫ t in Ioi (2 : ℝ), mertensFloorError t * mertensErrorWeight t

private theorem primeRecipSum_split {N : ℕ} (hN : 2 ≤ N) :
    primeRecipSum N =
      mertensPrimeWeightSum N / Real.log N +
        (Real.log (Real.log N) - Real.log (Real.log 2)) +
        ∫ t in Ioc (2 : ℝ) N, mertensFloorError t * mertensErrorWeight t := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hcontMain : ContinuousOn (fun t : ℝ => (t * Real.log t)⁻¹) (Icc (2 : ℝ) (N : ℝ)) := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have ht0 : t ≠ 0 := by linarith
    have hlog : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
    exact ((continuousAt_id.mul (Real.continuousAt_log ht0)).inv₀
      (mul_ne_zero ht0 hlog)).continuousWithinAt
  have hintMain : IntegrableOn (fun t : ℝ => (t * Real.log t)⁻¹) (Ioc (2 : ℝ) (N : ℝ)) :=
    (hcontMain.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hintErr : IntegrableOn
      (fun t : ℝ => mertensFloorError t * mertensErrorWeight t) (Ioc (2 : ℝ) (N : ℝ)) :=
    integrableOn_mertensFloorError_mul_mertensErrorWeight.mono_set Ioc_subset_Ioi_self
  have hptwise : ∀ t ∈ Ioc (2 : ℝ) (N : ℝ),
      -(invLogDeriv t * mertensPrimeWeightSum ⌊t⌋₊) =
        (t * Real.log t)⁻¹ + mertensFloorError t * mertensErrorWeight t := by
    intro t ht
    have ht2 : (2 : ℝ) < t := ht.1
    have ht0 : t ≠ 0 := by linarith
    have hlog : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
    rw [invLogDeriv, mertensErrorWeight, mertensFloorError]
    field_simp
    ring
  have hsplit : (∫ t in Ioc (2 : ℝ) (N : ℝ), invLogDeriv t * mertensPrimeWeightSum ⌊t⌋₊) =
      -((∫ t in Ioc (2 : ℝ) (N : ℝ), (t * Real.log t)⁻¹) +
        ∫ t in Ioc (2 : ℝ) (N : ℝ), mertensFloorError t * mertensErrorWeight t) := by
    rw [← MeasureTheory.integral_add hintMain hintErr, ← MeasureTheory.integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [← hptwise t ht, neg_neg]
  rw [primeRecipSum_abel hN, hsplit, integral_invLogMul hN]
  ring

private theorem tendsto_mertensPrimeWeightSum_div_log :
    Tendsto (fun N : ℕ => mertensPrimeWeightSum N / Real.log N) atTop (nhds 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlogtop : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hb : ∀ᶠ N : ℕ in atTop,
      ‖mertensPrimeWeightSum N / Real.log N - 1‖ ≤ mertensPrimeWindowBound / Real.log N := by
    filter_upwards [Filter.eventually_ge_atTop 2] with N hN
    have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
    have h := abs_mertensPrimeWeightSum_sub_log_le N (by omega)
    rw [Real.norm_eq_abs, show mertensPrimeWeightSum N / Real.log N - 1 =
        (mertensPrimeWeightSum N - Real.log N) / Real.log N by field_simp,
      abs_div, abs_of_pos hlogN]
    gcongr
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => norm_nonneg _) hb ?_
  exact Tendsto.div_atTop tendsto_const_nhds hlogtop

private theorem tendsto_errorIntegral :
    Tendsto (fun N : ℕ =>
      ∫ t in Ioc (2 : ℝ) (N : ℝ), mertensFloorError t * mertensErrorWeight t) atTop
      (nhds (∫ t in Ioi (2 : ℝ), mertensFloorError t * mertensErrorWeight t)) := by
  have hmono : Monotone (fun N : ℕ => Ioc (2 : ℝ) (N : ℝ)) := by
    intro a b hab
    exact Ioc_subset_Ioc_right (by exact_mod_cast hab)
  have hunion : (⋃ N : ℕ, Ioc (2 : ℝ) (N : ℝ)) = Ioi (2 : ℝ) := by
    ext t
    simp only [mem_iUnion, mem_Ioc, mem_Ioi]
    constructor
    · rintro ⟨N, hN, -⟩
      exact hN
    · intro ht
      obtain ⟨N, hN⟩ := exists_nat_ge t
      exact ⟨N, ht, hN⟩
  have hfi : IntegrableOn (fun t : ℝ => mertensFloorError t * mertensErrorWeight t)
      (⋃ N : ℕ, Ioc (2 : ℝ) (N : ℝ)) := by
    rw [hunion]
    exact integrableOn_mertensFloorError_mul_mertensErrorWeight
  have h := MeasureTheory.tendsto_setIntegral_of_monotone
    (fun N : ℕ => measurableSet_Ioc) hmono hfi
  rwa [hunion] at h

/-- **Mertens' second theorem with its constant.** -/
theorem tendsto_primeRecipSum_sub_logLog :
    Tendsto (fun N : ℕ => primeRecipSum N - Real.log (Real.log N)) atTop
      (nhds mertensSecondConstant) := by
  have hmain := tendsto_mertensPrimeWeightSum_div_log
  have herr := tendsto_errorIntegral
  have hsum := (hmain.sub_const (Real.log (Real.log 2))).add herr
  rw [mertensSecondConstant]
  refine hsum.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with N hN
  rw [primeRecipSum_split hN]
  ring

end

end RHTower
