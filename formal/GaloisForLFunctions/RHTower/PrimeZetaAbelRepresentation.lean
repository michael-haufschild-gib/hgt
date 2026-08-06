import GaloisForLFunctions.RHTower.MertensSecondTheorem
import GaloisForLFunctions.RHTower.PrimeZetaLogAsymptotic
import Mathlib.NumberTheory.AbelSummation

/-!
# The Abel representation of the prime zeta function

For `δ > 0` improper Abel summation of `∑_p p^(-1-δ)` against the prime reciprocal sum gives

```text
P(1 + δ) = δ ∫_1^∞ t^(-δ-1) (∑_{p ≤ t} 1/p) dt.
```

The two inputs are the elementary bound `∑_{p ≤ N} 1/p ≤ (log N + C)/log 2`, obtained from
Mertens' first theorem alone, and the decay `N^(-δ) log N → 0`.
-/

open Filter Topology MeasureTheory Set Asymptotics
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## An elementary bound on the prime reciprocal sum -/

theorem primeRecipSum_le (N : ℕ) :
    primeRecipSum N ≤ mertensPrimeWeightSum N / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [primeRecipSum, mertensPrimeWeightSum, Finset.sum_div]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [primeRecipWeight, mertensPrimeWeight]
  by_cases hp : n.Prime
  · rw [if_pos hp, if_pos hp]
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp.two_le
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hlogn : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hn2
    rw [div_div, le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) * Real.log 2),
      show (n : ℝ)⁻¹ * ((n : ℝ) * Real.log 2) = Real.log 2 by field_simp]
    exact hlogn
  · rw [if_neg hp, if_neg hp]
    simp

theorem primeRecipSum_le_log {N : ℕ} (hN : 1 ≤ N) :
    primeRecipSum N ≤ (Real.log N + mertensPrimeWindowBound) / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine (primeRecipSum_le N).trans ?_
  gcongr
  exact mertensPrimeWeightSum_le N hN

theorem primeRecipSum_nonneg (N : ℕ) : 0 ≤ primeRecipSum N := by
  refine Finset.sum_nonneg fun n _ => ?_
  rw [primeRecipWeight]
  split_ifs
  · positivity
  · exact le_rfl

/-! ## The Abel representation -/

private def rpowNeg (δ : ℝ) (t : ℝ) : ℝ := t ^ (-δ)

private theorem hasDerivAt_rpowNeg {δ t : ℝ} (ht : 0 < t) :
    HasDerivAt (rpowNeg δ) (-δ * t ^ (-δ - 1)) t := by
  have h := Real.hasDerivAt_rpow_const (x := t) (p := -δ) (Or.inl ht.ne')
  exact h

private theorem deriv_rpowNeg {δ t : ℝ} (ht : 0 < t) :
    deriv (rpowNeg δ) t = -δ * t ^ (-δ - 1) := (hasDerivAt_rpowNeg ht).deriv

private theorem continuousOn_derivRpowNeg (δ : ℝ) :
    ContinuousOn (fun t : ℝ => -δ * t ^ (-δ - 1)) (Ici (1 : ℝ)) := by
  intro t ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have : ContinuousAt (fun x : ℝ => -δ * x ^ (-δ - 1)) t := by
    refine continuousAt_const.mul ?_
    exact (Real.continuousAt_rpow_const t (-δ - 1) (Or.inl ht0.ne'))
  exact this.continuousWithinAt

theorem tendsto_rpow_neg_mul_log {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun t : ℝ => t ^ (-δ) * (Real.log t + mertensPrimeWindowBound)) atTop (nhds 0) := by
  have h1 : Tendsto (fun t : ℝ => Real.log t / t ^ δ) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop hδ).tendsto_div_nhds_zero
  have h2 : Tendsto (fun t : ℝ => mertensPrimeWindowBound / t ^ δ) atTop (nhds 0) := by
    refine Tendsto.div_atTop tendsto_const_nhds ?_
    exact tendsto_rpow_atTop hδ
  have h := h1.add h2
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [Real.rpow_neg ht.le]
  have hne : (t : ℝ) ^ δ ≠ 0 := by positivity
  field_simp

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology MeasureTheory Set Asymptotics
open scoped BigOperators

/-! ## The improper Abel representation -/

private theorem tendsto_rpowNeg_mul_primeRecipSum {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => rpowNeg δ n * primeRecipSum n) atTop (nhds 0) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmajor : Tendsto
      (fun n : ℕ => ((n : ℝ) ^ (-δ) * (Real.log n + mertensPrimeWindowBound)) / Real.log 2)
      atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_mul_log hδ).comp tendsto_natCast_atTop_atTop
    simpa using h.div_const (Real.log 2)
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hmajor
  · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (primeRecipSum_nonneg n)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 : primeRecipSum 0 = 0 := by simp [primeRecipSum, primeRecipWeight]
      have hz : (((0 : ℕ) : ℝ)) ^ (-δ) = 0 := by
        rw [Nat.cast_zero, Real.zero_rpow (by linarith : -δ ≠ 0)]
      rw [rpowNeg, h0, mul_zero, hz, zero_mul, zero_div]
    · have hbound := primeRecipSum_le_log (N := n) hn
      have hpow : (0 : ℝ) ≤ (n : ℝ) ^ (-δ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      rw [rpowNeg, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hbound hpow

private theorem locallyIntegrableOn_deriv_rpowNeg (δ : ℝ) :
    LocallyIntegrableOn (deriv (rpowNeg δ)) (Ici (1 : ℝ)) := by
  have hcont : ContinuousOn (deriv (rpowNeg δ)) (Ici (1 : ℝ)) := by
    refine (continuousOn_derivRpowNeg δ).congr fun t ht => ?_
    exact deriv_rpowNeg (lt_of_lt_of_le zero_lt_one ht)
  exact hcont.locallyIntegrableOn measurableSet_Ici

private theorem sum_rpowNeg_mul_primeRecipWeight (δ : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 0 n, rpowNeg δ k * primeRecipWeight k =
      ∑ k ∈ Finset.Icc 0 n, (if k.Prime then ((k : ℝ)) ^ (-(1 + δ)) else 0) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [rpowNeg, primeRecipWeight]
  by_cases hp : k.Prime
  · have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hp.pos
    rw [if_pos hp, if_pos hp, ← Real.rpow_neg_one (k : ℝ), ← Real.rpow_add hk0]
    congr 1
    ring
  · rw [if_neg hp, if_neg hp, mul_zero]

theorem summable_primeIndicatorRpow {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => if n.Prime then ((n : ℝ)) ^ (-s) else 0) := by
  have h : Summable (fun n : ℕ => ((n : ℝ)) ^ (-s)) := by
    have h0 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ s) :=
      Real.summable_one_div_nat_rpow.mpr hs
    refine h0.congr fun n => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) h
  · split_ifs
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
    · exact le_rfl
  · split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) _

theorem tsum_primeIndicatorRpow {s : ℝ} (_hs : 1 < s) :
    (∑' n : ℕ, if n.Prime then ((n : ℝ)) ^ (-s) else 0) = primeZeta s := by
  rw [primeZeta]
  have hsupp : Function.support (fun n : ℕ => if n.Prime then ((n : ℝ)) ^ (-s) else 0) ⊆
      {n : ℕ | n.Prime} := by
    intro n hn
    simp only [Function.mem_support] at hn
    by_contra hc
    simp only [Set.mem_setOf_eq] at hc
    rw [if_neg hc] at hn
    exact hn rfl
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  refine tsum_congr fun p => ?_
  have hp : Nat.Prime (p : ℕ) := p.2
  rw [if_pos hp]

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology MeasureTheory Set Asymptotics
open scoped BigOperators

private theorem isBigO_const_rpow {C r : ℝ} (hr : 0 < r) :
    (fun _ : ℝ => C) =O[atTop] (fun t : ℝ => t ^ r) := by
  refine IsBigO.of_bound |C| ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have h1 : (1 : ℝ) ≤ t ^ r := Real.one_le_rpow ht hr.le
  have hpos : (0 : ℝ) ≤ t ^ r := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos]
  nlinarith [abs_nonneg C]

private theorem isBigO_derivRpowNeg_mul_primeRecipSum {δ : ℝ} (hδ : 0 < δ) :
    (fun t : ℝ => deriv (rpowNeg δ) t * primeRecipSum ⌊t⌋₊) =O[atTop]
      (fun t : ℝ => t ^ (-1 - δ / 2)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 ≤ mertensPrimeWindowBound := mertensPrimeWindowBound_nonneg
  have hb : (fun t : ℝ => deriv (rpowNeg δ) t * primeRecipSum ⌊t⌋₊) =O[atTop]
      (fun t : ℝ => t ^ (-δ - 1) * (Real.log t + mertensPrimeWindowBound)) := by
    refine IsBigO.of_bound (δ / Real.log 2) ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hfloor1 : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr (by linarith)
    have hfloorle : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0.le
    have hfloorpos : (0 : ℝ) < ((⌊t⌋₊ : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hfloor1
    have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
    have hAle : primeRecipSum ⌊t⌋₊ ≤ (Real.log t + mertensPrimeWindowBound) / Real.log 2 := by
      refine (primeRecipSum_le_log hfloor1).trans ?_
      gcongr
    have hA0 : 0 ≤ primeRecipSum ⌊t⌋₊ := primeRecipSum_nonneg _
    have hpow : (0 : ℝ) < t ^ (-δ - 1) := Real.rpow_pos_of_pos ht0 _
    have hlogD : (0 : ℝ) ≤ Real.log t + mertensPrimeWindowBound := by linarith
    rw [deriv_rpowNeg ht0, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hpow.le hlogD), abs_mul, abs_mul, abs_neg,
      abs_of_pos hδ, abs_of_nonneg hpow.le, abs_of_nonneg hA0]
    calc δ * t ^ (-δ - 1) * primeRecipSum ⌊t⌋₊
        ≤ δ * t ^ (-δ - 1) * ((Real.log t + mertensPrimeWindowBound) / Real.log 2) := by
          exact mul_le_mul_of_nonneg_left hAle (by positivity)
      _ = δ / Real.log 2 * (t ^ (-δ - 1) * (Real.log t + mertensPrimeWindowBound)) := by
          field_simp
  refine hb.trans ?_
  have hlogO : (fun t : ℝ => Real.log t + mertensPrimeWindowBound) =O[atTop]
      (fun t : ℝ => t ^ (δ / 2)) :=
    ((isLittleO_log_rpow_atTop (by positivity : (0 : ℝ) < δ / 2)).isBigO).add
      (isBigO_const_rpow (by positivity))
  have hmul := (isBigO_refl (fun t : ℝ => t ^ (-δ - 1)) atTop).mul hlogO
  refine hmul.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [← Real.rpow_add ht, show -δ - 1 + δ / 2 = -1 - δ / 2 by ring, one_mul]

/-- **The improper Abel representation of the prime zeta function.** -/
theorem primeZeta_eq_abel_integral {δ : ℝ} (hδ : 0 < δ) :
    primeZeta (1 + δ) = δ * ∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) * primeRecipSum ⌊t⌋₊ := by
  have hs : 1 < 1 + δ := by linarith
  have hc0 : primeRecipWeight 0 = 0 := by simp [primeRecipWeight]
  have hf_diff : ∀ t ∈ Ici (1 : ℝ), DifferentiableAt ℝ (rpowNeg δ) t :=
    fun t ht => (hasDerivAt_rpowNeg (lt_of_lt_of_le zero_lt_one ht)).differentiableAt
  have hg_int : IntegrableAtFilter (fun t : ℝ => t ^ (-1 - δ / 2)) atTop := by
    refine ⟨Ioi (1 : ℝ), Ioi_mem_atTop 1, ?_⟩
    exact integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have habel := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (c := primeRecipWeight)
    (f := rpowNeg δ) hc0 hf_diff (locallyIntegrableOn_deriv_rpowNeg δ)
    (tendsto_rpowNeg_mul_primeRecipSum hδ)
    (isBigO_derivRpowNeg_mul_primeRecipSum hδ) hg_int
  have hpartial : Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, rpowNeg δ k * primeRecipWeight k)
      atTop (nhds (primeZeta (1 + δ))) := by
    have hsum := summable_primeIndicatorRpow hs
    have h := hsum.hasSum.tendsto_sum_nat
    have hshift : Tendsto (fun n : ℕ =>
        ∑ k ∈ Finset.range (n + 1), (if k.Prime then ((k : ℝ)) ^ (-(1 + δ)) else 0)) atTop
        (nhds (∑' n : ℕ, if n.Prime then ((n : ℝ)) ^ (-(1 + δ)) else 0)) :=
      h.comp (tendsto_add_atTop_nat 1)
    rw [tsum_primeIndicatorRpow hs] at hshift
    refine hshift.congr fun n => ?_
    rw [sum_rpowNeg_mul_primeRecipWeight]
    congr 1
    ext k
    simp [Finset.mem_Icc, Finset.mem_range]
  have hval := tendsto_nhds_unique hpartial habel
  have hderiv : (∫ t in Ioi (1 : ℝ),
      deriv (rpowNeg δ) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeRecipWeight k) =
      -δ * ∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) * primeRecipSum ⌊t⌋₊ := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [deriv_rpowNeg (lt_trans zero_lt_one ht), primeRecipSum]
    ring
  rw [hval, hderiv]
  ring

end

end RHTower
