import GaloisForLFunctions.RHTower.PrimeZetaAbelRepresentation
import GaloisForLFunctions.RHTower.MertensConstantIdentification

/-!
# The Abelian pole of the prime log-zeta function

For `δ > 0` put

```text
P_log(1 + δ) = ∑_p (log p) p^(-1-δ) .
```

Improper Abel summation against Mertens' first theorem `∑_{p ≤ t} (log p)/p = log t + O(1)` gives

```text
P_log(1 + δ) = δ ∫_1^∞ t^(-δ-1) (∑_{p ≤ t} (log p)/p) dt = 1/δ + O(1),
```

hence the Abelian normalisation

```text
δ · P_log(1 + δ) → 1     as δ → 0⁺ .
```

The exact elementary integral `∫_1^∞ t^(-δ-1) log t dt = 1/δ²` supplies the main term and the
uniform Mertens error supplies the `O(1)`.  No prime number theorem is used: Mertens' first
theorem suffices.
-/

open Filter Topology MeasureTheory Set Asymptotics
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The elementary logarithmic power integral -/

/-- The antiderivative of `t^(-δ-1) log t`. -/
def logRpowPrimitive (δ t : ℝ) : ℝ :=
  -(Real.log t) * t ^ (-δ) / δ - t ^ (-δ) / δ ^ 2

theorem hasDerivAt_logRpowPrimitive {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (logRpowPrimitive δ) (t ^ (-δ - 1) * Real.log t) t := by
  have hpow : HasDerivAt (fun x : ℝ => x ^ (-δ)) (-δ * t ^ (-δ - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht.ne'
  have hmul : HasDerivAt (fun x : ℝ => -(Real.log x) * x ^ (-δ))
      (-(t⁻¹) * t ^ (-δ) + -(Real.log t) * (-δ * t ^ (-δ - 1))) t := by
    exact (hlog.neg).mul hpow
  have hd := (hmul.div_const δ).sub (hpow.div_const (δ ^ 2))
  refine hd.congr_deriv ?_
  have hδne : δ ≠ 0 := ne_of_gt hδ
  have htne : t ≠ 0 := ne_of_gt ht
  have hpowsplit : t * t ^ (-δ - 1) = t ^ (-δ) := by
    have h := Real.rpow_add ht 1 (-δ - 1)
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    ring
  rw [← hpowsplit]
  field_simp
  ring

theorem tendsto_logRpowPrimitive {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (logRpowPrimitive δ) atTop (nhds 0) := by
  have h1 : Tendsto (fun t : ℝ => Real.log t / t ^ δ) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop hδ).tendsto_div_nhds_zero
  have h2 : Tendsto (fun t : ℝ => (1 : ℝ) / t ^ δ) atTop (nhds 0) := by
    refine Tendsto.div_atTop tendsto_const_nhds (tendsto_rpow_atTop hδ)
  have h : Tendsto (fun t : ℝ => -(Real.log t / t ^ δ) / δ - (1 / t ^ δ) / δ ^ 2)
      atTop (nhds 0) := by
    have := ((h1.neg).div_const δ).sub (h2.div_const (δ ^ 2))
    simpa using this
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [logRpowPrimitive, Real.rpow_neg ht.le]
  have hne : (t : ℝ) ^ δ ≠ 0 := by positivity
  field_simp

theorem integrableOn_rpow_mul_log_Ioi_one {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ => t ^ (-δ - 1) * Real.log t) (Ioi (1 : ℝ)) := by
  have hmaj : IntegrableOn (fun t : ℝ => (2 / δ) * t ^ (-1 - δ / 2)) (Ioi (1 : ℝ)) := by
    have h : IntegrableOn (fun t : ℝ => t ^ (-1 - δ / 2)) (Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    exact h.const_mul _
  have hne : ∀ t ∈ Ioi (1 : ℝ), t ≠ 0 := by
    intro t ht
    have h1 : (1 : ℝ) < t := ht
    linarith
  refine Integrable.mono' hmaj ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul ?_ ?_
    · exact ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (hne t ht)
    · exact Real.continuousOn_log.mono fun t ht => Set.mem_compl_singleton_iff.mpr (hne t ht)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hlog : 0 ≤ Real.log t := Real.log_nonneg ht1.le
    have hbound : Real.log t ≤ t ^ (δ / 2) / (δ / 2) :=
      Real.log_le_rpow_div ht0.le (by positivity)
    have hpow : (0 : ℝ) < t ^ (-δ - 1) := Real.rpow_pos_of_pos ht0 _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc t ^ (-δ - 1) * Real.log t ≤ t ^ (-δ - 1) * (t ^ (δ / 2) / (δ / 2)) :=
          mul_le_mul_of_nonneg_left hbound hpow.le
      _ = (2 / δ) * t ^ (-1 - δ / 2) := by
          have hadd : t ^ (-δ - 1) * t ^ (δ / 2) = t ^ (-1 - δ / 2) := by
            rw [← Real.rpow_add ht0]
            congr 1
            ring
          rw [← mul_div_assoc, hadd]
          field_simp

/-- **The elementary logarithmic power integral.**  `∫_1^∞ t^(-δ-1) log t dt = 1/δ²`. -/
theorem integral_rpow_mul_log_Ioi_one {δ : ℝ} (hδ : 0 < δ) :
    (∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) * Real.log t) = 1 / δ ^ 2 := by
  have hcont : ContinuousWithinAt (logRpowPrimitive δ) (Ici (1 : ℝ)) 1 := by
    refine (hasDerivAt_logRpowPrimitive hδ (by norm_num : (0:ℝ) < 1)).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Ioi (1 : ℝ),
      HasDerivAt (logRpowPrimitive δ) (x ^ (-δ - 1) * Real.log x) x := by
    intro x hx
    exact hasDerivAt_logRpowPrimitive hδ (lt_trans zero_lt_one hx)
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (integrableOn_rpow_mul_log_Ioi_one hδ) (tendsto_logRpowPrimitive hδ)
  rw [h, logRpowPrimitive]
  simp [Real.log_one, Real.one_rpow]

/-! ## The prime log-zeta function -/

/-- The prime log-zeta function `∑_p (log p) p^(-s)`. -/
def primeLogZeta (s : ℝ) : ℝ :=
  ∑' p : Nat.Primes, Real.log ((p : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ (-s)

theorem summable_primeLogIndicatorRpow {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => if n.Prime then Real.log n * ((n : ℝ)) ^ (-s) else 0) := by
  set e : ℝ := (s - 1) / 2 with he
  have he0 : 0 < e := by rw [he]; linarith
  have hmaj : Summable (fun n : ℕ => (1 / e) * ((n : ℝ)) ^ (-(s - e))) := by
    have h0 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (s - e)) :=
      Real.summable_one_div_nat_rpow.mpr (by rw [he]; linarith)
    have h1 : Summable (fun n : ℕ => ((n : ℝ)) ^ (-(s - e))) := by
      refine h0.congr fun n => ?_
      rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]
    exact h1.mul_left _
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · split_ifs with hp
    · exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_le)) (Real.rpow_nonneg (by positivity) _)
    · exact le_rfl
  · split_ifs with hp
    · have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp.one_le
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      have hlog : Real.log n ≤ ((n : ℝ)) ^ e / e := Real.log_le_rpow_div hn0 he0
      have hpow : (0 : ℝ) < ((n : ℝ)) ^ (-s) := Real.rpow_pos_of_pos hnpos _
      calc Real.log n * ((n : ℝ)) ^ (-s) ≤ (((n : ℝ)) ^ e / e) * ((n : ℝ)) ^ (-s) :=
            mul_le_mul_of_nonneg_right hlog hpow.le
        _ = (1 / e) * ((n : ℝ)) ^ (-(s - e)) := by
            have hadd : ((n : ℝ)) ^ e * ((n : ℝ)) ^ (-s) = ((n : ℝ)) ^ (-(s - e)) := by
              rw [← Real.rpow_add hnpos]
              congr 1
              ring
            rw [div_mul_eq_mul_div, hadd]
            field_simp
    · exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem tsum_primeLogIndicatorRpow {s : ℝ} :
    (∑' n : ℕ, if n.Prime then Real.log n * ((n : ℝ)) ^ (-s) else 0) = primeLogZeta s := by
  rw [primeLogZeta]
  have hsupp : Function.support
      (fun n : ℕ => if n.Prime then Real.log n * ((n : ℝ)) ^ (-s) else 0) ⊆
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

/-! ## The Abel representation -/

private def rpowNegP (δ : ℝ) (t : ℝ) : ℝ := t ^ (-δ)

private theorem hasDerivAt_rpowNegP {δ t : ℝ} (ht : 0 < t) :
    HasDerivAt (rpowNegP δ) (-δ * t ^ (-δ - 1)) t :=
  Real.hasDerivAt_rpow_const (Or.inl ht.ne')

private theorem deriv_rpowNegP {δ t : ℝ} (ht : 0 < t) :
    deriv (rpowNegP δ) t = -δ * t ^ (-δ - 1) := (hasDerivAt_rpowNegP ht).deriv

private theorem locallyIntegrableOn_deriv_rpowNegP (δ : ℝ) :
    LocallyIntegrableOn (deriv (rpowNegP δ)) (Ici (1 : ℝ)) := by
  have hcont : ContinuousOn (deriv (rpowNegP δ)) (Ici (1 : ℝ)) := by
    have hc : ContinuousOn (fun t : ℝ => -δ * t ^ (-δ - 1)) (Ici (1 : ℝ)) := by
      refine continuousOn_const.mul ?_
      refine ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl ?_
      have h1 : (1 : ℝ) ≤ t := ht
      intro h
      rw [h] at h1
      linarith
    exact hc.congr fun t ht => deriv_rpowNegP (lt_of_lt_of_le zero_lt_one ht)
  exact hcont.locallyIntegrableOn measurableSet_Ici

private theorem tendsto_rpowNegP_mul_mertensPrimeWeightSum {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => rpowNegP δ n * mertensPrimeWeightSum n) atTop (nhds 0) := by
  have hmajor : Tendsto
      (fun n : ℕ => ((n : ℝ) ^ (-δ) * (Real.log n + mertensPrimeWindowBound)))
      atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_mul_log hδ).comp tendsto_natCast_atTop_atTop
    exact h
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hmajor
  · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (mertensPrimeWeightSum_nonneg n)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 : mertensPrimeWeightSum 0 = 0 := by
        simp [mertensPrimeWeightSum, mertensPrimeWeight]
      have hz : (((0 : ℕ) : ℝ)) ^ (-δ) = 0 := by
        rw [Nat.cast_zero, Real.zero_rpow (by linarith : -δ ≠ 0)]
      rw [rpowNegP, h0, mul_zero, hz, zero_mul]
    · have hbound := mertensPrimeWeightSum_le n hn
      have hpow : (0 : ℝ) ≤ (n : ℝ) ^ (-δ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      rw [rpowNegP]
      exact mul_le_mul_of_nonneg_left hbound hpow

private theorem sum_rpowNegP_mul_mertensPrimeWeight (δ : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 0 n, rpowNegP δ k * mertensPrimeWeight k =
      ∑ k ∈ Finset.Icc 0 n, (if k.Prime then Real.log k * ((k : ℝ)) ^ (-(1 + δ)) else 0) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [rpowNegP, mertensPrimeWeight]
  by_cases hp : k.Prime
  · have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hp.pos
    rw [if_pos hp, if_pos hp]
    rw [div_eq_mul_inv, ← Real.rpow_neg_one (k : ℝ)]
    rw [show -(1 + δ) = -δ + -1 by ring, Real.rpow_add hk0]
    ring
  · rw [if_neg hp, if_neg hp, mul_zero]

private theorem isBigO_const_rpowP {C r : ℝ} (hr : 0 < r) :
    (fun _ : ℝ => C) =O[atTop] (fun t : ℝ => t ^ r) := by
  refine IsBigO.of_bound |C| ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have h1 : (1 : ℝ) ≤ t ^ r := Real.one_le_rpow ht hr.le
  have hpos : (0 : ℝ) ≤ t ^ r := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos]
  nlinarith [abs_nonneg C]

private theorem isBigO_derivRpowNegP_mul_mertens {δ : ℝ} (hδ : 0 < δ) :
    (fun t : ℝ => deriv (rpowNegP δ) t * mertensPrimeWeightSum ⌊t⌋₊) =O[atTop]
      (fun t : ℝ => t ^ (-1 - δ / 2)) := by
  have hD : 0 ≤ mertensPrimeWindowBound := mertensPrimeWindowBound_nonneg
  have hb : (fun t : ℝ => deriv (rpowNegP δ) t * mertensPrimeWeightSum ⌊t⌋₊) =O[atTop]
      (fun t : ℝ => t ^ (-δ - 1) * (Real.log t + mertensPrimeWindowBound)) := by
    refine IsBigO.of_bound δ ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hfloor1 : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr (by linarith)
    have hfloorle : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0.le
    have hfloorpos : (0 : ℝ) < ((⌊t⌋₊ : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hfloor1
    have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
    have hAle : mertensPrimeWeightSum ⌊t⌋₊ ≤ Real.log t + mertensPrimeWindowBound := by
      refine (mertensPrimeWeightSum_le _ hfloor1).trans ?_
      gcongr
    have hA0 : 0 ≤ mertensPrimeWeightSum ⌊t⌋₊ := mertensPrimeWeightSum_nonneg _
    have hpow : (0 : ℝ) < t ^ (-δ - 1) := Real.rpow_pos_of_pos ht0 _
    have hlogD : (0 : ℝ) ≤ Real.log t + mertensPrimeWindowBound := by linarith
    rw [deriv_rpowNegP ht0, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hpow.le hlogD), abs_mul, abs_mul, abs_neg,
      abs_of_pos hδ, abs_of_nonneg hpow.le, abs_of_nonneg hA0]
    calc δ * t ^ (-δ - 1) * mertensPrimeWeightSum ⌊t⌋₊
        ≤ δ * t ^ (-δ - 1) * (Real.log t + mertensPrimeWindowBound) :=
          mul_le_mul_of_nonneg_left hAle (by positivity)
      _ = δ * (t ^ (-δ - 1) * (Real.log t + mertensPrimeWindowBound)) := by ring
  refine hb.trans ?_
  have hlogO : (fun t : ℝ => Real.log t + mertensPrimeWindowBound) =O[atTop]
      (fun t : ℝ => t ^ (δ / 2)) :=
    ((isLittleO_log_rpow_atTop (by positivity : (0 : ℝ) < δ / 2)).isBigO).add
      (isBigO_const_rpowP (by positivity))
  have hmul := (isBigO_refl (fun t : ℝ => t ^ (-δ - 1)) atTop).mul hlogO
  refine hmul.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [← Real.rpow_add ht, show -δ - 1 + δ / 2 = -1 - δ / 2 by ring, one_mul]

/-- **The improper Abel representation of the prime log-zeta function.** -/
theorem primeLogZeta_eq_abel_integral {δ : ℝ} (hδ : 0 < δ) :
    primeLogZeta (1 + δ) = δ * ∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) * mertensPrimeWeightSum ⌊t⌋₊ := by
  have hs : 1 < 1 + δ := by linarith
  have hc0 : mertensPrimeWeight 0 = 0 := by simp [mertensPrimeWeight]
  have hf_diff : ∀ t ∈ Ici (1 : ℝ), DifferentiableAt ℝ (rpowNegP δ) t :=
    fun t ht => (hasDerivAt_rpowNegP (lt_of_lt_of_le zero_lt_one ht)).differentiableAt
  have hg_int : IntegrableAtFilter (fun t : ℝ => t ^ (-1 - δ / 2)) atTop := by
    refine ⟨Ioi (1 : ℝ), Ioi_mem_atTop 1, ?_⟩
    exact integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have habel := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (c := mertensPrimeWeight)
    (f := rpowNegP δ) hc0 hf_diff (locallyIntegrableOn_deriv_rpowNegP δ)
    (tendsto_rpowNegP_mul_mertensPrimeWeightSum hδ)
    (isBigO_derivRpowNegP_mul_mertens hδ) hg_int
  have hpartial : Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, rpowNegP δ k * mertensPrimeWeight k)
      atTop (nhds (primeLogZeta (1 + δ))) := by
    have hsum := summable_primeLogIndicatorRpow hs
    have h := hsum.hasSum.tendsto_sum_nat
    have hshift : Tendsto (fun n : ℕ =>
        ∑ k ∈ Finset.range (n + 1),
          (if k.Prime then Real.log k * ((k : ℝ)) ^ (-(1 + δ)) else 0)) atTop
        (nhds (∑' n : ℕ, if n.Prime then Real.log n * ((n : ℝ)) ^ (-(1 + δ)) else 0)) :=
      h.comp (tendsto_add_atTop_nat 1)
    rw [tsum_primeLogIndicatorRpow] at hshift
    refine hshift.congr fun n => ?_
    rw [sum_rpowNegP_mul_mertensPrimeWeight]
    congr 1
    ext k
    simp [Finset.mem_Icc, Finset.mem_range]
  have hval := tendsto_nhds_unique hpartial habel
  have hderiv : (∫ t in Ioi (1 : ℝ),
      deriv (rpowNegP δ) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mertensPrimeWeight k) =
      -δ * ∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) * mertensPrimeWeightSum ⌊t⌋₊ := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [deriv_rpowNegP (lt_trans zero_lt_one ht), mertensPrimeWeightSum]
    ring
  rw [hval, hderiv]
  ring

/-! ## The Abelian pole -/

/-- Uniform bound on the Mertens floor error over `(1, ∞)`. -/
def mertensFloorErrorBound : ℝ := mertensPrimeWindowBound + 1 + Real.log 2

theorem mertensFloorErrorBound_nonneg : 0 ≤ mertensFloorErrorBound := by
  have h1 : 0 ≤ mertensPrimeWindowBound := mertensPrimeWindowBound_nonneg
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [mertensFloorErrorBound]
  linarith

theorem mertensPrimeWeightSum_one : mertensPrimeWeightSum 1 = 0 := by
  rw [mertensPrimeWeightSum, show Finset.Icc 0 1 = ({0, 1} : Finset ℕ) by decide]
  norm_num [mertensPrimeWeight]

theorem abs_mertensFloorError_uniform_le {t : ℝ} (ht : 1 < t) :
    |mertensPrimeWeightSum ⌊t⌋₊ - Real.log t| ≤ mertensFloorErrorBound := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hB : 0 ≤ mertensPrimeWindowBound := mertensPrimeWindowBound_nonneg
  rcases le_or_gt 2 t with h2 | h2
  · have h := abs_mertensPrimeWeightSum_floor_sub_log_le h2
    rw [mertensFloorErrorBound]
    linarith
  · have hfloor : ⌊t⌋₊ = 1 := by
      have h1 : (1 : ℝ) ≤ t := ht.le
      rw [Nat.floor_eq_iff (by linarith)]
      constructor
      · exact_mod_cast h1
      · push_cast
        linarith
    rw [hfloor, mertensPrimeWeightSum_one, zero_sub, abs_neg]
    have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht.le
    have hle : Real.log t ≤ Real.log 2 := Real.log_le_log (by linarith) h2.le
    rw [abs_of_nonneg hlogt, mertensFloorErrorBound]
    linarith

theorem measurable_mertensPrimeWeightSum_floor :
    Measurable (fun t : ℝ => mertensPrimeWeightSum ⌊t⌋₊) := by
  have h : Measurable (fun n : ℕ => mertensPrimeWeightSum n) := measurable_from_top
  exact h.comp Nat.measurable_floor

theorem integrableOn_rpow_mul_mertensFloor {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ => t ^ (-δ - 1) * mertensPrimeWeightSum ⌊t⌋₊) (Ioi (1 : ℝ)) := by
  have hrpow : IntegrableOn (fun t : ℝ => t ^ (-δ - 1)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hmaj : IntegrableOn
      (fun t : ℝ => t ^ (-δ - 1) * Real.log t + mertensFloorErrorBound * t ^ (-δ - 1))
      (Ioi (1 : ℝ)) :=
    (integrableOn_rpow_mul_log_Ioi_one hδ).add (hrpow.const_mul _)
  refine Integrable.mono' hmaj ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl ?_
      have h1 : (1 : ℝ) < t := ht
      intro h
      rw [h] at h1
      linarith
    · exact measurable_mertensPrimeWeightSum_floor.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hlog : 0 ≤ Real.log t := Real.log_nonneg ht1.le
    have hpow : (0 : ℝ) < t ^ (-δ - 1) := Real.rpow_pos_of_pos ht0 _
    have hA0 : 0 ≤ mertensPrimeWeightSum ⌊t⌋₊ := mertensPrimeWeightSum_nonneg _
    have herr := abs_mertensFloorError_uniform_le ht1
    have hAle : mertensPrimeWeightSum ⌊t⌋₊ ≤ Real.log t + mertensFloorErrorBound := by
      have := (abs_le.mp herr).2
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hpow.le hA0)]
    calc t ^ (-δ - 1) * mertensPrimeWeightSum ⌊t⌋₊
        ≤ t ^ (-δ - 1) * (Real.log t + mertensFloorErrorBound) :=
          mul_le_mul_of_nonneg_left hAle hpow.le
      _ = t ^ (-δ - 1) * Real.log t + mertensFloorErrorBound * t ^ (-δ - 1) := by ring

theorem abs_abelIntegral_sub_le {δ : ℝ} (hδ : 0 < δ) :
    |(∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) * mertensPrimeWeightSum ⌊t⌋₊) - 1 / δ ^ 2|
      ≤ mertensFloorErrorBound / δ := by
  have h1 := integrableOn_rpow_mul_mertensFloor hδ
  have h2 := integrableOn_rpow_mul_log_Ioi_one hδ
  have hrpow : IntegrableOn (fun t : ℝ => t ^ (-δ - 1)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hsub : (∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) * mertensPrimeWeightSum ⌊t⌋₊)
      - (∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) * Real.log t)
      = ∫ t in Ioi (1 : ℝ),
          (t ^ (-δ - 1) * mertensPrimeWeightSum ⌊t⌋₊ - t ^ (-δ - 1) * Real.log t) :=
    (MeasureTheory.integral_sub h1 h2).symm
  rw [integral_rpow_mul_log_Ioi_one hδ] at hsub
  rw [hsub]
  have hnorm : ∀ t ∈ Ioi (1 : ℝ),
      ‖t ^ (-δ - 1) * mertensPrimeWeightSum ⌊t⌋₊ - t ^ (-δ - 1) * Real.log t‖
        ≤ mertensFloorErrorBound * t ^ (-δ - 1) := by
    intro t ht
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hpow : (0 : ℝ) < t ^ (-δ - 1) := Real.rpow_pos_of_pos ht0 _
    have herr := abs_mertensFloorError_uniform_le ht1
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg hpow.le]
    calc t ^ (-δ - 1) * |mertensPrimeWeightSum ⌊t⌋₊ - Real.log t|
        ≤ t ^ (-δ - 1) * mertensFloorErrorBound :=
          mul_le_mul_of_nonneg_left herr hpow.le
      _ = mertensFloorErrorBound * t ^ (-δ - 1) := by ring
  have hint : IntegrableOn
      (fun t : ℝ => t ^ (-δ - 1) * mertensPrimeWeightSum ⌊t⌋₊ - t ^ (-δ - 1) * Real.log t)
      (Ioi (1 : ℝ)) := h1.sub h2
  have hle : ‖∫ t in Ioi (1 : ℝ),
      (t ^ (-δ - 1) * mertensPrimeWeightSum ⌊t⌋₊ - t ^ (-δ - 1) * Real.log t)‖
      ≤ ∫ t in Ioi (1 : ℝ), mertensFloorErrorBound * t ^ (-δ - 1) := by
    refine norm_integral_le_of_norm_le ((hrpow.const_mul _)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hnorm t ht
  rw [Real.norm_eq_abs] at hle
  refine le_trans hle ?_
  rw [MeasureTheory.integral_const_mul, integral_rpow_neg_Ioi hδ 1 one_pos]
  rw [Real.one_rpow]
  rw [mul_one_div]

/-- **The Abelian pole of the prime log-zeta function.**
`δ · ∑_p (log p) p^(-1-δ) → 1` as `δ → 0⁺`. -/
theorem tendsto_mul_primeLogZeta :
    Tendsto (fun δ : ℝ => δ * primeLogZeta (1 + δ)) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  rw [← tendsto_sub_nhds_zero_iff]
  have hmaj : Tendsto (fun δ : ℝ => δ * mertensFloorErrorBound) (nhdsWithin 0 (Ioi 0))
      (nhds 0) := by
    have h : Tendsto (fun δ : ℝ => δ * mertensFloorErrorBound) (nhds 0) (nhds 0) := by
      have hx : Tendsto (fun δ : ℝ => δ) (nhds 0) (nhds 0) := tendsto_id
      simpa using hx.mul_const mertensFloorErrorBound
    exact h.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [self_mem_nhdsWithin] with δ hδ0
  have hδ : (0 : ℝ) < δ := hδ0
  have habel := primeLogZeta_eq_abel_integral hδ
  set I : ℝ := ∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) * mertensPrimeWeightSum ⌊t⌋₊ with hI
  have hkey : δ * primeLogZeta (1 + δ) - 1 = δ ^ 2 * (I - 1 / δ ^ 2) := by
    rw [habel]
    have hne : (δ : ℝ) ≠ 0 := ne_of_gt hδ
    field_simp
  rw [Real.norm_eq_abs, hkey, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ δ ^ 2)]
  calc δ ^ 2 * |I - 1 / δ ^ 2| ≤ δ ^ 2 * (mertensFloorErrorBound / δ) :=
        mul_le_mul_of_nonneg_left (abs_abelIntegral_sub_le hδ) (by positivity)
    _ = δ * mertensFloorErrorBound := by field_simp

/-! ## A general Abel representation for logarithmically bounded prime weights -/

/-- Partial sums of an arithmetic weight. -/
def weightPartialSum (c : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 0 n, c k

theorem tendsto_rpow_neg_mul_logAffine {δ : ℝ} (hδ : 0 < δ) (K : ℝ) :
    Tendsto (fun t : ℝ => t ^ (-δ) * (K * (Real.log t + 1))) atTop (nhds 0) := by
  have h1 : Tendsto (fun t : ℝ => Real.log t / t ^ δ) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop hδ).tendsto_div_nhds_zero
  have h2 : Tendsto (fun t : ℝ => (1 : ℝ) / t ^ δ) atTop (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds (tendsto_rpow_atTop hδ)
  have h : Tendsto (fun t : ℝ => K * (Real.log t / t ^ δ + 1 / t ^ δ)) atTop (nhds 0) := by
    have := (h1.add h2).const_mul K
    simpa using this
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [Real.rpow_neg ht.le]
  have hne : (t : ℝ) ^ δ ≠ 0 := by positivity
  field_simp

private theorem locallyIntegrableOn_deriv_rpowNegP' (δ : ℝ) :
    LocallyIntegrableOn (deriv (rpowNegP δ)) (Ici (1 : ℝ)) :=
  locallyIntegrableOn_deriv_rpowNegP δ

/-- **Abel representation of a logarithmically bounded arithmetic Dirichlet series.** -/
theorem weightedDirichlet_eq_abel_integral {c : ℕ → ℝ} (hc0 : c 0 = 0)
    (hcnn : ∀ n, 0 ≤ c n) {K : ℝ} (hK0 : 0 ≤ K)
    (hbound : ∀ n : ℕ, weightPartialSum c n ≤ K * (Real.log n + 1))
    {δ : ℝ} (hδ : 0 < δ) (hsum : Summable (fun n : ℕ => c n * ((n : ℝ)) ^ (-δ))) :
    (∑' n : ℕ, c n * ((n : ℝ)) ^ (-δ))
      = δ * ∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) * weightPartialSum c ⌊t⌋₊ := by
  have hSnn : ∀ n : ℕ, 0 ≤ weightPartialSum c n :=
    fun n => Finset.sum_nonneg fun k _ => hcnn k
  have hf_diff : ∀ t ∈ Ici (1 : ℝ), DifferentiableAt ℝ (rpowNegP δ) t :=
    fun t ht => (hasDerivAt_rpowNegP (lt_of_lt_of_le zero_lt_one ht)).differentiableAt
  have hg_int : IntegrableAtFilter (fun t : ℝ => t ^ (-1 - δ / 2)) atTop := by
    refine ⟨Ioi (1 : ℝ), Ioi_mem_atTop 1, ?_⟩
    exact integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have htend : Tendsto (fun n : ℕ => rpowNegP δ n * weightPartialSum c n) atTop (nhds 0) := by
    have hmajor : Tendsto
        (fun n : ℕ => ((n : ℝ) ^ (-δ) * (K * (Real.log n + 1)))) atTop (nhds 0) :=
      (tendsto_rpow_neg_mul_logAffine hδ K).comp tendsto_natCast_atTop_atTop
    refine squeeze_zero (fun n => ?_) (fun n => ?_) hmajor
    · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (hSnn n)
    · exact mul_le_mul_of_nonneg_left (hbound n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hbigO : (fun t : ℝ => deriv (rpowNegP δ) t * weightPartialSum c ⌊t⌋₊) =O[atTop]
      (fun t : ℝ => t ^ (-1 - δ / 2)) := by
    have hb : (fun t : ℝ => deriv (rpowNegP δ) t * weightPartialSum c ⌊t⌋₊) =O[atTop]
        (fun t : ℝ => t ^ (-δ - 1) * (K * (Real.log t + 1))) := by
      refine IsBigO.of_bound δ ?_
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
      have ht0 : (0 : ℝ) < t := by linarith
      have hfloor1 : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr (by linarith)
      have hfloorle : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0.le
      have hfloorpos : (0 : ℝ) < ((⌊t⌋₊ : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hfloor1
      have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
      have hAle : weightPartialSum c ⌊t⌋₊ ≤ K * (Real.log t + 1) := by
        refine (hbound ⌊t⌋₊).trans ?_
        have : Real.log ((⌊t⌋₊ : ℕ) : ℝ) ≤ Real.log t := Real.log_le_log hfloorpos hfloorle
        nlinarith
      have hpow : (0 : ℝ) < t ^ (-δ - 1) := Real.rpow_pos_of_pos ht0 _
      have hlogD : (0 : ℝ) ≤ K * (Real.log t + 1) := by positivity
      rw [deriv_rpowNegP ht0, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hpow.le hlogD), abs_mul, abs_mul, abs_neg,
        abs_of_pos hδ, abs_of_nonneg hpow.le, abs_of_nonneg (hSnn _)]
      calc δ * t ^ (-δ - 1) * weightPartialSum c ⌊t⌋₊
          ≤ δ * t ^ (-δ - 1) * (K * (Real.log t + 1)) :=
            mul_le_mul_of_nonneg_left hAle (by positivity)
        _ = δ * (t ^ (-δ - 1) * (K * (Real.log t + 1))) := by ring
    refine hb.trans ?_
    have hlogO : (fun t : ℝ => K * (Real.log t + 1)) =O[atTop] (fun t : ℝ => t ^ (δ / 2)) := by
      have h1 : (fun t : ℝ => Real.log t + 1) =O[atTop] (fun t : ℝ => t ^ (δ / 2)) :=
        ((isLittleO_log_rpow_atTop (by positivity : (0 : ℝ) < δ / 2)).isBigO).add
          (isBigO_const_rpowP (C := (1 : ℝ)) (by positivity))
      exact h1.const_mul_left K
    have hmul := (isBigO_refl (fun t : ℝ => t ^ (-δ - 1)) atTop).mul hlogO
    refine hmul.trans (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [← Real.rpow_add ht, show -δ - 1 + δ / 2 = -1 - δ / 2 by ring, one_mul]
  have habel := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (c := c)
    (f := rpowNegP δ) hc0 hf_diff (locallyIntegrableOn_deriv_rpowNegP δ) htend hbigO hg_int
  have hpartial : Tendsto (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, rpowNegP δ k * c k)
      atTop (nhds (∑' n : ℕ, c n * ((n : ℝ)) ^ (-δ))) := by
    have h := hsum.hasSum.tendsto_sum_nat
    have hshift := h.comp (tendsto_add_atTop_nat 1)
    refine hshift.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [show Finset.Icc 0 n = Finset.range (n + 1) by
      ext k
      simp [Finset.mem_Icc, Finset.mem_range]]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [rpowNegP]
    ring
  have hval := tendsto_nhds_unique hpartial habel
  have hderiv : (∫ t in Ioi (1 : ℝ), deriv (rpowNegP δ) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =
      -δ * ∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) * weightPartialSum c ⌊t⌋₊ := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [deriv_rpowNegP (lt_trans zero_lt_one ht), weightPartialSum]
    ring
  rw [hval, hderiv]
  ring

/-- **Uniform Abelian bound for logarithmically bounded weights.** -/
theorem mul_tsum_weightedDirichlet_le {c : ℕ → ℝ} (hc0 : c 0 = 0)
    (hcnn : ∀ n, 0 ≤ c n) {K : ℝ} (hK0 : 0 ≤ K)
    (hbound : ∀ n : ℕ, weightPartialSum c n ≤ K * (Real.log n + 1))
    {δ : ℝ} (hδ : 0 < δ) (hsum : Summable (fun n : ℕ => c n * ((n : ℝ)) ^ (-δ))) :
    δ * (∑' n : ℕ, c n * ((n : ℝ)) ^ (-δ)) ≤ K * (1 + δ) := by
  have hSnn : ∀ n : ℕ, 0 ≤ weightPartialSum c n :=
    fun n => Finset.sum_nonneg fun k _ => hcnn k
  have hrpow : IntegrableOn (fun t : ℝ => t ^ (-δ - 1)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hmaj : IntegrableOn
      (fun t : ℝ => K * (t ^ (-δ - 1) * Real.log t) + K * t ^ (-δ - 1)) (Ioi (1 : ℝ)) :=
    ((integrableOn_rpow_mul_log_Ioi_one hδ).const_mul _).add (hrpow.const_mul _)
  have hint : IntegrableOn (fun t : ℝ => t ^ (-δ - 1) * weightPartialSum c ⌊t⌋₊)
      (Ioi (1 : ℝ)) := by
    refine Integrable.mono' hmaj ?_ ?_
    · refine AEStronglyMeasurable.mul ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
        refine ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl ?_
        have h1 : (1 : ℝ) < t := ht
        intro h
        rw [h] at h1
        linarith
      · exact ((measurable_from_top (f := fun n : ℕ => weightPartialSum c n)).comp
          Nat.measurable_floor).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : (1 : ℝ) < t := ht
      have ht0 : (0 : ℝ) < t := by linarith
      have hlog : 0 ≤ Real.log t := Real.log_nonneg ht1.le
      have hpow : (0 : ℝ) < t ^ (-δ - 1) := Real.rpow_pos_of_pos ht0 _
      have hfloor1 : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr (by linarith)
      have hfloorle : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0.le
      have hfloorpos : (0 : ℝ) < ((⌊t⌋₊ : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hfloor1
      have hAle : weightPartialSum c ⌊t⌋₊ ≤ K * (Real.log t + 1) := by
        refine (hbound ⌊t⌋₊).trans ?_
        have : Real.log ((⌊t⌋₊ : ℕ) : ℝ) ≤ Real.log t := Real.log_le_log hfloorpos hfloorle
        nlinarith
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hpow.le (hSnn _))]
      calc t ^ (-δ - 1) * weightPartialSum c ⌊t⌋₊
          ≤ t ^ (-δ - 1) * (K * (Real.log t + 1)) :=
            mul_le_mul_of_nonneg_left hAle hpow.le
        _ = K * (t ^ (-δ - 1) * Real.log t) + K * t ^ (-δ - 1) := by ring
  have hmono : (∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) * weightPartialSum c ⌊t⌋₊)
      ≤ ∫ t in Ioi (1 : ℝ), (K * (t ^ (-δ - 1) * Real.log t) + K * t ^ (-δ - 1)) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hmaj ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : (1 : ℝ) < t := ht
      have ht0 : (0 : ℝ) < t := by linarith
      exact mul_nonneg (Real.rpow_pos_of_pos ht0 _).le (hSnn _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : (1 : ℝ) < t := ht
      have ht0 : (0 : ℝ) < t := by linarith
      have hlog : 0 ≤ Real.log t := Real.log_nonneg ht1.le
      have hpow : (0 : ℝ) < t ^ (-δ - 1) := Real.rpow_pos_of_pos ht0 _
      have hfloor1 : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr (by linarith)
      have hfloorle : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0.le
      have hfloorpos : (0 : ℝ) < ((⌊t⌋₊ : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hfloor1
      have hAle : weightPartialSum c ⌊t⌋₊ ≤ K * (Real.log t + 1) := by
        refine (hbound ⌊t⌋₊).trans ?_
        have : Real.log ((⌊t⌋₊ : ℕ) : ℝ) ≤ Real.log t := Real.log_le_log hfloorpos hfloorle
        nlinarith
      calc t ^ (-δ - 1) * weightPartialSum c ⌊t⌋₊
          ≤ t ^ (-δ - 1) * (K * (Real.log t + 1)) :=
            mul_le_mul_of_nonneg_left hAle hpow.le
        _ = K * (t ^ (-δ - 1) * Real.log t) + K * t ^ (-δ - 1) := by ring
  have hvalue : (∫ t in Ioi (1 : ℝ), (K * (t ^ (-δ - 1) * Real.log t) + K * t ^ (-δ - 1)))
      = K * (1 / δ ^ 2) + K * (1 / δ) := by
    rw [MeasureTheory.integral_add ((integrableOn_rpow_mul_log_Ioi_one hδ).const_mul _)
      (hrpow.const_mul _), MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      integral_rpow_mul_log_Ioi_one hδ, integral_rpow_neg_Ioi hδ 1 one_pos, Real.one_rpow]
  rw [weightedDirichlet_eq_abel_integral hc0 hcnn hK0 hbound hδ hsum]
  have hfinal : δ * (δ * ∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) * weightPartialSum c ⌊t⌋₊)
      ≤ δ * (δ * (K * (1 / δ ^ 2) + K * (1 / δ))) := by
    have := mul_le_mul_of_nonneg_left (hmono.trans_eq hvalue) (le_of_lt hδ)
    exact mul_le_mul_of_nonneg_left this (le_of_lt hδ)
  refine hfinal.trans ?_
  have hne : (δ : ℝ) ≠ 0 := ne_of_gt hδ
  field_simp
  exact le_rfl

/-- **Summability and the uniform Abelian bound, from the logarithmic partial-sum bound alone.**
Truncating the weight makes the summability hypothesis of `mul_tsum_weightedDirichlet_le`
automatic. -/
theorem summable_and_mul_tsum_weightedDirichlet_le {c : ℕ → ℝ} (hc0 : c 0 = 0)
    (hcnn : ∀ n, 0 ≤ c n) {K : ℝ} (hK0 : 0 ≤ K)
    (hbound : ∀ n : ℕ, weightPartialSum c n ≤ K * (Real.log n + 1))
    {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun n : ℕ => c n * ((n : ℝ)) ^ (-δ)) ∧
      δ * (∑' n : ℕ, c n * ((n : ℝ)) ^ (-δ)) ≤ K * (1 + δ) := by
  have hterm : ∀ n : ℕ, 0 ≤ c n * ((n : ℝ)) ^ (-δ) := fun n =>
    mul_nonneg (hcnn n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hpartial : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, c n * ((n : ℝ)) ^ (-δ)) ≤ K * (1 + δ) / δ := by
    intro N
    set cN : ℕ → ℝ := fun n => if n < N then c n else 0 with hcN
    have hcN0 : cN 0 = 0 := by
      simp only [hcN]
      split_ifs
      · exact hc0
      · rfl
    have hcNnn : ∀ n, 0 ≤ cN n := by
      intro n
      simp only [hcN]
      split_ifs
      · exact hcnn n
      · exact le_rfl
    have hcNle : ∀ n, cN n ≤ c n := by
      intro n
      simp only [hcN]
      split_ifs
      · exact le_rfl
      · exact hcnn n
    have hcNbound : ∀ n : ℕ, weightPartialSum cN n ≤ K * (Real.log n + 1) := by
      intro n
      refine le_trans (Finset.sum_le_sum fun k _ => hcNle k) (hbound n)
    have hcNsum : Summable (fun n : ℕ => cN n * ((n : ℝ)) ^ (-δ)) := by
      refine summable_of_ne_finset_zero (s := Finset.range N) fun n hn => ?_
      have : ¬ n < N := by simpa using hn
      simp only [hcN, if_neg this, zero_mul]
    have hbnd := mul_tsum_weightedDirichlet_le hcN0 hcNnn hK0 hcNbound hδ hcNsum
    have hval : (∑' n : ℕ, cN n * ((n : ℝ)) ^ (-δ))
        = ∑ n ∈ Finset.range N, c n * ((n : ℝ)) ^ (-δ) := by
      rw [tsum_eq_sum (s := Finset.range N) (fun n hn => by
        have : ¬ n < N := by simpa using hn
        simp only [hcN, if_neg this, zero_mul])]
      refine Finset.sum_congr rfl fun n hn => ?_
      have : n < N := Finset.mem_range.mp hn
      simp only [hcN, if_pos this]
    rw [hval] at hbnd
    rw [le_div_iff₀ hδ]
    linarith [hbnd]
  have hsummable : Summable (fun n : ℕ => c n * ((n : ℝ)) ^ (-δ)) :=
    summable_of_sum_range_le hterm hpartial
  refine ⟨hsummable, ?_⟩
  have hle : (∑' n : ℕ, c n * ((n : ℝ)) ^ (-δ)) ≤ K * (1 + δ) / δ :=
    hsummable.tsum_le_of_sum_range_le hpartial
  have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt hδ)
  refine hmul.trans ?_
  have hne : (δ : ℝ) ≠ 0 := ne_of_gt hδ
  field_simp
  exact le_rfl

end

end RHTower
