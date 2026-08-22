import GaloisForLFunctions.RHTower.PrimeLogZetaAbelPole
import GaloisForLFunctions.RHTower.PrimeHigherMertens
import GaloisForLFunctions.RHTower.EulerFisherCurvature

/-!
# The graded Abelian pole of the prime log-power zeta function

For `δ > 0` and `k ≥ 0` put

```text
P_{k+1}(1 + δ) = ∑_p (log p)^{k+1} p^{-1-δ} .
```

Improper Abel summation against the higher-order Mertens theorem
`∑_{p ≤ t} (log p)^{k+1}/p = (log t)^{k+1}/(k+1) + C_k + o(1)` and the elementary integral
`∫_1^∞ t^{-δ-1}(log t)^m dt = m!/δ^{m+1}` give the exact graded Abelian normalisation

```text
lim_{δ ↓ 0} δ^{k+1} P_{k+1}(1 + δ) = k! .
```
-/

open Filter MeasureTheory Set Topology

open scoped Topology

namespace RHTower

noncomputable section

/-! ## The elementary logarithmic power integral -/

/-- A uniform majorant constant for `(1 + log t)^m` against `t^{δ/2}` on `[1, ∞)`. -/
def logPowMajorantConst (δ : ℝ) (m : ℕ) : ℝ := (2 * (m : ℝ) / δ + 1) ^ m

theorem logPowMajorantConst_pos {δ : ℝ} (hδ : 0 < δ) (m : ℕ) : 0 < logPowMajorantConst δ m := by
  rw [logPowMajorantConst]
  positivity

/-- Every affine logarithmic power is dominated by a fixed positive power. -/
theorem logAffine_pow_le_majorant {δ : ℝ} (hδ : 0 < δ) (m : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    (Real.log t + 1) ^ m ≤ logPowMajorantConst δ m * t ^ (δ / 2) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  have hpow1 : (1 : ℝ) ≤ t ^ (δ / 2) := Real.one_le_rpow ht (by positivity)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [pow_zero, logPowMajorantConst]
    norm_num
    linarith
  · have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hr : (0 : ℝ) < δ / (2 * (m : ℝ)) := by positivity
    have hr1 : (1 : ℝ) ≤ t ^ (δ / (2 * (m : ℝ))) := Real.one_le_rpow ht hr.le
    have hstep : Real.log t + 1 ≤ (2 * (m : ℝ) / δ + 1) * t ^ (δ / (2 * (m : ℝ))) := by
      have hlogle : Real.log t ≤ 2 * (m : ℝ) / δ * t ^ (δ / (2 * (m : ℝ))) := by
        calc Real.log t ≤ t ^ (δ / (2 * (m : ℝ))) / (δ / (2 * (m : ℝ))) :=
              Real.log_le_rpow_div ht0.le hr
          _ = 2 * (m : ℝ) / δ * t ^ (δ / (2 * (m : ℝ))) := by field_simp
      nlinarith
    have hpm : (Real.log t + 1) ^ m
        ≤ ((2 * (m : ℝ) / δ + 1) * t ^ (δ / (2 * (m : ℝ)))) ^ m :=
      pow_le_pow_left₀ (by linarith) hstep m
    have hcollapse : ((2 * (m : ℝ) / δ + 1) * t ^ (δ / (2 * (m : ℝ)))) ^ m
        = (2 * (m : ℝ) / δ + 1) ^ m * t ^ (δ / 2) := by
      rw [mul_pow, ← Real.rpow_natCast (t ^ (δ / (2 * (m : ℝ)))) m, ← Real.rpow_mul ht0.le]
      congr 2
      field_simp
    rw [hcollapse] at hpm
    rw [logPowMajorantConst]
    exact hpm

theorem log_pow_le_majorant {δ : ℝ} (hδ : 0 < δ) (m : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    (Real.log t) ^ m ≤ logPowMajorantConst δ m * t ^ (δ / 2) :=
  le_trans (pow_le_pow_left₀ (Real.log_nonneg ht) (by linarith) m)
    (logAffine_pow_le_majorant hδ m ht)

/-- The `t^{-δ-1}`-weighted integrability of any affine logarithmic power. -/
theorem integrableOn_rpow_mul_logAffine_pow_Ioi_one {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ (-δ - 1) * (Real.log t + 1) ^ m) (Ioi (1 : ℝ)) := by
  have hmaj : IntegrableOn (fun t : ℝ => logPowMajorantConst δ m * t ^ (-1 - δ / 2))
      (Ioi (1 : ℝ)) := by
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
    · exact ((Real.continuousOn_log.mono fun t ht =>
        Set.mem_compl_singleton_iff.mpr (hne t ht)).add continuousOn_const).pow m
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hlog : 0 ≤ Real.log t := Real.log_nonneg ht1.le
    have hpow : (0 : ℝ) < t ^ (-δ - 1) := Real.rpow_pos_of_pos ht0 _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc t ^ (-δ - 1) * (Real.log t + 1) ^ m
        ≤ t ^ (-δ - 1) * (logPowMajorantConst δ m * t ^ (δ / 2)) :=
          mul_le_mul_of_nonneg_left (logAffine_pow_le_majorant hδ m ht1.le) hpow.le
      _ = logPowMajorantConst δ m * t ^ (-1 - δ / 2) := by
          have hadd : t ^ (-δ - 1) * t ^ (δ / 2) = t ^ (-1 - δ / 2) := by
            rw [← Real.rpow_add ht0]
            congr 1
            ring
          calc t ^ (-δ - 1) * (logPowMajorantConst δ m * t ^ (δ / 2))
              = logPowMajorantConst δ m * (t ^ (-δ - 1) * t ^ (δ / 2)) := by ring
            _ = logPowMajorantConst δ m * t ^ (-1 - δ / 2) := by rw [hadd]

theorem integrableOn_rpow_mul_log_pow_Ioi_one {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ (-δ - 1) * (Real.log t) ^ m) (Ioi (1 : ℝ)) := by
  have hmaj : IntegrableOn (fun t : ℝ => logPowMajorantConst δ m * t ^ (-1 - δ / 2))
      (Ioi (1 : ℝ)) := by
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
    · exact (Real.continuousOn_log.mono fun t ht =>
        Set.mem_compl_singleton_iff.mpr (hne t ht)).pow m
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hlog : 0 ≤ Real.log t := Real.log_nonneg ht1.le
    have hpow : (0 : ℝ) < t ^ (-δ - 1) := Real.rpow_pos_of_pos ht0 _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc t ^ (-δ - 1) * (Real.log t) ^ m
        ≤ t ^ (-δ - 1) * (logPowMajorantConst δ m * t ^ (δ / 2)) :=
          mul_le_mul_of_nonneg_left (log_pow_le_majorant hδ m ht1.le) hpow.le
      _ = logPowMajorantConst δ m * t ^ (-1 - δ / 2) := by
          have hadd : t ^ (-δ - 1) * t ^ (δ / 2) = t ^ (-1 - δ / 2) := by
            rw [← Real.rpow_add ht0]
            congr 1
            ring
          calc t ^ (-δ - 1) * (logPowMajorantConst δ m * t ^ (δ / 2))
              = logPowMajorantConst δ m * (t ^ (-δ - 1) * t ^ (δ / 2)) := by ring
            _ = logPowMajorantConst δ m * t ^ (-1 - δ / 2) := by rw [hadd]

/-- The antiderivative driving the recursion `I_{m+1} = ((m+1)/δ) I_m`. -/
def logPowRpowPrimitive (δ : ℝ) (m : ℕ) (t : ℝ) : ℝ := -((Real.log t) ^ m * t ^ (-δ)) / δ

theorem logPowRpowPrimitive_one_of_pos (δ : ℝ) (m : ℕ) (hm : m ≠ 0) :
    logPowRpowPrimitive δ m 1 = 0 := by
  rw [logPowRpowPrimitive, Real.log_one, zero_pow hm]
  ring

theorem hasDerivAt_logPowRpowPrimitive {δ : ℝ} (hδ : 0 < δ) (m : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (logPowRpowPrimitive δ (m + 1))
      (t ^ (-δ - 1) * (Real.log t) ^ (m + 1)
        - ((m : ℝ) + 1) / δ * (t ^ (-δ - 1) * (Real.log t) ^ m)) t := by
  have hpow : HasDerivAt (fun x : ℝ => x ^ (-δ)) (-δ * t ^ (-δ - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht.ne'
  have hlogpow : HasDerivAt (fun x : ℝ => (Real.log x) ^ (m + 1))
      (((m : ℝ) + 1) * (Real.log t) ^ m * t⁻¹) t := by
    have h := hlog.pow (m + 1)
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at h
    exact h
  have hd := ((hlogpow.mul hpow).neg).div_const δ
  refine hd.congr_deriv ?_
  have htne : t ≠ 0 := ne_of_gt ht
  have hδne : δ ≠ 0 := ne_of_gt hδ
  have hsplit : t⁻¹ * t ^ (-δ) = t ^ (-δ - 1) := by
    rw [← Real.rpow_neg_one t, ← Real.rpow_add ht]
    congr 1
    ring
  have hδinv : δ * δ⁻¹ = 1 := mul_inv_cancel₀ hδne
  linear_combination (-(((m : ℝ) + 1) * (Real.log t) ^ m / δ)) * hsplit
    + ((Real.log t) ^ (m + 1) * t ^ (-δ - 1)) * hδinv

theorem tendsto_logPowRpowPrimitive {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    Tendsto (logPowRpowPrimitive δ m) atTop (nhds 0) := by
  have hkey : Tendsto (fun t : ℝ => (Real.log t) ^ m * t ^ (-δ)) atTop (nhds 0) := by
    have hupper : Tendsto (fun t : ℝ => logPowMajorantConst δ m * t ^ (-(δ / 2)))
        atTop (nhds 0) := by
      have h : Tendsto (fun t : ℝ => t ^ (-(δ / 2))) atTop (nhds 0) :=
        tendsto_rpow_neg_atTop (by positivity)
      simpa using h.const_mul (logPowMajorantConst δ m)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      exact mul_nonneg (pow_nonneg (Real.log_nonneg ht) m)
        (Real.rpow_nonneg (by linarith) _)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      have ht0 : (0 : ℝ) < t := by linarith
      have hbound := log_pow_le_majorant hδ m ht
      have hrp : (0 : ℝ) < t ^ (-δ) := Real.rpow_pos_of_pos ht0 _
      have hcollapse : t ^ (δ / 2) * t ^ (-δ) = t ^ (-(δ / 2)) := by
        rw [← Real.rpow_add ht0]
        congr 1
        ring
      calc (Real.log t) ^ m * t ^ (-δ)
          ≤ (logPowMajorantConst δ m * t ^ (δ / 2)) * t ^ (-δ) :=
            mul_le_mul_of_nonneg_right hbound hrp.le
        _ = logPowMajorantConst δ m * (t ^ (δ / 2) * t ^ (-δ)) := by ring
        _ = logPowMajorantConst δ m * t ^ (-(δ / 2)) := by rw [hcollapse]
  have h := (hkey.neg).div_const δ
  rw [neg_zero, zero_div] at h
  refine h.congr' ?_
  filter_upwards with t
  rw [logPowRpowPrimitive]

/-- **The elementary logarithmic power integral.**  `∫_1^∞ t^(-δ-1)(log t)^m dt = m!/δ^{m+1}`. -/
theorem integral_rpow_mul_log_pow_Ioi_one {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    (∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) * (Real.log t) ^ m)
      = (Nat.factorial m : ℝ) / δ ^ (m + 1) := by
  induction m with
  | zero =>
    have h : (∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) * (Real.log t) ^ 0)
        = ∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [pow_zero, mul_one]
    rw [h, integral_Ioi_rpow_of_lt (by linarith) one_pos,
      show (-δ - 1 + 1 : ℝ) = -δ by ring, Real.one_rpow, Nat.factorial_zero]
    push_cast
    field_simp
  | succ j ih =>
    have hIj := integrableOn_rpow_mul_log_pow_Ioi_one hδ j
    have hIj1 := integrableOn_rpow_mul_log_pow_Ioi_one hδ (j + 1)
    have hderiv : ∀ x ∈ Ioi (1 : ℝ), HasDerivAt (logPowRpowPrimitive δ (j + 1))
        (x ^ (-δ - 1) * (Real.log x) ^ (j + 1)
          - ((j : ℝ) + 1) / δ * (x ^ (-δ - 1) * (Real.log x) ^ j)) x :=
      fun x hx => hasDerivAt_logPowRpowPrimitive hδ j (lt_trans zero_lt_one hx)
    have hcont : ContinuousWithinAt (logPowRpowPrimitive δ (j + 1)) (Ici (1 : ℝ)) 1 :=
      (hasDerivAt_logPowRpowPrimitive hδ j one_pos).continuousAt.continuousWithinAt
    have hint : IntegrableOn (fun t : ℝ => t ^ (-δ - 1) * (Real.log t) ^ (j + 1)
        - ((j : ℝ) + 1) / δ * (t ^ (-δ - 1) * (Real.log t) ^ j)) (Ioi (1 : ℝ)) :=
      hIj1.sub (hIj.const_mul _)
    have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint
      (tendsto_logPowRpowPrimitive hδ (j + 1))
    rw [integral_sub hIj1 (hIj.const_mul _), MeasureTheory.integral_const_mul, ih,
      logPowRpowPrimitive_one_of_pos δ (j + 1) (by omega), sub_zero] at h
    have hδne : δ ≠ 0 := ne_of_gt hδ
    have hfac : ((Nat.factorial (j + 1) : ℕ) : ℝ) = ((j : ℝ) + 1) * (Nat.factorial j : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hval : (∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) * (Real.log t) ^ (j + 1))
        = ((j : ℝ) + 1) / δ * ((Nat.factorial j : ℝ) / δ ^ (j + 1)) := by linarith
    rw [hval, hfac]
    field_simp
    ring

/-! ## The graded prime weight and its Mertens error -/

theorem primeLogPowWeight_nonneg (k n : ℕ) : 0 ≤ primeLogPowWeight k n := by
  by_cases hp : n.Prime
  · rw [primeLogPowWeight, if_pos hp]
    exact div_nonneg (pow_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le)) k)
      (Nat.cast_nonneg n)
  · rw [primeLogPowWeight, if_neg hp]

theorem primeLogPowWeight_zero_index (k : ℕ) : primeLogPowWeight k 0 = 0 := by
  rw [primeLogPowWeight, if_neg (by decide : ¬ Nat.Prime 0)]

theorem weightPartialSum_primeLogPowWeight (k n : ℕ) :
    weightPartialSum (primeLogPowWeight k) n = primeLogPowSum k (n : ℝ) := by
  rw [weightPartialSum, primeLogPowSum, Nat.floor_natCast]

theorem primeLogPowSum_nonneg (k : ℕ) (x : ℝ) : 0 ≤ primeLogPowSum k x :=
  Finset.sum_nonneg fun n _ => primeLogPowWeight_nonneg k n

theorem primeLogPowSum_mono (k : ℕ) {x y : ℝ} (h : x ≤ y) :
    primeLogPowSum k x ≤ primeLogPowSum k y := by
  rw [primeLogPowSum, primeLogPowSum]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right (Nat.floor_le_floor h))
    fun n _ _ => primeLogPowWeight_nonneg k n

theorem primeLogPowSum_floor_cast (k : ℕ) (t : ℝ) :
    primeLogPowSum k ((⌊t⌋₊ : ℕ) : ℝ) = primeLogPowSum k t := by
  rw [primeLogPowSum, primeLogPowSum, Nat.floor_natCast]

/-- The graded Mertens error `∑_{p ≤ t}(log p)^{k+1}/p - (log t)^{k+1}/(k+1) - C_k`. -/
def gradedMertensError (k : ℕ) (t : ℝ) : ℝ :=
  primeLogPowSum (k + 1) t - (Real.log t) ^ (k + 1) / ((k : ℝ) + 1)
    - mertensLogPowConstantFull k

theorem tendsto_gradedMertensError (k : ℕ) :
    Tendsto (gradedMertensError k) atTop (nhds 0) := by
  have h := (tendsto_primeLogPowSum_sub k).sub_const (mertensLogPowConstantFull k)
  rw [sub_self] at h
  exact h

/-- The graded Mertens error is globally bounded on `[1, ∞)`. -/
theorem exists_gradedMertensError_bound (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 1 ≤ t → |gradedMertensError k t| ≤ B := by
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.mp (tendsto_gradedMertensError k)) 1 one_pos
  set T' : ℝ := max T 1 with hT'def
  have hT'1 : (1 : ℝ) ≤ T' := le_max_right _ _
  refine ⟨max 1 (primeLogPowSum (k + 1) T' + (Real.log T') ^ (k + 1) / ((k : ℝ) + 1)
      + |mertensLogPowConstantFull k|), le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro t ht
  rcases le_or_gt t T' with hle | hgt
  · have hS0 : 0 ≤ primeLogPowSum (k + 1) t := primeLogPowSum_nonneg _ _
    have hSle : primeLogPowSum (k + 1) t ≤ primeLogPowSum (k + 1) T' :=
      primeLogPowSum_mono _ hle
    have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
    have hlogle : Real.log t ≤ Real.log T' := Real.log_le_log (by linarith) hle
    have hpowle : (Real.log t) ^ (k + 1) ≤ (Real.log T') ^ (k + 1) :=
      pow_le_pow_left₀ hlog hlogle _
    have hpow0 : (0 : ℝ) ≤ (Real.log t) ^ (k + 1) := pow_nonneg hlog _
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have habs := abs_le.mpr (And.intro
      (show -(primeLogPowSum (k + 1) T' + (Real.log T') ^ (k + 1) / ((k : ℝ) + 1)
          + |mertensLogPowConstantFull k|) ≤ gradedMertensError k t by
        rw [gradedMertensError]
        have h1 : (Real.log t) ^ (k + 1) / ((k : ℝ) + 1)
            ≤ (Real.log T') ^ (k + 1) / ((k : ℝ) + 1) := by gcongr
        have h2 : mertensLogPowConstantFull k ≤ |mertensLogPowConstantFull k| := le_abs_self _
        have h3 : (0 : ℝ) ≤ primeLogPowSum (k + 1) T' :=
          primeLogPowSum_nonneg _ _
        linarith)
      (show gradedMertensError k t
          ≤ primeLogPowSum (k + 1) T' + (Real.log T') ^ (k + 1) / ((k : ℝ) + 1)
            + |mertensLogPowConstantFull k| by
        rw [gradedMertensError]
        have h1 : (0 : ℝ) ≤ (Real.log t) ^ (k + 1) / ((k : ℝ) + 1) := by positivity
        have h2 : -|mertensLogPowConstantFull k| ≤ mertensLogPowConstantFull k := neg_abs_le _
        have h3 : (0 : ℝ) ≤ (Real.log T') ^ (k + 1) / ((k : ℝ) + 1) := by
          have : (0 : ℝ) ≤ Real.log T' := Real.log_nonneg hT'1
          positivity
        linarith))
    exact le_trans habs (le_max_right _ _)
  · have hd := hT t (le_trans (le_max_left T 1) hgt.le)
    rw [Real.dist_eq, sub_zero] at hd
    exact le_trans hd.le (le_max_left _ _)

/-- The graded prime partial sums grow at most like a fixed logarithmic power. -/
theorem exists_primeLogPowSum_bound (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, weightPartialSum (primeLogPowWeight (k + 1)) n
      ≤ K * (Real.log n + 1) ^ (k + 1) := by
  obtain ⟨B, hB0, hB⟩ := exists_gradedMertensError_bound k
  refine ⟨1 / ((k : ℝ) + 1) + |mertensLogPowConstantFull k| + B, by positivity, ?_⟩
  intro n
  rw [weightPartialSum_primeLogPowWeight]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : primeLogPowSum (k + 1) ((0 : ℕ) : ℝ) = 0 := by
      rw [primeLogPowSum]
      simp only [Nat.cast_zero, Nat.floor_zero, Finset.Icc_self, Finset.sum_singleton]
      exact primeLogPowWeight_zero_index _
    rw [h0]
    have : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) + |mertensLogPowConstantFull k| + B := by positivity
    have hpow : (0 : ℝ) ≤ (Real.log ((0 : ℕ) : ℝ) + 1) ^ (k + 1) := by
      simp only [Nat.cast_zero, Real.log_zero, zero_add, one_pow]
      norm_num
    positivity
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hE := (abs_le.mp (hB (n : ℝ) hn1)).2
    rw [gradedMertensError] at hE
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have hpow1 : (1 : ℝ) ≤ (Real.log (n : ℝ) + 1) ^ (k + 1) :=
      one_le_pow₀ (by linarith)
    have hpowle : (Real.log (n : ℝ)) ^ (k + 1) ≤ (Real.log (n : ℝ) + 1) ^ (k + 1) :=
      pow_le_pow_left₀ hlog (by linarith) _
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hdiv : (Real.log (n : ℝ)) ^ (k + 1) / ((k : ℝ) + 1)
        ≤ (Real.log (n : ℝ) + 1) ^ (k + 1) / ((k : ℝ) + 1) := by gcongr
    have hCle : mertensLogPowConstantFull k ≤ |mertensLogPowConstantFull k| := le_abs_self _
    have hexp : (1 / ((k : ℝ) + 1) + |mertensLogPowConstantFull k| + B)
        * (Real.log (n : ℝ) + 1) ^ (k + 1)
        = (Real.log (n : ℝ) + 1) ^ (k + 1) / ((k : ℝ) + 1)
          + (|mertensLogPowConstantFull k| + B) * (Real.log (n : ℝ) + 1) ^ (k + 1) := by
      field_simp
      ring
    rw [hexp]
    have habs0 : (0 : ℝ) ≤ |mertensLogPowConstantFull k| := abs_nonneg _
    nlinarith [hE, hdiv, hCle, hpow1, habs0, hB0]

/-! ## The graded prime log-zeta function -/

theorem summable_primeLogPowWeight_rpow (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun n : ℕ => primeLogPowWeight (k + 1) n * (n : ℝ) ^ (-δ)) := by
  have hmaj : Summable (fun n : ℕ => |Real.log n| ^ (k + 1) * (n : ℝ) ^ (-(1 + δ))) :=
    summable_abs_log_natCast_pow_mul_rpow_neg (k + 1) (1 + δ) (by linarith)
  refine hmaj.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · exact mul_nonneg (primeLogPowWeight_nonneg _ _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · have hlog : 0 ≤ Real.log (n : ℝ) := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · exact Real.log_nonneg (by exact_mod_cast hn)
    have habs : |Real.log (n : ℝ)| = Real.log (n : ℝ) := abs_of_nonneg hlog
    rw [habs]
    by_cases hp : n.Prime
    · rw [primeLogPowWeight, if_pos hp]
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hp.pos
      have hd : (0 : ℝ) < (n : ℝ) ^ δ := Real.rpow_pos_of_pos hn0 δ
      refine le_of_eq ?_
      rw [Real.rpow_neg hn0.le, Real.rpow_neg hn0.le, Real.rpow_add hn0, Real.rpow_one]
      field_simp
    · rw [primeLogPowWeight, if_neg hp, zero_mul]
      exact mul_nonneg (pow_nonneg hlog _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem measurable_weightPartialSum_floor (c : ℕ → ℝ) :
    Measurable fun t : ℝ => weightPartialSum c ⌊t⌋₊ :=
  (measurable_from_top : Measurable fun n : ℕ => weightPartialSum c n).comp Nat.measurable_floor

theorem integrableOn_rpow_mul_gradedFloor (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ => t ^ (-δ - 1)
      * weightPartialSum (primeLogPowWeight (k + 1)) ⌊t⌋₊) (Ioi (1 : ℝ)) := by
  obtain ⟨K, hK0, hK⟩ := exists_primeLogPowSum_bound k
  have hmaj : IntegrableOn (fun t : ℝ => K * (t ^ (-δ - 1) * (Real.log t + 1) ^ (k + 1)))
      (Ioi (1 : ℝ)) := (integrableOn_rpow_mul_logAffine_pow_Ioi_one hδ (k + 1)).const_mul K
  have hne : ∀ t ∈ Ioi (1 : ℝ), t ≠ 0 := by
    intro t ht
    have h1 : (1 : ℝ) < t := ht
    linarith
  refine Integrable.mono' hmaj ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      exact ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (hne t ht)
    · exact (measurable_weightPartialSum_floor _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hpow : (0 : ℝ) < t ^ (-δ - 1) := Real.rpow_pos_of_pos ht0 _
    have hS0 : 0 ≤ weightPartialSum (primeLogPowWeight (k + 1)) ⌊t⌋₊ :=
      Finset.sum_nonneg fun j _ => primeLogPowWeight_nonneg _ _
    have hfloor1 : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr (by linarith)
    have hfloorpos : (0 : ℝ) < ((⌊t⌋₊ : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hfloor1
    have hlogmono : Real.log ((⌊t⌋₊ : ℕ) : ℝ) ≤ Real.log t :=
      Real.log_le_log hfloorpos (Nat.floor_le ht0.le)
    have hlogfloor : 0 ≤ Real.log ((⌊t⌋₊ : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hfloor1)
    have hSle : weightPartialSum (primeLogPowWeight (k + 1)) ⌊t⌋₊
        ≤ K * (Real.log t + 1) ^ (k + 1) := by
      refine (hK ⌊t⌋₊).trans ?_
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith) (by linarith) _) hK0
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hpow.le hS0)]
    calc t ^ (-δ - 1) * weightPartialSum (primeLogPowWeight (k + 1)) ⌊t⌋₊
        ≤ t ^ (-δ - 1) * (K * (Real.log t + 1) ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left hSle hpow.le
      _ = K * (t ^ (-δ - 1) * (Real.log t + 1) ^ (k + 1)) := by ring

/-- The graded prime log-zeta function `∑_p (log p)^{k+1} p^{-1-δ}`. -/
def gradedPrimeLogZeta (k : ℕ) (δ : ℝ) : ℝ :=
  ∑' n : ℕ, primeLogPowWeight (k + 1) n * (n : ℝ) ^ (-δ)

theorem gradedPrimeLogZeta_eq_abel_integral (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    gradedPrimeLogZeta k δ
      = δ * ∫ t in Ioi (1 : ℝ), t ^ (-δ - 1)
          * weightPartialSum (primeLogPowWeight (k + 1)) ⌊t⌋₊ := by
  obtain ⟨K, hK0, hK⟩ := exists_primeLogPowSum_bound k
  exact weightedDirichlet_eq_abel_integral_pow (primeLogPowWeight_zero_index _)
    (primeLogPowWeight_nonneg _) hK0 (k + 1) hK hδ (summable_primeLogPowWeight_rpow k hδ)

/-- The exact Abel decomposition of the graded floor integral. -/
theorem gradedAbelIntegral_eq (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (∫ t in Ioi (1 : ℝ), t ^ (-δ - 1)
        * weightPartialSum (primeLogPowWeight (k + 1)) ⌊t⌋₊)
      = (Nat.factorial (k + 1) : ℝ) / δ ^ (k + 2) / ((k : ℝ) + 1)
        + mertensLogPowConstantFull k / δ
        + ∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) * gradedMertensError k t := by
  have hrpow : IntegrableOn (fun t : ℝ => t ^ (-δ - 1)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have h1 : IntegrableOn (fun t : ℝ => t ^ (-δ - 1) * (Real.log t) ^ (k + 1) / ((k : ℝ) + 1))
      (Ioi (1 : ℝ)) := (integrableOn_rpow_mul_log_pow_Ioi_one hδ (k + 1)).div_const _
  have h2 : IntegrableOn (fun t : ℝ => t ^ (-δ - 1) * mertensLogPowConstantFull k)
      (Ioi (1 : ℝ)) := hrpow.mul_const _
  have h12 : IntegrableOn (fun t : ℝ =>
      t ^ (-δ - 1) * (Real.log t) ^ (k + 1) / ((k : ℝ) + 1)
        + t ^ (-δ - 1) * mertensLogPowConstantFull k) (Ioi (1 : ℝ)) := h1.add h2
  have hS := integrableOn_rpow_mul_gradedFloor k hδ
  have hsplit : ∀ t ∈ Ioi (1 : ℝ),
      t ^ (-δ - 1) * weightPartialSum (primeLogPowWeight (k + 1)) ⌊t⌋₊
        = t ^ (-δ - 1) * (Real.log t) ^ (k + 1) / ((k : ℝ) + 1)
          + t ^ (-δ - 1) * mertensLogPowConstantFull k
          + t ^ (-δ - 1) * gradedMertensError k t := by
    intro t _
    rw [weightPartialSum_primeLogPowWeight, primeLogPowSum_floor_cast, gradedMertensError]
    ring
  have hsub : IntegrableOn (fun t : ℝ =>
      t ^ (-δ - 1) * weightPartialSum (primeLogPowWeight (k + 1)) ⌊t⌋₊
        - (t ^ (-δ - 1) * (Real.log t) ^ (k + 1) / ((k : ℝ) + 1)
          + t ^ (-δ - 1) * mertensLogPowConstantFull k)) (Ioi (1 : ℝ)) := hS.sub h12
  have h3 : IntegrableOn (fun t : ℝ => t ^ (-δ - 1) * gradedMertensError k t)
      (Ioi (1 : ℝ)) := by
    refine hsub.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hsplit t ht]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hsplit,
    MeasureTheory.integral_add h12 h3, MeasureTheory.integral_add h1 h2]
  congr 2
  · rw [MeasureTheory.integral_div, integral_rpow_mul_log_pow_Ioi_one hδ (k + 1)]
  · rw [MeasureTheory.integral_mul_const, integral_Ioi_rpow_of_lt (by linarith) one_pos,
      show (-δ - 1 + 1 : ℝ) = -δ by ring, Real.one_rpow]
    field_simp

theorem abs_gradedErrorIntegral_le (k : ℕ) {δ : ℝ} (hδ : 0 < δ) {B : ℝ}
    (hB : ∀ t : ℝ, 1 ≤ t → |gradedMertensError k t| ≤ B) :
    |∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) * gradedMertensError k t| ≤ B / δ := by
  have hrpow : IntegrableOn (fun t : ℝ => t ^ (-δ - 1)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  have hmaj : IntegrableOn (fun t : ℝ => B * t ^ (-δ - 1)) (Ioi (1 : ℝ)) := hrpow.const_mul B
  have hbound : ∀ᵐ t ∂(volume.restrict (Ioi (1 : ℝ))),
      ‖t ^ (-δ - 1) * gradedMertensError k t‖ ≤ B * t ^ (-δ - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) < t := ht
    have hpow : (0 : ℝ) < t ^ (-δ - 1) := Real.rpow_pos_of_pos (by linarith) _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpow.le]
    calc t ^ (-δ - 1) * |gradedMertensError k t| ≤ t ^ (-δ - 1) * B :=
          mul_le_mul_of_nonneg_left (hB t ht1.le) hpow.le
      _ = B * t ^ (-δ - 1) := by ring
  have h := MeasureTheory.norm_integral_le_of_norm_le hmaj hbound
  rw [Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos,
    show (-δ - 1 + 1 : ℝ) = -δ by ring, Real.one_rpow]
  field_simp

/-- **The graded Abelian pole of the prime log-power zeta function.**
`lim_{δ ↓ 0} δ^{k+1} ∑_p (log p)^{k+1} p^{-1-δ} = k!`. -/
theorem tendsto_gradedPrimeLogZeta (k : ℕ) :
    Tendsto (fun δ : ℝ => δ ^ (k + 1) * gradedPrimeLogZeta k δ)
      (nhdsWithin 0 (Ioi 0)) (nhds (Nat.factorial k : ℝ)) := by
  obtain ⟨B, hB0, hB⟩ := exists_gradedMertensError_bound k
  set A : ℝ := |mertensLogPowConstantFull k| + B with hA
  have hA0 : 0 ≤ A := by positivity
  have hmain : ∀ δ : ℝ, δ ∈ Ioi (0 : ℝ) →
      ‖δ ^ (k + 1) * gradedPrimeLogZeta k δ - (Nat.factorial k : ℝ)‖ ≤ δ ^ (k + 1) * A := by
    intro δ hδmem
    have hδ : (0 : ℝ) < δ := hδmem
    have hδne : δ ≠ 0 := ne_of_gt hδ
    have hfacsplit : (Nat.factorial (k + 1) : ℝ) = ((k : ℝ) + 1) * (Nat.factorial k : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hR := abs_gradedErrorIntegral_le k hδ hB
    have hval : δ ^ (k + 1) * gradedPrimeLogZeta k δ - (Nat.factorial k : ℝ)
        = δ ^ (k + 1) * mertensLogPowConstantFull k
          + δ ^ (k + 2)
            * ∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) * gradedMertensError k t := by
      rw [gradedPrimeLogZeta_eq_abel_integral k hδ, gradedAbelIntegral_eq k hδ, hfacsplit]
      field_simp
      ring
    rw [hval, Real.norm_eq_abs]
    have hstep : |δ ^ (k + 1) * mertensLogPowConstantFull k
          + δ ^ (k + 2) * ∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) * gradedMertensError k t|
        ≤ δ ^ (k + 1) * |mertensLogPowConstantFull k|
          + δ ^ (k + 2) * |∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) * gradedMertensError k t| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ δ ^ (k + 1)),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ δ ^ (k + 2))]
    refine hstep.trans ?_
    have hdpow : δ ^ (k + 2) = δ ^ (k + 1) * δ := by ring
    have hlast : δ ^ (k + 2)
        * |∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) * gradedMertensError k t| ≤ δ ^ (k + 1) * B := by
      rw [hdpow, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc δ * |∫ t in Ioi (1 : ℝ), t ^ (-δ - 1) * gradedMertensError k t|
          ≤ δ * (B / δ) := mul_le_mul_of_nonneg_left hR hδ.le
        _ = B := by field_simp
    rw [hA, mul_add]
    linarith
  have hg : Tendsto (fun δ : ℝ => δ ^ (k + 1) * A) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hcont : Tendsto (fun δ : ℝ => δ ^ (k + 1) * A) (nhds 0) (nhds ((0 : ℝ) ^ (k + 1) * A)) :=
      ((continuous_pow (k + 1)).mul continuous_const).tendsto 0
    rw [zero_pow (by omega), zero_mul] at hcont
    exact hcont.mono_left nhdsWithin_le_nhds
  have hzero : Tendsto (fun δ : ℝ => δ ^ (k + 1) * gradedPrimeLogZeta k δ
      - (Nat.factorial k : ℝ)) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [self_mem_nhdsWithin] with δ hδ using hmain δ hδ
  have := hzero.add_const (Nat.factorial k : ℝ)
  simpa using this

end

end RHTower
