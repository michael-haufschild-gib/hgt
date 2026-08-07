import GaloisForLFunctions.RHTower.PrimeRpowSumAsymptotic
import GaloisForLFunctions.RHTower.EulerHellingerLocalFirstOrder
import GaloisForLFunctions.HTGeometry.RpowPartialSumBound

/-!
# The prime--Wold asymptotic of the reflected sewing cost

For a fixed drift `0 < c < 1/2` the reflected sewing cost has the sharp prime power asymptotic

```text
L_N(c) = N^(2c)/(2c log N) (1 + o(1)).
```

The local cost is `p^(2c-1)` to first order with error `O(p^(α-1))` for `α = max(4c-1) c < 2c`,
whose prime sum is `O(N^α)`, and the leading prime power sum is asymptotic to `N^(2c)/(2c log N)`
by Abel summation against the Chebyshev function.
-/

open Filter Topology Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The half-open prime power sum -/

/-- The prime power sum over `p < N`. -/
def primeRpowSumBelow (a : ℝ) (N : ℕ) : ℝ := ∑ p ∈ Nat.primesBelow N, (p : ℝ) ^ (a - 1)

private theorem primeRpowIndicator_range (a : ℝ) (N : ℕ) :
    primeRpowSumBelow a N
      = ∑ k ∈ Finset.range N, (if k.Prime then ((k : ℕ) : ℝ) ^ (a - 1) else 0) := by
  rw [primeRpowSumBelow, Nat.primesBelow, Finset.sum_filter]

private theorem primeRpowIndicator_Ioc (a : ℝ) (N : ℕ) :
    primeRpowSumIoc a (N : ℝ)
      = ∑ k ∈ Finset.Ioc 2 N, (if k.Prime then ((k : ℕ) : ℝ) ^ (a - 1) else 0) := by
  rw [primeRpowSumIoc, Nat.floor_natCast]

theorem primeRpowSumBelow_eq {a : ℝ} {N : ℕ} (hN : 3 ≤ N) :
    primeRpowSumBelow a N
      = primeRpowSumIoc a (N : ℝ) + (2 : ℝ) ^ (a - 1)
        - (if N.Prime then ((N : ℕ) : ℝ) ^ (a - 1) else 0) := by
  set ind : ℕ → ℝ := fun k => if k.Prime then ((k : ℕ) : ℝ) ^ (a - 1) else 0 with hind
  have hIoc : Finset.Ioc 2 N = Finset.Ico 3 (N + 1) := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have hsplitIoc : ∑ k ∈ Finset.Ioc 2 N, ind k = (∑ k ∈ Finset.Ico 3 N, ind k) + ind N := by
    rw [hIoc, Finset.sum_Ico_succ_top (by omega : 3 ≤ N)]
  have hsplitRange : ∑ k ∈ Finset.range N, ind k
      = (∑ k ∈ Finset.range 3, ind k) + ∑ k ∈ Finset.Ico 3 N, ind k := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.sum_Ico_consecutive ind (by omega : 0 ≤ 3) (by omega : 3 ≤ N)]
  have hthree : ∑ k ∈ Finset.range 3, ind k = (2 : ℝ) ^ (a - 1) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hind]
    norm_num [Nat.not_prime_zero, Nat.not_prime_one, Nat.prime_two]
  rw [primeRpowIndicator_range, primeRpowIndicator_Ioc, hsplitRange, hthree, hsplitIoc]
  ring

/-! ## The asymptotic of the half-open prime power sum -/

private theorem tendsto_log_div_natRpow {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ) ^ β) atTop (nhds 0) :=
  ((isLittleO_log_rpow_atTop hβ).tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop

theorem tendsto_primeRpowSumBelow {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Tendsto (fun N : ℕ => primeRpowSumBelow a N * (a * Real.log N) / (N : ℝ) ^ a) atTop
      (nhds 1) := by
  have hIoc : Tendsto
      (fun N : ℕ => primeRpowSumIoc a (N : ℝ) * (a * Real.log N) / (N : ℝ) ^ a) atTop (nhds 1) :=
    (tendsto_primeRpowSumIoc ha0 ha1).comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto
      (fun N : ℕ => (2 : ℝ) ^ (a - 1) * (a * Real.log N) / (N : ℝ) ^ a) atTop (nhds 0) := by
    have h := (tendsto_log_div_natRpow ha0).const_mul ((2 : ℝ) ^ (a - 1) * a)
    rw [mul_zero] at h
    refine h.congr fun N => ?_
    ring
  have htop : Tendsto
      (fun N : ℕ => (if N.Prime then ((N : ℕ) : ℝ) ^ (a - 1) else 0) * (a * Real.log N)
        / (N : ℝ) ^ a) atTop (nhds 0) := by
    have hmaj : Tendsto (fun N : ℕ => a * Real.log (N : ℝ) / (N : ℝ)) atTop (nhds 0) := by
      have h := (tendsto_log_div_natRpow (β := 1) (by norm_num)).const_mul a
      rw [mul_zero] at h
      refine h.congr fun N => ?_
      rw [Real.rpow_one]
      ring
    refine squeeze_zero' ?_ ?_ hmaj
    · filter_upwards [eventually_ge_atTop 2] with N hN
      have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
      have hXpos : (0 : ℝ) < (N : ℝ) ^ a := Real.rpow_pos_of_pos (by linarith) a
      have hnum : (0 : ℝ) ≤ (if N.Prime then ((N : ℕ) : ℝ) ^ (a - 1) else 0) := by
        split_ifs
        · exact Real.rpow_nonneg (by linarith) _
        · exact le_rfl
      positivity
    · filter_upwards [eventually_ge_atTop 2] with N hN
      have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
      have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
      have hXpos : (0 : ℝ) < (N : ℝ) ^ a := Real.rpow_pos_of_pos hN0 a
      have hsub : ((N : ℕ) : ℝ) ^ (a - 1) = (N : ℝ) ^ a / (N : ℝ) := by
        rw [Real.rpow_sub hN0, Real.rpow_one]
      have hle : (if N.Prime then ((N : ℕ) : ℝ) ^ (a - 1) else 0) ≤ (N : ℝ) ^ a / (N : ℝ) := by
        split_ifs
        · rw [hsub]
        · positivity
      have hstep : (if N.Prime then ((N : ℕ) : ℝ) ^ (a - 1) else 0) * (a * Real.log (N : ℝ))
          / (N : ℝ) ^ a ≤ (N : ℝ) ^ a / (N : ℝ) * (a * Real.log (N : ℝ)) / (N : ℝ) ^ a := by
        have := mul_le_mul_of_nonneg_right hle (by positivity : (0:ℝ) ≤ a * Real.log (N : ℝ))
        exact div_le_div_of_nonneg_right this hXpos.le
      have hval : (N : ℝ) ^ a / (N : ℝ) * (a * Real.log (N : ℝ)) / (N : ℝ) ^ a
          = a * Real.log (N : ℝ) / (N : ℝ) := by
        field_simp
      rw [hval] at hstep
      exact hstep
  have hcomb := (hIoc.add hconst).sub htop
  rw [add_zero, sub_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with N hN
  rw [primeRpowSumBelow_eq hN]
  ring

/-! ## The prime sum of the first-order error -/

theorem sum_primesBelow_rpow_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (N : ℕ) :
    ∑ p ∈ Nat.primesBelow N, (p : ℝ) ^ (α - 1) ≤ (N : ℝ) ^ α / α := by
  classical
  have hinj : ∀ x ∈ Nat.primesBelow N, ∀ y ∈ Nat.primesBelow N, x - 1 = y - 1 → x = y := by
    intro x hx y hy hxy
    have hx2 := (Nat.prime_of_mem_primesBelow hx).two_le
    have hy2 := (Nat.prime_of_mem_primesBelow hy).two_le
    omega
  have hmap : ∑ n ∈ (Nat.primesBelow N).image (fun p : ℕ => p - 1), ((n : ℝ) + 1) ^ (α - 1)
      = ∑ p ∈ Nat.primesBelow N, (((p - 1 : ℕ) : ℝ) + 1) ^ (α - 1) := Finset.sum_image hinj
  have hshift : ∑ p ∈ Nat.primesBelow N, (((p - 1 : ℕ) : ℝ) + 1) ^ (α - 1)
      = ∑ p ∈ Nat.primesBelow N, (p : ℝ) ^ (α - 1) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp2 := (Nat.prime_of_mem_primesBelow hp).two_le
    have hcast : ((p - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by
      have h1 : (1 : ℕ) ≤ p := by omega
      rw [Nat.cast_sub h1]
      push_cast
      ring
    rw [hcast]
  have hsub : (Nat.primesBelow N).image (fun p : ℕ => p - 1) ⊆ Finset.range N := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨p, hp, rfl⟩ := hn
    have hpN := (Nat.mem_primesBelow.mp hp).1
    rw [Finset.mem_range]
    omega
  have hle : ∑ n ∈ (Nat.primesBelow N).image (fun p : ℕ => p - 1), ((n : ℝ) + 1) ^ (α - 1)
      ≤ ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (α - 1) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => ?_
    positivity
  rw [← hshift, ← hmap]
  exact le_trans hle (HTGeometry.sum_rpow_sub_one_le hα0 hα1 N)

/-! ## The prime--Wold asymptotic -/

theorem abs_logReflectedSewing_sub_primeRpowSum_le {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2)
    (N : ℕ) :
    |logReflectedSewingBelow c N - primeRpowSumBelow (2 * c) N| ≤
      sewingFirstOrderConst c * ((N : ℝ) ^ sewingErrorExponent c / sewingErrorExponent c) := by
  have habs : |c| < 1 / 2 := by
    rw [abs_of_pos hc0]
    exact hc
  have hK := sewingFirstOrderConst_nonneg hc
  have hα0 := sewingErrorExponent_pos hc0
  have hα1 := sewingErrorExponent_lt_one hc0 hc
  rw [logReflectedSewingBelow_eq_sum_localSewingLog habs N, primeRpowSumBelow,
    ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ p ∈ Nat.primesBelow N,
      |localSewingLog p c - (p : ℝ) ^ (2 * c - 1)| ≤
        sewingFirstOrderConst c * (p : ℝ) ^ (sewingErrorExponent c - 1) := fun p hp =>
    abs_localSewingLog_sub_rpow_le (Nat.prime_of_mem_primesBelow hp) hc0 hc
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_primesBelow_rpow_le hα0 hα1 N) hK

/-- **The prime--Wold asymptotic.**  The reflected sewing cost satisfies
`L_N(c) = N^(2c)/(2c log N)(1 + o(1))`. -/
theorem tendsto_logReflectedSewing_mul_log_div_rpow {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2) :
    Tendsto (fun N : ℕ =>
        logReflectedSewingBelow c N * (2 * c * Real.log N) / (N : ℝ) ^ (2 * c)) atTop
      (nhds 1) := by
  have hα0 := sewingErrorExponent_pos hc0
  have hα1 := sewingErrorExponent_lt_one hc0 hc
  have hαlt := sewingErrorExponent_lt hc0 hc
  have hK := sewingFirstOrderConst_nonneg hc
  have hmain : Tendsto
      (fun N : ℕ => primeRpowSumBelow (2 * c) N * (2 * c * Real.log N) / (N : ℝ) ^ (2 * c)) atTop
      (nhds 1) := tendsto_primeRpowSumBelow (by linarith) (by linarith)
  have herr : Tendsto
      (fun N : ℕ => (logReflectedSewingBelow c N - primeRpowSumBelow (2 * c) N) *
        (2 * c * Real.log N) / (N : ℝ) ^ (2 * c)) atTop (nhds 0) := by
    have hmaj : Tendsto (fun N : ℕ =>
        sewingFirstOrderConst c / sewingErrorExponent c * (2 * c) *
          (Real.log (N : ℝ) / (N : ℝ) ^ (2 * c - sewingErrorExponent c))) atTop (nhds 0) := by
      have h := (tendsto_log_div_natRpow (β := 2 * c - sewingErrorExponent c)
        (by linarith)).const_mul (sewingFirstOrderConst c / sewingErrorExponent c * (2 * c))
      rwa [mul_zero] at h
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
    have hXpos : (0 : ℝ) < (N : ℝ) ^ (2 * c) := Real.rpow_pos_of_pos hN0 _
    have hbound := abs_logReflectedSewing_sub_primeRpowSum_le hc0 hc N
    have hstep : |logReflectedSewingBelow c N - primeRpowSumBelow (2 * c) N| *
        (2 * c * Real.log (N : ℝ)) / (N : ℝ) ^ (2 * c) ≤
        sewingFirstOrderConst c * ((N : ℝ) ^ sewingErrorExponent c / sewingErrorExponent c) *
          (2 * c * Real.log (N : ℝ)) / (N : ℝ) ^ (2 * c) := by
      have := mul_le_mul_of_nonneg_right hbound
        (by positivity : (0 : ℝ) ≤ 2 * c * Real.log (N : ℝ))
      exact div_le_div_of_nonneg_right this hXpos.le
    have hsplit : (N : ℝ) ^ (2 * c) = (N : ℝ) ^ (2 * c - sewingErrorExponent c) *
        (N : ℝ) ^ sewingErrorExponent c := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring
    have hEpos : (0 : ℝ) < (N : ℝ) ^ sewingErrorExponent c := Real.rpow_pos_of_pos hN0 _
    have hDpos : (0 : ℝ) < (N : ℝ) ^ (2 * c - sewingErrorExponent c) :=
      Real.rpow_pos_of_pos hN0 _
    have hval : sewingFirstOrderConst c * ((N : ℝ) ^ sewingErrorExponent c / sewingErrorExponent c) *
        (2 * c * Real.log (N : ℝ)) / (N : ℝ) ^ (2 * c)
        = sewingFirstOrderConst c / sewingErrorExponent c * (2 * c) *
          (Real.log (N : ℝ) / (N : ℝ) ^ (2 * c - sewingErrorExponent c)) := by
      rw [hsplit]
      field_simp
    rw [hval] at hstep
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hXpos,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * c * Real.log (N : ℝ))]
    exact hstep
  have hcomb := hmain.add herr
  rw [add_zero] at hcomb
  refine hcomb.congr fun N => ?_
  ring

end

end RHTower
