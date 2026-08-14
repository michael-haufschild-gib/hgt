import GaloisForLFunctions.RHTower.RouteEGibbsWideBatch
import GaloisForLFunctions.RHTower.RouteESaddlePntTransport
import GaloisForLFunctions.RHTower.Sieve.MertensThird
import GaloisForLFunctions.HTGeometry.ArctanSinTaylor

/-!
# The prefix phase weight

The initial prime prefix carries the weighted sum

```text
∑_{p ≤ Y} √p log p/(p-1) = 2√Y (1 + o(1)),
```

which is the prime power–logarithm sum at exponent `1/2` corrected by the convergent factor
`p/(p-1)`: the correction is bounded by `4 ∑_{p ≤ Y} 1/p`, hence `O(log log Y)`, because
`log p ≤ 2√p`.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- The prefix phase weight `∑_{p ≤ Y} √p log p /(p-1)`. -/
def prefixPhaseWeight (Y : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊Y⌋₊, Real.sqrt p * Real.log p / ((p : ℝ) - 1)

theorem prefixPhaseWeight_eq_add {Y : ℝ} (hY : 2 ≤ Y) :
    prefixPhaseWeight Y
      = primeRpowLogSumLE (1 / 2) Y
        + ∑ p ∈ Nat.primesLE ⌊Y⌋₊, (p : ℝ) ^ (-(1 : ℝ) / 2) * Real.log p / ((p : ℝ) - 1) := by
  rw [prefixPhaseWeight, primeRpowLogSumLE, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hprime := Nat.prime_of_mem_primesLE hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hp1 : ((p : ℝ) - 1) ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    linarith [h]
  have hsqrt : Real.sqrt p = (p : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  have hexp : (p : ℝ) ^ ((1 : ℝ) / 2 - 1) = (p : ℝ) ^ (-(1 : ℝ) / 2) := by
    congr 1
    ring
  have hsplit : (p : ℝ) ^ (-(1 : ℝ) / 2) * (p : ℝ) = (p : ℝ) ^ ((1 : ℝ) / 2) := by
    nth_rewrite 2 [← Real.rpow_one (p : ℝ)]
    rw [← Real.rpow_add hp0]
    norm_num
  rw [hsqrt, hexp, ← hsplit]
  field_simp
  ring

/-- The convergent correction of the prefix weight is `O(log log Y)`. -/
theorem prefixPhaseCorrection_le {Y : ℝ} (hY : 2 ≤ Y) :
    ∑ p ∈ Nat.primesLE ⌊Y⌋₊, (p : ℝ) ^ (-(1 : ℝ) / 2) * Real.log p / ((p : ℝ) - 1)
      ≤ 4 * Sieve.mertensS ⌊Y⌋₊ := by
  rw [Sieve.mertensS, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hprime := Nat.prime_of_mem_primesLE hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hhalf : (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by linarith
  have hlog : Real.log p ≤ 2 * Real.sqrt p := Sieve.log_le_two_mul_sqrt hp0
  have hsqrt : Real.sqrt p = (p : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
  have hrp : (p : ℝ) ^ (-(1 : ℝ) / 2) * (p : ℝ) ^ ((1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hp0]
    norm_num
  have hrppos : (0 : ℝ) < (p : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hp0 _
  have hnum : (p : ℝ) ^ (-(1 : ℝ) / 2) * Real.log p ≤ 2 := by
    calc (p : ℝ) ^ (-(1 : ℝ) / 2) * Real.log p
        ≤ (p : ℝ) ^ (-(1 : ℝ) / 2) * (2 * Real.sqrt p) :=
          mul_le_mul_of_nonneg_left hlog hrppos.le
      _ = 2 * ((p : ℝ) ^ (-(1 : ℝ) / 2) * (p : ℝ) ^ ((1 : ℝ) / 2)) := by
          rw [hsqrt]
          ring
      _ = 2 := by rw [hrp]; ring
  have hnum0 : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 : ℝ) / 2) * Real.log p := by
    have hlog0 : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
    positivity
  calc (p : ℝ) ^ (-(1 : ℝ) / 2) * Real.log p / ((p : ℝ) - 1)
      ≤ 2 / ((p : ℝ) - 1) := by
        apply div_le_div_of_nonneg_right hnum hp1.le
    _ ≤ 2 / ((p : ℝ) / 2) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by linarith) hhalf
    _ = 4 * (1 / (p : ℝ)) := by
        field_simp
        ring

/-- **The prefix phase weight.**  `∑_{p ≤ Y} √p log p/(p-1) = 2√Y(1 + o(1))`. -/
theorem tendsto_prefixPhaseWeight :
    Tendsto (fun Y : ℝ => prefixPhaseWeight Y / Y ^ ((1 : ℝ) / 2)) atTop (nhds 2) := by
  have ha0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hmain := tendsto_primeRpowLogSumLE ha0
  have hval : (1 : ℝ) / (1 / 2) = 2 := by norm_num
  rw [hval] at hmain
  have hcorr : Tendsto (fun Y : ℝ =>
      (∑ p ∈ Nat.primesLE ⌊Y⌋₊, (p : ℝ) ^ (-(1 : ℝ) / 2) * Real.log p / ((p : ℝ) - 1)) /
        Y ^ ((1 : ℝ) / 2)) atTop (nhds 0) := by
    have hmaj : Tendsto (fun Y : ℝ =>
        4 * (Real.log Y + Sieve.mertensUpperConst) / Y ^ ((1 : ℝ) / 2)) atTop (nhds 0) := by
      have hlog : Tendsto (fun Y : ℝ => Real.log Y / Y ^ ((1 : ℝ) / 2)) atTop (nhds 0) :=
        (isLittleO_log_rpow_atTop ha0).tendsto_div_nhds_zero
      have hconst : Tendsto (fun Y : ℝ => Sieve.mertensUpperConst / Y ^ ((1 : ℝ) / 2)) atTop
          (nhds 0) := tendsto_const_nhds.div_atTop (tendsto_rpow_atTop ha0)
      have h := (hlog.add hconst).const_mul (4 : ℝ)
      rw [add_zero, mul_zero] at h
      refine h.congr fun Y => ?_
      ring
    refine squeeze_zero' ?_ ?_ hmaj
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with Y hY
      have hYa : (0 : ℝ) < Y ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _
      refine div_nonneg (Finset.sum_nonneg fun p hp => ?_) hYa.le
      have hprime := Nat.prime_of_mem_primesLE hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      have hlog0 : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
      have hrppos : (0 : ℝ) < (p : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hp0 _
      have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      positivity
    · filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
      have hY0 : (0 : ℝ) < Y := by linarith
      have hYa : (0 : ℝ) < Y ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hY0 _
      have hfloor : 2 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
      have hfloorle : ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Y := Nat.floor_le hY0.le
      have hfloorpos : (0 : ℝ) < ((⌊Y⌋₊ : ℕ) : ℝ) := by
        have : (0 : ℕ) < ⌊Y⌋₊ := by omega
        exact_mod_cast this
      have hlogfloor : Real.log ⌊Y⌋₊ ≤ Real.log Y := Real.log_le_log hfloorpos hfloorle
      have hmert := Sieve.mertensS_le_logLog_add hfloor
      have hloglog : Sieve.logLog ⌊Y⌋₊ ≤ Real.log Y := by
        rw [Sieve.logLog]
        have hlogfloorpos : (0 : ℝ) < Real.log ⌊Y⌋₊ := by
          have h2 : (2 : ℝ) ≤ ((⌊Y⌋₊ : ℕ) : ℝ) := by exact_mod_cast hfloor
          have := Real.log_le_log (by norm_num : (0:ℝ) < 2) h2
          have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
          linarith
        have hlogY : (0 : ℝ) < Real.log Y := by
          have := Real.log_pos (by linarith : (1:ℝ) < Y)
          linarith
        calc Real.log (Real.log ⌊Y⌋₊) ≤ Real.log (Real.log Y) :=
              Real.log_le_log hlogfloorpos hlogfloor
          _ ≤ Real.log Y := by
              have := Real.log_le_sub_one_of_pos hlogY
              linarith
      have hnum := prefixPhaseCorrection_le hY
      have hle : ∑ p ∈ Nat.primesLE ⌊Y⌋₊,
          (p : ℝ) ^ (-(1 : ℝ) / 2) * Real.log p / ((p : ℝ) - 1)
          ≤ 4 * (Real.log Y + Sieve.mertensUpperConst) := by linarith
      exact div_le_div_of_nonneg_right hle hYa.le
  have hsum := hmain.add hcorr
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
  rw [prefixPhaseWeight_eq_add hY, add_div]

/-! ## The prefix phase -/

/-- The prefix phase: the sum of the local Euler arguments of the signed/unsigned pair. -/
def prefixPhase (Y t : ℝ) : ℝ :=
  -∑ p ∈ Nat.primesLE ⌊Y⌋₊,
    Real.arctan (2 * Real.sqrt p * Real.sin (t * Real.log p) / ((p : ℝ) - 1))

/-- **The linear phase law.**  The prefix phase is linear in the frequency up to a cubic error. -/
theorem abs_prefixPhase_add_le {Y t : ℝ} (hY : 2 ≤ Y) (ht : 0 ≤ t) :
    |prefixPhase Y t + 2 * t * prefixPhaseWeight Y|
      ≤ 68 * t ^ 3 * Real.log Y ^ 2 * primeRpowLogSumLE (1 / 2) Y := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : (0 : ℝ) ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hsum : prefixPhase Y t + 2 * t * prefixPhaseWeight Y
      = ∑ p ∈ Nat.primesLE ⌊Y⌋₊,
        (2 * t * (Real.sqrt p * Real.log p / ((p : ℝ) - 1))
          - Real.arctan (2 * Real.sqrt p * Real.sin (t * Real.log p) / ((p : ℝ) - 1))) := by
    rw [prefixPhase, prefixPhaseWeight, Finset.mul_sum, Finset.sum_sub_distrib]
    ring
  rw [hsum]
  have hbound : ∀ p ∈ Nat.primesLE ⌊Y⌋₊,
      |2 * t * (Real.sqrt p * Real.log p / ((p : ℝ) - 1))
        - Real.arctan (2 * Real.sqrt p * Real.sin (t * Real.log p) / ((p : ℝ) - 1))|
        ≤ 68 * t ^ 3 * Real.log Y ^ 2 * ((p : ℝ) ^ (-(1 : ℝ) / 2) * Real.log p) := by
    intro p hp
    have hprime := Nat.prime_of_mem_primesLE hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hple : (p : ℝ) ≤ Y := by
      have hmem : p ≤ ⌊Y⌋₊ := (Nat.mem_primesLE.mp hp).1
      have h : (p : ℝ) ≤ ((⌊Y⌋₊ : ℕ) : ℝ) := by exact_mod_cast hmem
      exact le_trans h (Nat.floor_le hY0.le)
    have hlogp0 : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
    have hlogple : Real.log p ≤ Real.log Y := Real.log_le_log hp0 hple
    have hsqrt : Real.sqrt p = (p : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
    have hsqrtpos : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr hp0
    have hsqrtsq : Real.sqrt p * Real.sqrt p = (p : ℝ) := Real.mul_self_sqrt hp0.le
    -- the local amplitude
    set r : ℝ := 2 * Real.sqrt p / ((p : ℝ) - 1) with hr
    have hrpos : 0 < r := by
      rw [hr]
      positivity
    have hrle : r ≤ 4 / Real.sqrt p := by
      rw [hr, div_le_div_iff₀ hp1 hsqrtpos]
      nlinarith [hsqrtsq, hsqrtpos, hp2]
    have hval : 2 * t * (Real.sqrt p * Real.log p / ((p : ℝ) - 1)) = r * (t * Real.log p) := by
      rw [hr]
      field_simp
    have hval2 : 2 * Real.sqrt p * Real.sin (t * Real.log p) / ((p : ℝ) - 1)
        = r * Real.sin (t * Real.log p) := by
      rw [hr]
      field_simp
    rw [hval, hval2]
    -- split the two Taylor errors
    have hstep1 : |r * (t * Real.log p) - Real.arctan (r * Real.sin (t * Real.log p))|
        ≤ |r * (t * Real.log p) - r * Real.sin (t * Real.log p)|
          + |r * Real.sin (t * Real.log p) - Real.arctan (r * Real.sin (t * Real.log p))| := by
      have h := abs_add_le (r * (t * Real.log p) - r * Real.sin (t * Real.log p))
        (r * Real.sin (t * Real.log p) - Real.arctan (r * Real.sin (t * Real.log p)))
      have heq : (r * (t * Real.log p) - r * Real.sin (t * Real.log p))
          + (r * Real.sin (t * Real.log p) - Real.arctan (r * Real.sin (t * Real.log p)))
          = r * (t * Real.log p) - Real.arctan (r * Real.sin (t * Real.log p)) := by ring
      rw [heq] at h
      exact h
    have hsin := HTGeometry.abs_sin_sub_self_le (t * Real.log p)
    have harctan := HTGeometry.abs_arctan_sub_self_le (r * Real.sin (t * Real.log p))
    have hsinabs : |Real.sin (t * Real.log p)| ≤ |t * Real.log p| := Real.abs_sin_le_abs
    -- bound the two errors by `t³ (log p)³ / √p`
    have htl0 : (0 : ℝ) ≤ t * Real.log p := by positivity
    have habs1 : |r * (t * Real.log p) - r * Real.sin (t * Real.log p)|
        ≤ r * |t * Real.log p| ^ 3 := by
      have : r * (t * Real.log p) - r * Real.sin (t * Real.log p)
          = r * ((t * Real.log p) - Real.sin (t * Real.log p)) := by ring
      rw [this, abs_mul, abs_of_pos hrpos]
      refine mul_le_mul_of_nonneg_left ?_ hrpos.le
      rw [abs_sub_comm]
      exact hsin
    have habs2 : |r * Real.sin (t * Real.log p)
        - Real.arctan (r * Real.sin (t * Real.log p))|
        ≤ |r * Real.sin (t * Real.log p)| ^ 3 := by
      rw [abs_sub_comm]
      exact harctan
    have hramp : |r * Real.sin (t * Real.log p)| ≤ r * |t * Real.log p| := by
      rw [abs_mul, abs_of_pos hrpos]
      exact mul_le_mul_of_nonneg_left hsinabs hrpos.le
    have hcube : |r * Real.sin (t * Real.log p)| ^ 3 ≤ (r * |t * Real.log p|) ^ 3 :=
      pow_le_pow_left₀ (abs_nonneg _) hramp 3
    have hsqrtinv : (0 : ℝ) < Real.sqrt p := hsqrtpos
    have hr4 : r ≤ 4 / Real.sqrt p := hrle
    have hone : (1 : ℝ) ≤ Real.sqrt p := by
      have h2 : Real.sqrt 1 ≤ Real.sqrt p := Real.sqrt_le_sqrt (by linarith)
      rwa [Real.sqrt_one] at h2
    have htlabs : |t * Real.log p| = t * Real.log p := abs_of_nonneg htl0
    have hkey : r * |t * Real.log p| ^ 3 + (r * |t * Real.log p|) ^ 3
        ≤ 68 * t ^ 3 * Real.log Y ^ 2 * ((p : ℝ) ^ (-(1 : ℝ) / 2) * Real.log p) := by
      have hinv : (p : ℝ) ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt p := by
        rw [hsqrt, one_div, ← Real.rpow_neg hp0.le]
        congr 1
        ring
      rw [hinv, htlabs]
      have hrb : r ≤ 4 / Real.sqrt p := hr4
      have hsq : (t * Real.log p) ^ 3 ≤ t ^ 3 * Real.log Y ^ 2 * Real.log p := by
        have h1 : Real.log p ^ 3 ≤ Real.log Y ^ 2 * Real.log p := by
          have hsq2 : Real.log p ^ 2 ≤ Real.log Y ^ 2 := pow_le_pow_left₀ hlogp0 hlogple 2
          calc Real.log p ^ 3 = Real.log p ^ 2 * Real.log p := by ring
            _ ≤ Real.log Y ^ 2 * Real.log p := mul_le_mul_of_nonneg_right hsq2 hlogp0
        have ht3 : (0 : ℝ) ≤ t ^ 3 := pow_nonneg ht 3
        calc (t * Real.log p) ^ 3 = t ^ 3 * Real.log p ^ 3 := by ring
          _ ≤ t ^ 3 * (Real.log Y ^ 2 * Real.log p) := mul_le_mul_of_nonneg_left h1 ht3
          _ = t ^ 3 * Real.log Y ^ 2 * Real.log p := by ring
      have hcube2 : (r * (t * Real.log p)) ^ 3 ≤ (4 / Real.sqrt p) ^ 3 * (t * Real.log p) ^ 3 := by
        have h1 : r ^ 3 ≤ (4 / Real.sqrt p) ^ 3 := pow_le_pow_left₀ hrpos.le hrb 3
        have hx3 : (0 : ℝ) ≤ (t * Real.log p) ^ 3 := pow_nonneg htl0 3
        calc (r * (t * Real.log p)) ^ 3 = r ^ 3 * (t * Real.log p) ^ 3 := by ring
          _ ≤ (4 / Real.sqrt p) ^ 3 * (t * Real.log p) ^ 3 :=
              mul_le_mul_of_nonneg_right h1 hx3
      have hcube3 : (4 / Real.sqrt p) ^ 3 ≤ 64 / Real.sqrt p := by
        rw [div_pow, div_le_div_iff₀ (by positivity) hsqrtpos]
        nlinarith [hone, hsqrtpos, hsqrtsq, hp2]
      have hstep : r * (t * Real.log p) ^ 3 ≤ (4 / Real.sqrt p) * (t * Real.log p) ^ 3 :=
        mul_le_mul_of_nonneg_right hrb (pow_nonneg htl0 3)
      have hpos : (0 : ℝ) < 1 / Real.sqrt p := by positivity
      have hfinal : (4 / Real.sqrt p) * (t * Real.log p) ^ 3
          + (64 / Real.sqrt p) * (t * Real.log p) ^ 3
          ≤ 68 * t ^ 3 * Real.log Y ^ 2 * (1 / Real.sqrt p * Real.log p) := by
        have hsum : (4 / Real.sqrt p) * (t * Real.log p) ^ 3
            + (64 / Real.sqrt p) * (t * Real.log p) ^ 3
            = (68 / Real.sqrt p) * (t * Real.log p) ^ 3 := by ring
        rw [hsum]
        have hmul : (t * Real.log p) ^ 3 ≤ t ^ 3 * Real.log Y ^ 2 * Real.log p := hsq
        have hcoef : (0 : ℝ) < 68 / Real.sqrt p := by positivity
        calc (68 / Real.sqrt p) * (t * Real.log p) ^ 3
            ≤ (68 / Real.sqrt p) * (t ^ 3 * Real.log Y ^ 2 * Real.log p) :=
              mul_le_mul_of_nonneg_left hmul hcoef.le
          _ = 68 * t ^ 3 * Real.log Y ^ 2 * (1 / Real.sqrt p * Real.log p) := by
              field_simp
      have hcube4 : (r * (t * Real.log p)) ^ 3 ≤ (64 / Real.sqrt p) * (t * Real.log p) ^ 3 := by
        calc (r * (t * Real.log p)) ^ 3 ≤ (4 / Real.sqrt p) ^ 3 * (t * Real.log p) ^ 3 := hcube2
          _ ≤ (64 / Real.sqrt p) * (t * Real.log p) ^ 3 :=
              mul_le_mul_of_nonneg_right hcube3 (pow_nonneg htl0 3)
      linarith [hstep, hcube4, hfinal]
    calc |r * (t * Real.log p) - Real.arctan (r * Real.sin (t * Real.log p))|
        ≤ |r * (t * Real.log p) - r * Real.sin (t * Real.log p)|
          + |r * Real.sin (t * Real.log p)
            - Real.arctan (r * Real.sin (t * Real.log p))| := hstep1
      _ ≤ r * |t * Real.log p| ^ 3 + (r * |t * Real.log p|) ^ 3 := by
          linarith [habs1, habs2, hcube]
      _ ≤ 68 * t ^ 3 * Real.log Y ^ 2 * ((p : ℝ) ^ (-(1 : ℝ) / 2) * Real.log p) := hkey
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hbound) ?_
  rw [primeRpowLogSumLE, Finset.mul_sum]
  refine le_of_eq (Finset.sum_congr rfl fun p _ => ?_)
  have hexp : ((1 : ℝ) / 2 - 1) = -(1 : ℝ) / 2 := by norm_num
  rw [hexp]

/-! ## The sharp prefix-phase threshold -/

/-- **The prefix-phase threshold law.**  With prefix `Y = (log X)^A` and terminal frequency
`t_X = π/log X`, the prefix phase is `-4π (log X)^{A/2 - 1}(1 + o(1))`, so `A = 2` is the exact
prefix-phase threshold. -/
theorem tendsto_prefixPhase_threshold {A : ℝ} (hA : 0 < A) :
    Tendsto (fun X : ℝ =>
      prefixPhase (Real.log X ^ A) (terminalFrequency X) * Real.log X ^ (1 - A / 2)) atTop
      (nhds (-(4 * Real.pi))) := by
  have ha0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hYtop : Tendsto (fun X : ℝ => Real.log X ^ A) atTop atTop :=
    (tendsto_rpow_atTop hA).comp Real.tendsto_log_atTop
  have hW := tendsto_prefixPhaseWeight.comp hYtop
  have hS := (tendsto_primeRpowLogSumLE ha0).comp hYtop
  have hSval : (1 : ℝ) / (1 / 2) = 2 := by norm_num
  rw [hSval] at hS
  -- the main linear term
  have hmain : Tendsto (fun X : ℝ =>
      -(2 * terminalFrequency X * prefixPhaseWeight (Real.log X ^ A)) *
        Real.log X ^ (1 - A / 2)) atTop (nhds (-(4 * Real.pi))) := by
    have h := hW.const_mul (-(2 * Real.pi))
    have hval : -(2 * Real.pi) * 2 = -(4 * Real.pi) := by ring
    rw [hval] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hlogX : (0 : ℝ) < Real.log X := Real.log_pos hX
    have hhalfpos : (0 : ℝ) < Real.log X ^ (A / 2) := Real.rpow_pos_of_pos hlogX _
    have hhalf : (Real.log X ^ A) ^ ((1 : ℝ) / 2) = Real.log X ^ (A / 2) := by
      rw [← Real.rpow_mul hlogX.le]
      congr 1
      ring
    have hdiv : Real.log X ^ (1 - A / 2) = Real.log X / Real.log X ^ (A / 2) := by
      rw [eq_div_iff (ne_of_gt hhalfpos), ← Real.rpow_add hlogX]
      norm_num
    simp only [Function.comp_apply, terminalFrequency]
    rw [hhalf, hdiv]
    field_simp
  -- the cubic remainder
  have herr : Tendsto (fun X : ℝ =>
      (prefixPhase (Real.log X ^ A) (terminalFrequency X)
        + 2 * terminalFrequency X * prefixPhaseWeight (Real.log X ^ A)) *
          Real.log X ^ (1 - A / 2)) atTop (nhds 0) := by
    have hloglog : Tendsto (fun X : ℝ => Real.log (Real.log X) ^ 2 / Real.log X ^ (2 : ℝ)) atTop
        (nhds 0) :=
      (HTGeometry.tendsto_logPow_div_rpow (by norm_num : (0:ℝ) < 2) 2).comp Real.tendsto_log_atTop
    have hmaj : Tendsto (fun X : ℝ =>
        68 * Real.pi ^ 3 * A ^ 2 * (Real.log (Real.log X) ^ 2 / Real.log X ^ (2 : ℝ)) *
          (primeRpowLogSumLE (1 / 2) (Real.log X ^ A) /
            (Real.log X ^ A) ^ ((1 : ℝ) / 2))) atTop (nhds 0) := by
      have h := (hloglog.const_mul (68 * Real.pi ^ 3 * A ^ 2)).mul hS
      rw [mul_zero, zero_mul] at h
      exact h
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [eventually_gt_atTop (Real.exp (Real.exp (2 / A)))] with X hX
    have hexppos : (0 : ℝ) < Real.exp (Real.exp (2 / A)) := Real.exp_pos _
    have hX1 : (1 : ℝ) < X := by
      have h1 : (1 : ℝ) < Real.exp (Real.exp (2 / A)) := by
        have h := Real.add_one_le_exp (Real.exp (2 / A))
        have := Real.exp_pos (2 / A)
        linarith
      linarith
    have hlogX : (0 : ℝ) < Real.log X := Real.log_pos hX1
    have hlogXge : Real.exp (2 / A) ≤ Real.log X := by
      have h := Real.log_le_log hexppos hX.le
      rwa [Real.log_exp] at h
    have hYpos : (0 : ℝ) < Real.log X ^ A := Real.rpow_pos_of_pos hlogX A
    have hYtwo : (2 : ℝ) ≤ Real.log X ^ A := by
      have hmono : Real.exp (2 / A) ^ A ≤ Real.log X ^ A :=
        Real.rpow_le_rpow (Real.exp_pos _).le hlogXge hA.le
      have hval : Real.exp (2 / A) ^ A = Real.exp 2 := by
        rw [← Real.exp_mul]
        congr 1
        field_simp
      rw [hval] at hmono
      have h2 : (2 : ℝ) ≤ Real.exp 2 := by
        have := Real.add_one_le_exp (2 : ℝ)
        linarith
      linarith
    have ht0 : (0 : ℝ) ≤ terminalFrequency X := by
      rw [terminalFrequency]
      have := Real.pi_pos
      positivity
    have hbound := abs_prefixPhase_add_le hYtwo ht0
    have hhalfpos : (0 : ℝ) < Real.log X ^ (A / 2) := Real.rpow_pos_of_pos hlogX _
    have hhalf : (Real.log X ^ A) ^ ((1 : ℝ) / 2) = Real.log X ^ (A / 2) := by
      rw [← Real.rpow_mul hlogX.le]
      congr 1
      ring
    have hdiv : Real.log X ^ (1 - A / 2) = Real.log X / Real.log X ^ (A / 2) := by
      rw [eq_div_iff (ne_of_gt hhalfpos), ← Real.rpow_add hlogX]
      norm_num
    have hlogY : Real.log (Real.log X ^ A) = A * Real.log (Real.log X) := Real.log_rpow hlogX A
    have hL2 : Real.log X ^ (2 : ℝ) = Real.log X * Real.log X := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    have hSnn : (0 : ℝ) ≤ primeRpowLogSumLE (1 / 2) (Real.log X ^ A) := by
      rw [primeRpowLogSumLE]
      refine Finset.sum_nonneg fun p hp => ?_
      have hprime := Nat.prime_of_mem_primesLE hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
      have hrp : (0 : ℝ) < (p : ℝ) ^ ((1 : ℝ) / 2 - 1) := Real.rpow_pos_of_pos hp0 _
      positivity
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hlogX.le (1 - A / 2))]
    calc |prefixPhase (Real.log X ^ A) (terminalFrequency X)
            + 2 * terminalFrequency X * prefixPhaseWeight (Real.log X ^ A)| *
          Real.log X ^ (1 - A / 2)
        ≤ (68 * terminalFrequency X ^ 3 * Real.log (Real.log X ^ A) ^ 2 *
            primeRpowLogSumLE (1 / 2) (Real.log X ^ A)) * Real.log X ^ (1 - A / 2) :=
          mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hlogX.le _)
      _ = 68 * Real.pi ^ 3 * A ^ 2 *
            (Real.log (Real.log X) ^ 2 / Real.log X ^ (2 : ℝ)) *
            (primeRpowLogSumLE (1 / 2) (Real.log X ^ A) /
              (Real.log X ^ A) ^ ((1 : ℝ) / 2)) := by
          rw [hlogY, hhalf, hdiv, hL2, terminalFrequency]
          field_simp
  have hsum := herr.add hmain
  rw [zero_add] at hsum
  refine hsum.congr fun X => ?_
  ring

end

end RHTower
