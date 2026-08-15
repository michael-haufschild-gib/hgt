import GaloisForLFunctions.RHTower.ZetaEulerLogPrimeSum
import GaloisForLFunctions.RHTower.EulerTiltMeanEnergy

/-!
# The zeta one-line deficit is the prime clock energy

At the canonical shift `δ = 1/log x` the logarithmic modulus of zeta on the line `Re s = 1 + δ`
differs from the prime clock energy by one absolute constant, uniformly in the frequency:

```text
log log x - log |ζ(1 + 1/log x + iτ)| = ∑_{p ≤ x} (1 - cos(τ log p))/p + O(1).
```

The three corrections are the prime-power correction of the Euler logarithm, the abscissa shift on
the head `p ≤ x`, and the tail `p > x`, which is bounded because a prime beyond `x` carries a
logarithm at least `log x`.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-! ## Prime-indexed coefficient sequences -/

/-- The prime rpow coefficient, extended by zero. -/
def primeRpowCoeff (σ : ℝ) (n : ℕ) : ℝ := if n.Prime then (n : ℝ) ^ (-σ) else 0

/-- The prime rpow-logarithm coefficient, extended by zero. -/
def primeRpowLogCoeff (σ : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then (n : ℝ) ^ (-σ) * Real.log n else 0

theorem primeRpowCoeff_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ primeRpowCoeff σ n := by
  rw [primeRpowCoeff]
  split
  · positivity
  · exact le_rfl

theorem primeRpowLogCoeff_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ primeRpowLogCoeff σ n := by
  rw [primeRpowLogCoeff]
  split
  · rename_i hp
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp.one_lt.le
    have hlog : 0 ≤ Real.log n := Real.log_nonneg h1
    positivity
  · exact le_rfl

theorem primeRpowCoeff_le_invRpow (σ : ℝ) (n : ℕ) :
    primeRpowCoeff σ n ≤ 1 / (n : ℝ) ^ σ := by
  rw [primeRpowCoeff]
  split
  · rename_i hp
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hp.pos
    rw [Real.rpow_neg hn0.le, one_div]
  · positivity

theorem primeRpowLogCoeff_le_logDiv (σ : ℝ) (n : ℕ) :
    primeRpowLogCoeff σ n ≤ Real.log n / (n : ℝ) ^ σ := by
  rw [primeRpowLogCoeff]
  split
  · rename_i hp
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hp.pos
    rw [Real.rpow_neg hn0.le]
    exact le_of_eq (by rw [div_eq_mul_inv]; ring)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hlog : 0 ≤ Real.log n := Real.log_nonneg h1
      positivity

theorem summable_primeRpowCoeff {σ : ℝ} (hσ : 1 < σ) : Summable (primeRpowCoeff σ) :=
  Summable.of_nonneg_of_le (fun n => primeRpowCoeff_nonneg σ n)
    (fun n => primeRpowCoeff_le_invRpow σ n) (Real.summable_one_div_nat_rpow.mpr hσ)

theorem summable_primeRpowLogCoeff {σ : ℝ} (hσ : 1 < σ) : Summable (primeRpowLogCoeff σ) :=
  Summable.of_nonneg_of_le (fun n => primeRpowLogCoeff_nonneg σ n)
    (fun n => primeRpowLogCoeff_le_logDiv σ n) (Mertens.summable_log_div_rpow hσ)

/-! ## Finite prime sums -/

theorem sum_range_primeRpowLogCoeff (σ : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), primeRpowLogCoeff σ n
      = ∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-σ) * Real.log p := by
  rw [Nat.primesLE, Nat.primesBelow, Finset.sum_filter]
  exact Finset.sum_congr rfl fun n _ => rfl

theorem sum_range_primeRpowCoeff (σ : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), primeRpowCoeff σ n
      = ∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-σ) := by
  rw [Nat.primesLE, Nat.primesBelow, Finset.sum_filter]
  exact Finset.sum_congr rfl fun n _ => rfl

/-- The uniform bound for the full tilted prime logarithm sum. -/
def tiltedPrimeLogTotalConst : ℝ := tiltedPrimeLogSumConst + Real.log 2

theorem tiltedPrimeLogTotalConst_nonneg : 0 ≤ tiltedPrimeLogTotalConst := by
  have h1 : 0 ≤ tiltedPrimeLogSumConst := by
    rw [tiltedPrimeLogSumConst]
    have := thetaRelMass_nonneg
    have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [tiltedPrimeLogTotalConst]
  linarith

theorem sum_primesLE_rpowLog_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-(1 + δ)) * Real.log p
      ≤ 1 / δ + tiltedPrimeLogTotalConst := by
  have hconst := tiltedPrimeLogTotalConst_nonneg
  rcases lt_or_ge N 2 with hN | hN
  · have hzero : ∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-(1 + δ)) * Real.log p = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      have hprime := Nat.prime_of_mem_primesLE hp
      have hple : p ≤ N := (Nat.mem_primesLE.mp hp).1
      have h2 := hprime.two_le
      exfalso
      omega
    rw [hzero]
    positivity
  · have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hfloor : ⌊(N : ℝ)⌋₊ = N := Nat.floor_natCast N
    have hexp : ∀ p : ℕ, (p : ℝ) ^ (-(1 + δ)) * Real.log p
        = (p : ℝ) ^ (-δ - 1) * Real.log p := by
      intro p
      congr 2
      ring
    have hsum : ∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-(1 + δ)) * Real.log p
        = tiltedPrimeLogSumLE δ (N : ℝ) := by
      rw [tiltedPrimeLogSumLE, hfloor]
      exact Finset.sum_congr rfl fun p _ => hexp p
    rw [hsum, tiltedPrimeLogSumLE_eq hNR]
    have hbound := abs_le.mp (abs_tiltedPrimeLogSum_sub_le hδ0 hδ1 hNR)
    have hrp : (2 : ℝ) ^ (-δ - 1) ≤ 1 := by
      have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
        (show -δ - 1 ≤ 0 by linarith)
      rwa [Real.rpow_zero] at h
    have hrp0 : (0 : ℝ) < (2 : ℝ) ^ (-δ - 1) := Real.rpow_pos_of_pos (by norm_num) _
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hNrp : (0 : ℝ) < (N : ℝ) ^ (-δ) := Real.rpow_pos_of_pos (by linarith) _
    have hdiv : (1 - (N : ℝ) ^ (-δ)) / δ ≤ 1 / δ := by
      rw [div_le_div_iff_of_pos_right hδ0]
      linarith
    rw [tiltedPrimeLogTotalConst]
    nlinarith [hbound.2, hrp, hrp0, hlog2, hdiv]

theorem tsum_primeRpowLogCoeff_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∑' n : ℕ, primeRpowLogCoeff (1 + δ) n ≤ 1 / δ + tiltedPrimeLogTotalConst := by
  have hsummable : Summable (primeRpowLogCoeff (1 + δ)) :=
    summable_primeRpowLogCoeff (by linarith)
  refine hsummable.tsum_le_of_sum_range_le fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · have hzero : ∑ n ∈ Finset.range 0, primeRpowLogCoeff (1 + δ) n = 0 := by simp
    have hconst := tiltedPrimeLogTotalConst_nonneg
    have hδinv : 0 < 1 / δ := by positivity
    rw [hzero]
    linarith
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
    rw [sum_range_primeRpowLogCoeff]
    exact sum_primesLE_rpowLog_le hδ0 hδ1 m

/-! ## The prime cosine coefficient and the tail -/

/-- The prime cosine coefficient, extended by zero. -/
def primeCosCoeff (σ τ : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then (n : ℝ) ^ (-σ) * Real.cos (τ * Real.log n) else 0

theorem abs_primeCosCoeff_le (σ τ : ℝ) (n : ℕ) :
    |primeCosCoeff σ τ n| ≤ primeRpowCoeff σ n := by
  rw [primeCosCoeff, primeRpowCoeff]
  split
  · rename_i hp
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hp.pos
    have hnn : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg hn0.le _
    rw [abs_mul, abs_of_nonneg hnn]
    have hcos : |Real.cos (τ * Real.log n)| ≤ 1 := Real.abs_cos_le_one _
    nlinarith [hcos, hnn]
  · simp

theorem summable_primeCosCoeff {σ τ : ℝ} (hσ : 1 < σ) : Summable (primeCosCoeff σ τ) := by
  refine Summable.of_norm_bounded (summable_primeRpowCoeff hσ) fun n => ?_
  rw [Real.norm_eq_abs]
  exact abs_primeCosCoeff_le σ τ n

theorem indicator_eq_primeCosCoeff (σ τ : ℝ) :
    Set.indicator {n : ℕ | n.Prime} (fun n => (n : ℝ) ^ (-σ) * Real.cos (τ * Real.log n))
      = primeCosCoeff σ τ := by
  funext n
  rw [Set.indicator_apply, primeCosCoeff]
  by_cases hp : n.Prime
  · rw [if_pos (show n ∈ {n : ℕ | n.Prime} from hp), if_pos hp]
  · rw [if_neg (show n ∉ {n : ℕ | n.Prime} from hp), if_neg hp]

theorem primeCosTsum_eq_tsum_coeff {σ τ : ℝ} :
    primeCosTsum σ τ = ∑' n : ℕ, primeCosCoeff σ τ n := by
  have h := tsum_subtype {n : ℕ | n.Prime}
    (fun n : ℕ => (n : ℝ) ^ (-σ) * Real.cos (τ * Real.log n))
  rw [indicator_eq_primeCosCoeff] at h
  rw [primeCosTsum, ← h]
  rfl

/-! ## The tail beyond the cutoff -/

theorem primeRpowCoeff_le_logCoeff_div {δ x : ℝ} (hx : 1 < x) {n : ℕ} (hn : x ≤ (n : ℝ)) :
    primeRpowCoeff (1 + δ) n ≤ primeRpowLogCoeff (1 + δ) n / Real.log x := by
  have hlogx : 0 < Real.log x := Real.log_pos hx
  rw [primeRpowCoeff, primeRpowLogCoeff]
  split
  · rename_i hp
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hp.pos
    have hnn : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 + δ)) := Real.rpow_nonneg hn0.le _
    have hlogn : Real.log x ≤ Real.log n := Real.log_le_log (by linarith) hn
    rw [le_div_iff₀ hlogx]
    nlinarith [hnn, hlogn, hlogx]
  · positivity

theorem tsum_tail_primeRpowCoeff_le {δ x : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hx : 2 ≤ x) :
    ∑' n : ↥((Finset.range (⌊x⌋₊ + 1) : Finset ℕ) : Set ℕ)ᶜ, primeRpowCoeff (1 + δ) (n : ℕ)
      ≤ (1 / δ + tiltedPrimeLogTotalConst) / Real.log x := by
  have hσ : (1 : ℝ) < 1 + δ := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hsum := summable_primeRpowCoeff hσ
  have hsumlog := summable_primeRpowLogCoeff hσ
  have hsub : Summable (fun n : ↥((Finset.range (⌊x⌋₊ + 1) : Finset ℕ) : Set ℕ)ᶜ =>
      primeRpowCoeff (1 + δ) (n : ℕ)) := hsum.subtype _
  have hdivsum : Summable (fun n : ℕ => primeRpowLogCoeff (1 + δ) n / Real.log x) :=
    hsumlog.div_const _
  have hcompare : ∑' n : ↥((Finset.range (⌊x⌋₊ + 1) : Finset ℕ) : Set ℕ)ᶜ,
      primeRpowCoeff (1 + δ) (n : ℕ)
      ≤ ∑' n : ℕ, primeRpowLogCoeff (1 + δ) n / Real.log x := by
    refine Summable.tsum_le_tsum_of_inj (fun n => (n : ℕ)) Subtype.val_injective ?_ ?_ hsub hdivsum
    · intro n _
      have := primeRpowLogCoeff_nonneg (1 + δ) n
      positivity
    · intro n
      have hmem : (n : ℕ) ∉ Finset.range (⌊x⌋₊ + 1) := by
        have := n.prop
        simpa using this
      have hge : ⌊x⌋₊ + 1 ≤ (n : ℕ) := by
        rw [Finset.mem_range] at hmem
        omega
      have hxle : x ≤ ((n : ℕ) : ℝ) := by
        have hfl := Nat.lt_floor_add_one x
        have : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hge
        push_cast at this
        linarith
      exact primeRpowCoeff_le_logCoeff_div hx1 hxle
  have hval : ∑' n : ℕ, primeRpowLogCoeff (1 + δ) n / Real.log x
      = (∑' n : ℕ, primeRpowLogCoeff (1 + δ) n) / Real.log x := tsum_div_const
  rw [hval] at hcompare
  refine le_trans hcompare ?_
  exact div_le_div_of_nonneg_right (tsum_primeRpowLogCoeff_le hδ0 hδ1) hlogx.le

theorem abs_tsum_sub_sum_primeCosCoeff_le {δ τ x : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hx : 2 ≤ x) :
    |(∑' n : ℕ, primeCosCoeff (1 + δ) τ n)
        - ∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) ^ (-(1 + δ)) * Real.cos (τ * Real.log p)|
      ≤ (1 / δ + tiltedPrimeLogTotalConst) / Real.log x := by
  have hσ : (1 : ℝ) < 1 + δ := by linarith
  have hsum := summable_primeCosCoeff (σ := 1 + δ) (τ := τ) hσ
  have hsplit := hsum.sum_add_tsum_compl (s := Finset.range (⌊x⌋₊ + 1))
  have hhead : ∑ n ∈ Finset.range (⌊x⌋₊ + 1), primeCosCoeff (1 + δ) τ n
      = ∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) ^ (-(1 + δ)) * Real.cos (τ * Real.log p) := by
    rw [Nat.primesLE, Nat.primesBelow, Finset.sum_filter]
    exact Finset.sum_congr rfl fun n _ => rfl
  have hdiff : (∑' n : ℕ, primeCosCoeff (1 + δ) τ n)
      - ∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) ^ (-(1 + δ)) * Real.cos (τ * Real.log p)
      = ∑' n : ↥((Finset.range (⌊x⌋₊ + 1) : Finset ℕ) : Set ℕ)ᶜ,
          primeCosCoeff (1 + δ) τ (n : ℕ) := by
    rw [← hsplit, hhead]
    ring
  rw [hdiff]
  have hsubcos : Summable (fun n : ↥((Finset.range (⌊x⌋₊ + 1) : Finset ℕ) : Set ℕ)ᶜ =>
      primeCosCoeff (1 + δ) τ (n : ℕ)) := hsum.subtype _
  have hsubrpow : Summable (fun n : ↥((Finset.range (⌊x⌋₊ + 1) : Finset ℕ) : Set ℕ)ᶜ =>
      primeRpowCoeff (1 + δ) (n : ℕ)) := (summable_primeRpowCoeff hσ).subtype _
  have habs : Summable (fun n : ↥((Finset.range (⌊x⌋₊ + 1) : Finset ℕ) : Set ℕ)ᶜ =>
      ‖primeCosCoeff (1 + δ) τ (n : ℕ)‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hsubrpow
    rw [Real.norm_eq_abs]
    exact abs_primeCosCoeff_le _ _ _
  have h1 := norm_tsum_le_tsum_norm habs
  have h2 : ∑' n : ↥((Finset.range (⌊x⌋₊ + 1) : Finset ℕ) : Set ℕ)ᶜ,
      ‖primeCosCoeff (1 + δ) τ (n : ℕ)‖
      ≤ ∑' n : ↥((Finset.range (⌊x⌋₊ + 1) : Finset ℕ) : Set ℕ)ᶜ,
        primeRpowCoeff (1 + δ) (n : ℕ) := by
    refine Summable.tsum_le_tsum (fun n => ?_) habs hsubrpow
    rw [Real.norm_eq_abs]
    exact abs_primeCosCoeff_le _ _ _
  have h3 := tsum_tail_primeRpowCoeff_le hδ0 hδ1 hx
  rw [Real.norm_eq_abs] at h1
  linarith [h1, h2, h3]

/-! ## The abscissa shift on the head -/

theorem abs_sum_primeCos_shift_le {δ τ x : ℝ} (hδ : 0 ≤ δ) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) ^ (-(1 + δ)) * Real.cos (τ * Real.log p)
        - ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.cos (τ * Real.log p) / p|
      ≤ δ * mertensPrimeWeightSum ⌊x⌋₊ := by
  have hdiff : ∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) ^ (-(1 + δ)) * Real.cos (τ * Real.log p)
      - ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.cos (τ * Real.log p) / p
      = ∑ p ∈ Nat.primesLE ⌊x⌋₊,
        ((p : ℝ) ^ (-(1 + δ)) * Real.cos (τ * Real.log p)
          - Real.cos (τ * Real.log p) / p) := by
    rw [← Finset.sum_sub_distrib]
  rw [hdiff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [← sum_primesLE_log_div_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hprime := Nat.prime_of_mem_primesLE hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hfactor : (p : ℝ) ^ (-(1 + δ)) = ((p : ℝ))⁻¹ * (p : ℝ) ^ (-δ) := by
    have hinv : (p : ℝ) ^ (-(1 : ℝ)) = ((p : ℝ))⁻¹ := Real.rpow_neg_one _
    rw [← hinv, ← Real.rpow_add hp0]
    congr 1
    ring
  have htilt : 1 - (p : ℝ) ^ (-δ) ≤ δ * Real.log p := by
    have hexp : (p : ℝ) ^ (-δ) = Real.exp (-(δ * Real.log p)) := by
      rw [Real.rpow_def_of_pos hp0]
      congr 1
      ring
    have h := Real.add_one_le_exp (-(δ * Real.log p))
    rw [hexp]
    linarith
  have htiltle : (p : ℝ) ^ (-δ) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ (p : ℝ) by linarith)
      (show -δ ≤ 0 by linarith)
    rwa [Real.rpow_zero] at h
  have hcos : |Real.cos (τ * Real.log p)| ≤ 1 := Real.abs_cos_le_one _
  have hval : (p : ℝ) ^ (-(1 + δ)) * Real.cos (τ * Real.log p)
      - Real.cos (τ * Real.log p) / p
      = -(((p : ℝ))⁻¹ * (1 - (p : ℝ) ^ (-δ)) * Real.cos (τ * Real.log p)) := by
    rw [hfactor]
    field_simp
    ring
  rw [hval, abs_neg, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((p : ℝ))⁻¹),
    abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - (p : ℝ) ^ (-δ))]
  have hstep : ((p : ℝ))⁻¹ * (1 - (p : ℝ) ^ (-δ)) * |Real.cos (τ * Real.log p)|
      ≤ ((p : ℝ))⁻¹ * (δ * Real.log p) * 1 := by
    have h1 : ((p : ℝ))⁻¹ * (1 - (p : ℝ) ^ (-δ)) ≤ ((p : ℝ))⁻¹ * (δ * Real.log p) :=
      mul_le_mul_of_nonneg_left htilt (by positivity)
    have h2 : (0 : ℝ) ≤ ((p : ℝ))⁻¹ * (1 - (p : ℝ) ^ (-δ)) := by
      have : (0 : ℝ) ≤ 1 - (p : ℝ) ^ (-δ) := by linarith
      positivity
    nlinarith [h1, h2, hcos, abs_nonneg (Real.cos (τ * Real.log p))]
  refine le_trans hstep (le_of_eq ?_)
  field_simp

/-! ## The deficit identity -/

/-- The prime clock energy `∑_{p ≤ x} (1 - cos(τ log p))/p`. -/
def primeClockEnergy (τ x : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 - Real.cos (τ * Real.log p)) / p

theorem sum_primeCos_div_eq (τ x : ℝ) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.cos (τ * Real.log p) / p
      = Sieve.mertensS ⌊x⌋₊ - primeClockEnergy τ x := by
  rw [Sieve.mertensS, primeClockEnergy, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← sub_div]
  congr 1
  ring

/-- The absolute constant of the one-line deficit identity. -/
def zetaDeficitConst : ℝ :=
  invSquareTailConst + (1 + (mertensPrimeWindowBound + 1) / 2)
    + (1 + tiltedPrimeLogTotalConst / 2)
    + (|Sieve.meisselMertensConst| + (2 * Sieve.mertensFirstConst + 1 / 2) + 1)

/-- **(Z2a) The shifted zeta deficit is the prime clock energy.**  Uniformly in the frequency, the
one-line logarithmic modulus at the canonical shift `1/log x` differs from `log log x` minus the
prime clock energy by one absolute constant. -/
theorem abs_zeta_deficit_sub_primeClockEnergy_le {τ x : ℝ} (hx : Real.exp 2 ≤ x) :
    |Real.log (Real.log x)
        - Real.log ‖riemannZeta (zetaLinePoint (1 + 1 / Real.log x) τ)‖
        - primeClockEnergy τ x| ≤ zetaDeficitConst := by
  have hexp2 : (7 : ℝ) < Real.exp 2 := by
    have h := Real.exp_one_gt_d9
    have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [h, Real.exp_pos 1, hsq]
  have hx7 : (7 : ℝ) < x := lt_of_lt_of_le hexp2 hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hlogx : (2 : ℝ) ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 2) hx
    rwa [Real.log_exp] at h
  have hlogx0 : (0 : ℝ) < Real.log x := by linarith
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 / Real.log x := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ1 : δ ≤ 1 / 2 := by
    rw [hδdef, div_le_div_iff₀ hlogx0 (by norm_num)]
    linarith
  have hδle1 : δ ≤ 1 := by linarith
  have hδlog : δ * Real.log x = 1 := by
    rw [hδdef]
    field_simp
  -- step 1: the Euler logarithm
  have hre : (1 : ℝ) < (zetaLinePoint (1 + δ) τ).re := by
    rw [zetaLinePoint_re]
    linarith
  have h1 : Real.log ‖riemannZeta (zetaLinePoint (1 + δ) τ)‖
      = (canonicalEulerLogZeta (zetaLinePoint (1 + δ) τ)).re :=
    log_norm_riemannZeta_eq_re_eulerLog hre
  have h2 := abs_le.mp (abs_re_eulerLog_sub_primeCosTsum_le (σ := 1 + δ) (τ := τ)
    (by linarith))
  have h3 : primeCosTsum (1 + δ) τ = ∑' n : ℕ, primeCosCoeff (1 + δ) τ n :=
    primeCosTsum_eq_tsum_coeff
  have h4 := abs_le.mp (abs_tsum_sub_sum_primeCosCoeff_le (δ := δ) (τ := τ) (x := x)
    hδ0 hδle1 hx2)
  have h5 := abs_le.mp (abs_sum_primeCos_shift_le (δ := δ) (τ := τ) (x := x) hδ0.le)
  have h6 := sum_primeCos_div_eq τ x
  -- the tail and shift constants
  have htail : (1 / δ + tiltedPrimeLogTotalConst) / Real.log x
      ≤ 1 + tiltedPrimeLogTotalConst / 2 := by
    have hinv : 1 / δ = Real.log x := by
      rw [hδdef, one_div_one_div]
    rw [hinv, add_div, div_self (ne_of_gt hlogx0)]
    have hconst := tiltedPrimeLogTotalConst_nonneg
    have : tiltedPrimeLogTotalConst / Real.log x ≤ tiltedPrimeLogTotalConst / 2 :=
      div_le_div_of_nonneg_left hconst (by norm_num) hlogx
    linarith
  have hweight := abs_le.mp (abs_mertensPrimeWeightSum_floor_sub_log_le hx2)
  have hW := mertensPrimeWindowBound_nonneg
  have hshift : δ * mertensPrimeWeightSum ⌊x⌋₊ ≤ 1 + (mertensPrimeWindowBound + 1) / 2 := by
    have hle : mertensPrimeWeightSum ⌊x⌋₊ ≤ Real.log x + (mertensPrimeWindowBound + 1) := by
      linarith [hweight.2]
    have hstep : δ * mertensPrimeWeightSum ⌊x⌋₊
        ≤ δ * (Real.log x + (mertensPrimeWindowBound + 1)) :=
      mul_le_mul_of_nonneg_left hle hδ0.le
    have hval : δ * (Real.log x + (mertensPrimeWindowBound + 1))
        = 1 + δ * (mertensPrimeWindowBound + 1) := by
      rw [mul_add, hδlog]
    rw [hval] at hstep
    nlinarith [hstep, hδ1, hW]
  -- step 2: Mertens' second theorem
  have hfloor2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx2)
  have hfloor6 : (6 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by
    have h : (6 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (6 : ℝ) ≤ x))
    exact_mod_cast h
  have hexp1 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hlogfloor : (1 : ℝ) ≤ Real.log ((⌊x⌋₊ : ℕ) : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ ((⌊x⌋₊ : ℕ) : ℝ) by linarith)
    rwa [Real.log_exp] at h
  have hmertens := abs_le.mp (Sieve.abs_mertensS_sub_logLog_sub_const_le hfloor2)
  have hfloorlog := abs_le.mp (abs_logLog_floor_sub_le hx)
  have hC1 : 0 ≤ 2 * Sieve.mertensFirstConst + 1 / 2 := by
    have := Sieve.mertensFirstConst_nonneg
    linarith
  have hdiv : (2 * Sieve.mertensFirstConst + 1 / 2) / Real.log ((⌊x⌋₊ : ℕ) : ℝ)
      ≤ 2 * Sieve.mertensFirstConst + 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hC1, hlogfloor]
  have hmabs : Sieve.meisselMertensConst ≤ |Sieve.meisselMertensConst| := le_abs_self _
  have hmabs' : -|Sieve.meisselMertensConst| ≤ Sieve.meisselMertensConst := neg_abs_le _
  have hinvnn : 0 ≤ invSquareTailConst := by
    rw [invSquareTailConst]
    exact tsum_nonneg invSquareTail_nonneg
  rw [← hδdef, zetaDeficitConst, abs_le]
  constructor
  · linarith [h2.1, h2.2, h4.1, h4.2, h5.1, h5.2, htail, hshift, hmertens.1, hmertens.2,
      hfloorlog.1, hfloorlog.2, hdiv, hmabs, hmabs', h6, hinvnn]
  · linarith [h2.1, h2.2, h4.1, h4.2, h5.1, h5.2, htail, hshift, hmertens.1, hmertens.2,
      hfloorlog.1, hfloorlog.2, hdiv, hmabs, hmabs', h6, hinvnn]

end

end RHTower
