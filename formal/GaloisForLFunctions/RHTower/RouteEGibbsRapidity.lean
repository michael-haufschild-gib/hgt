import GaloisForLFunctions.RHTower.RouteEGibbsPrefixModulus

/-!
# The batch rapidity at the terminal frequency

The complete odd cube of a growing batch `Y < p ≤ X` is one additive rapidity

```text
R_X = ∑_{Y < p ≤ X} artanh(2 d_p cos(t_X log p)),   d_p = p^{-1/2}/(1 + p^{-1}),
```

and at the terminal frequency `t_X = π/log X` with `Y = (log X)^A` it equals
`-(4√X/log X)(1 + o(1))`: the linear grade is the critical cosine sum, the `artanh` correction is
`O(∑ 1/p)`, the `d_p` versus `p^{-1/2}` correction is `O(∑ 1/p)`, and the discarded prefix is
`O(√Y)`.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- The critical half density `d_p = p^{-1/2}/(1 + p^{-1})`. -/
def criticalHalfDensity (p : ℕ) : ℝ := (p : ℝ) ^ (-(1 : ℝ) / 2) / (1 + (p : ℝ)⁻¹)

/-- The batch rapidity `∑_{Y < p ≤ X} artanh(2 d_p cos(t_X log p))`. -/
def batchRapidity (Y X : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc ⌊Y⌋₊ ⌊X⌋₊,
    (if k.Prime then Real.artanh (2 * criticalHalfDensity k *
      Real.cos (terminalFrequency X * Real.log k)) else 0)

theorem criticalHalfDensity_pos {p : ℕ} (hp : 0 < p) : 0 < criticalHalfDensity p := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hrp : (0 : ℝ) < (p : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hp0 _
  have hden : (0 : ℝ) < 1 + (p : ℝ)⁻¹ := by positivity
  rw [criticalHalfDensity]
  positivity

theorem criticalHalfDensity_le {p : ℕ} (hp : 0 < p) :
    criticalHalfDensity p ≤ (p : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hrp : (0 : ℝ) < (p : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hp0 _
  have hden : (1 : ℝ) ≤ 1 + (p : ℝ)⁻¹ := by
    have : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
    linarith
  rw [criticalHalfDensity, div_le_iff₀ (by linarith)]
  nlinarith [hrp, hden]

/-- The square-root density and the critical half density differ by at most `1/p`. -/
theorem sub_criticalHalfDensity_le {p : ℕ} (hp : 1 ≤ p) :
    (p : ℝ) ^ (-(1 : ℝ) / 2) - criticalHalfDensity p ≤ (p : ℝ)⁻¹ := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hrp : (0 : ℝ) < (p : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hp0 _
  have hrple : (p : ℝ) ^ (-(1 : ℝ) / 2) ≤ 1 := by
    have hsq : ((p : ℝ) ^ (-(1 : ℝ) / 2)) * ((p : ℝ) ^ (-(1 : ℝ) / 2)) = (p : ℝ)⁻¹ := by
      rw [← Real.rpow_add hp0]
      norm_num
      rw [Real.rpow_neg_one]
    have hinv : (p : ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      exact hp1
    nlinarith [hrp, hsq, hinv]
  have hden : (0 : ℝ) < 1 + (p : ℝ)⁻¹ := by positivity
  have hval : (p : ℝ) ^ (-(1 : ℝ) / 2) - criticalHalfDensity p
      = (p : ℝ) ^ (-(1 : ℝ) / 2) * ((p : ℝ)⁻¹ / (1 + (p : ℝ)⁻¹)) := by
    rw [criticalHalfDensity]
    field_simp
    ring
  rw [hval]
  have hfrac : (p : ℝ)⁻¹ / (1 + (p : ℝ)⁻¹) ≤ (p : ℝ)⁻¹ := by
    rw [div_le_iff₀ hden]
    have : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
    nlinarith
  have hinv0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  calc (p : ℝ) ^ (-(1 : ℝ) / 2) * ((p : ℝ)⁻¹ / (1 + (p : ℝ)⁻¹))
      ≤ (p : ℝ) ^ (-(1 : ℝ) / 2) * (p : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hfrac hrp.le
    _ ≤ 1 * (p : ℝ)⁻¹ := mul_le_mul_of_nonneg_right hrple hinv0
    _ = (p : ℝ)⁻¹ := by ring

/-- Past `16` the local rapidity argument is at most `1/2` in absolute value. -/
theorem abs_two_mul_criticalHalfDensity_mul_cos_le {p : ℕ} (hp : 16 ≤ p) (φ : ℝ) :
    |2 * criticalHalfDensity p * Real.cos φ| ≤ 1 / 2 := by
  have hp0 : 0 < p := by omega
  have hp16 : (16 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0R : (0 : ℝ) < (p : ℝ) := by linarith
  have hd0 := criticalHalfDensity_pos hp0
  have hdle := criticalHalfDensity_le hp0
  have hrp : (0 : ℝ) < (p : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hp0R _
  have hsq : ((p : ℝ) ^ (-(1 : ℝ) / 2)) * ((p : ℝ) ^ (-(1 : ℝ) / 2)) = (p : ℝ)⁻¹ := by
    rw [← Real.rpow_add hp0R]
    norm_num
    rw [Real.rpow_neg_one]
  have hinv16 : (p : ℝ)⁻¹ ≤ 1 / 16 := by
    rw [inv_le_comm₀ hp0R (by norm_num)]
    linarith
  have hquarter : (p : ℝ) ^ (-(1 : ℝ) / 2) ≤ 1 / 4 := by nlinarith [hrp, hsq, hinv16]
  have hcos : |Real.cos φ| ≤ 1 := Real.abs_cos_le_one φ
  have habs : |2 * criticalHalfDensity p * Real.cos φ|
      = 2 * criticalHalfDensity p * |Real.cos φ| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * criticalHalfDensity p)]
  rw [habs]
  nlinarith [hd0, hdle, hquarter, hcos, abs_nonneg (Real.cos φ)]

/-! ## The linear grade of the batch -/

/-- The batch cosine sum with the pure square-root density. -/
def batchCosSum (Y X : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc ⌊Y⌋₊ ⌊X⌋₊,
    (if k.Prime then (k : ℝ) ^ (-(1 : ℝ) / 2) *
      Real.cos (terminalFrequency X * Real.log k) else 0)

/-- **The rapidity is its linear grade up to a Mertens remainder.** -/
theorem abs_batchRapidity_sub_two_mul_batchCosSum_le {Y X : ℝ} (hY : 16 ≤ Y)
    (hYX : Y ≤ X) :
    |batchRapidity Y X - 2 * batchCosSum Y X| ≤ 18 * Sieve.mertensS ⌊X⌋₊ := by
  have hfloorY : 16 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
  have hfloorle : ⌊Y⌋₊ ≤ ⌊X⌋₊ := Nat.floor_le_floor hYX
  have hdiff : batchRapidity Y X - 2 * batchCosSum Y X
      = ∑ k ∈ Finset.Ioc ⌊Y⌋₊ ⌊X⌋₊,
        (if k.Prime then Real.artanh (2 * criticalHalfDensity k *
            Real.cos (terminalFrequency X * Real.log k))
          - 2 * ((k : ℝ) ^ (-(1 : ℝ) / 2) *
            Real.cos (terminalFrequency X * Real.log k)) else 0) := by
    rw [batchRapidity, batchCosSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hp : k.Prime
    · rw [if_pos hp, if_pos hp, if_pos hp]
    · rw [if_neg hp, if_neg hp, if_neg hp]
      ring
  rw [hdiff]
  have hterm : ∀ k ∈ Finset.Ioc ⌊Y⌋₊ ⌊X⌋₊,
      |(if k.Prime then Real.artanh (2 * criticalHalfDensity k *
          Real.cos (terminalFrequency X * Real.log k))
        - 2 * ((k : ℝ) ^ (-(1 : ℝ) / 2) *
          Real.cos (terminalFrequency X * Real.log k)) else 0)|
        ≤ (if k.Prime then 18 * (k : ℝ)⁻¹ else 0) := by
    intro k hk
    rw [Finset.mem_Ioc] at hk
    by_cases hp : k.Prime
    · rw [if_pos hp, if_pos hp]
      have hk16 : 16 ≤ k := by omega
      have hk0 : 0 < k := by omega
      have hk0R : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
      have hk1 : 1 ≤ k := by omega
      have hcos : |Real.cos (terminalFrequency X * Real.log k)| ≤ 1 :=
        Real.abs_cos_le_one _
      have hrp : (0 : ℝ) < (k : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hk0R _
      have hd0 := criticalHalfDensity_pos hk0
      have hdle := criticalHalfDensity_le hk0
      have habs := abs_two_mul_criticalHalfDensity_mul_cos_le hk16
        (terminalFrequency X * Real.log k)
      have hartanh := HTGeometry.abs_artanh_sub_self_le habs
      have hsq : ((k : ℝ) ^ (-(1 : ℝ) / 2)) * ((k : ℝ) ^ (-(1 : ℝ) / 2)) = (k : ℝ)⁻¹ := by
        rw [← Real.rpow_add hk0R]
        norm_num
        rw [Real.rpow_neg_one]
      -- the quadratic `artanh` correction
      have hquad : (2 * criticalHalfDensity k *
          Real.cos (terminalFrequency X * Real.log k)) ^ 2 ≤ 4 * (k : ℝ)⁻¹ := by
        have hbase : |2 * criticalHalfDensity k *
            Real.cos (terminalFrequency X * Real.log k)| ≤ 2 * (k : ℝ) ^ (-(1 : ℝ) / 2) := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * criticalHalfDensity k)]
          nlinarith [hcos, hd0, hdle, abs_nonneg (Real.cos (terminalFrequency X * Real.log k))]
        have hsqabs := sq_abs (2 * criticalHalfDensity k *
          Real.cos (terminalFrequency X * Real.log k))
        nlinarith [hbase, abs_nonneg (2 * criticalHalfDensity k *
          Real.cos (terminalFrequency X * Real.log k)), hsq, hrp]
      -- the density correction
      have hdens : |2 * criticalHalfDensity k * Real.cos (terminalFrequency X * Real.log k)
          - 2 * ((k : ℝ) ^ (-(1 : ℝ) / 2) *
            Real.cos (terminalFrequency X * Real.log k))|
          ≤ 2 * (k : ℝ)⁻¹ := by
        have hval : 2 * criticalHalfDensity k * Real.cos (terminalFrequency X * Real.log k)
            - 2 * ((k : ℝ) ^ (-(1 : ℝ) / 2) *
              Real.cos (terminalFrequency X * Real.log k))
            = -(2 * ((k : ℝ) ^ (-(1 : ℝ) / 2) - criticalHalfDensity k)) *
              Real.cos (terminalFrequency X * Real.log k) := by ring
        rw [hval, abs_mul, abs_neg]
        have hgap := sub_criticalHalfDensity_le hk1
        have hgap0 : (0 : ℝ) ≤ (k : ℝ) ^ (-(1 : ℝ) / 2) - criticalHalfDensity k := by linarith
        have habs2 : |2 * ((k : ℝ) ^ (-(1 : ℝ) / 2) - criticalHalfDensity k)|
            = 2 * ((k : ℝ) ^ (-(1 : ℝ) / 2) - criticalHalfDensity k) := by
          rw [abs_of_nonneg (by linarith)]
        rw [habs2]
        nlinarith [hcos, hgap, hgap0, abs_nonneg (Real.cos (terminalFrequency X * Real.log k))]
      have hsplit : |Real.artanh (2 * criticalHalfDensity k *
            Real.cos (terminalFrequency X * Real.log k))
          - 2 * ((k : ℝ) ^ (-(1 : ℝ) / 2) *
            Real.cos (terminalFrequency X * Real.log k))|
          ≤ |Real.artanh (2 * criticalHalfDensity k *
              Real.cos (terminalFrequency X * Real.log k))
            - 2 * criticalHalfDensity k * Real.cos (terminalFrequency X * Real.log k)|
            + |2 * criticalHalfDensity k * Real.cos (terminalFrequency X * Real.log k)
              - 2 * ((k : ℝ) ^ (-(1 : ℝ) / 2) *
                Real.cos (terminalFrequency X * Real.log k))| := by
        have h := abs_add_le
          (Real.artanh (2 * criticalHalfDensity k *
            Real.cos (terminalFrequency X * Real.log k))
            - 2 * criticalHalfDensity k * Real.cos (terminalFrequency X * Real.log k))
          (2 * criticalHalfDensity k * Real.cos (terminalFrequency X * Real.log k)
            - 2 * ((k : ℝ) ^ (-(1 : ℝ) / 2) *
              Real.cos (terminalFrequency X * Real.log k)))
        have heq : (Real.artanh (2 * criticalHalfDensity k *
              Real.cos (terminalFrequency X * Real.log k))
            - 2 * criticalHalfDensity k * Real.cos (terminalFrequency X * Real.log k))
            + (2 * criticalHalfDensity k * Real.cos (terminalFrequency X * Real.log k)
              - 2 * ((k : ℝ) ^ (-(1 : ℝ) / 2) *
                Real.cos (terminalFrequency X * Real.log k)))
            = Real.artanh (2 * criticalHalfDensity k *
                Real.cos (terminalFrequency X * Real.log k))
              - 2 * ((k : ℝ) ^ (-(1 : ℝ) / 2) *
                Real.cos (terminalFrequency X * Real.log k)) := by ring
        rw [heq] at h
        exact h
      have hfirst : |Real.artanh (2 * criticalHalfDensity k *
            Real.cos (terminalFrequency X * Real.log k))
          - 2 * criticalHalfDensity k * Real.cos (terminalFrequency X * Real.log k)|
          ≤ 16 * (k : ℝ)⁻¹ := by
        have hmul : 2 * criticalHalfDensity k * Real.cos (terminalFrequency X * Real.log k)
            = 2 * criticalHalfDensity k * Real.cos (terminalFrequency X * Real.log k) := rfl
        calc |Real.artanh (2 * criticalHalfDensity k *
              Real.cos (terminalFrequency X * Real.log k))
            - 2 * criticalHalfDensity k * Real.cos (terminalFrequency X * Real.log k)|
            ≤ 4 * (2 * criticalHalfDensity k *
                Real.cos (terminalFrequency X * Real.log k)) ^ 2 := hartanh
          _ ≤ 4 * (4 * (k : ℝ)⁻¹) := by linarith
          _ = 16 * (k : ℝ)⁻¹ := by ring
      linarith [hsplit, hfirst, hdens]
    · rw [if_neg hp, if_neg hp, abs_zero]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  -- compare with the Mertens sum
  have hsub : (Finset.Ioc ⌊Y⌋₊ ⌊X⌋₊).filter Nat.Prime ⊆ Nat.primesLE ⌊X⌋₊ := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Ioc] at hk
    rw [Nat.mem_primesLE]
    exact ⟨hk.1.2, hk.2⟩
  have hrw : ∑ k ∈ Finset.Ioc ⌊Y⌋₊ ⌊X⌋₊, (if k.Prime then 18 * (k : ℝ)⁻¹ else 0)
      = ∑ k ∈ (Finset.Ioc ⌊Y⌋₊ ⌊X⌋₊).filter Nat.Prime, 18 * (k : ℝ)⁻¹ := by
    rw [Finset.sum_filter]
  rw [hrw, Sieve.mertensS, Finset.mul_sum]
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_ |>.trans (le_of_eq ?_)
  · intro k hk _
    have hprime := Nat.prime_of_mem_primesLE hk
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hprime.pos
    positivity
  · exact Finset.sum_congr rfl fun p _ => by rw [one_div]

/-! ## Two majorants -/

/-- A real power of the logarithm is negligible against any positive power. -/
theorem tendsto_logRpow_div_rpow {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun X : ℝ => Real.log X ^ b / X ^ a) atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_ (HTGeometry.tendsto_logPow_div_rpow ha ⌈b⌉₊)
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with X hX
    have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
    have hlog : (1 : ℝ) ≤ Real.log X := by
      have h := Real.log_le_log (Real.exp_pos 1) hX
      rwa [Real.log_exp] at h
    exact div_nonneg (Real.rpow_nonneg (by linarith) b) (Real.rpow_pos_of_pos hX0 a).le
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with X hX
    have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
    have hlog : (1 : ℝ) ≤ Real.log X := by
      have h := Real.log_le_log (Real.exp_pos 1) hX
      rwa [Real.log_exp] at h
    have hle : Real.log X ^ b ≤ Real.log X ^ ((⌈b⌉₊ : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hlog (Nat.le_ceil b)
    rw [Real.rpow_natCast] at hle
    exact div_le_div_of_nonneg_right hle (Real.rpow_pos_of_pos hX0 a).le

/-- The Mertens remainder is negligible against the terminal scale. -/
theorem tendsto_mertensS_floor_mul_log_div_sqrt :
    Tendsto (fun X : ℝ => Sieve.mertensS ⌊X⌋₊ * Real.log X / X ^ ((1 : ℝ) / 2)) atTop
      (nhds 0) := by
  have hmaj : Tendsto (fun X : ℝ =>
      (Real.log X + Sieve.mertensUpperConst) * Real.log X / X ^ ((1 : ℝ) / 2)) atTop
      (nhds 0) := by
    have ha : (0 : ℝ) < 1 / 2 := by norm_num
    have h2 := HTGeometry.tendsto_logPow_div_rpow ha 2
    have h1 := HTGeometry.tendsto_logPow_div_rpow ha 1
    have h := h2.add (h1.const_mul Sieve.mertensUpperConst)
    rw [mul_zero, add_zero] at h
    refine h.congr fun X => ?_
    rw [pow_one, ← mul_div_assoc, ← add_div]
    congr 1
    ring
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop (3 : ℝ)] with X hX
    have hX0 : (0 : ℝ) < X := by linarith
    have hlog : (0 : ℝ) ≤ Real.log X := Real.log_nonneg (by linarith)
    have hm : (0 : ℝ) ≤ Sieve.mertensS ⌊X⌋₊ := by
      rw [Sieve.mertensS]
      refine Finset.sum_nonneg fun p _ => ?_
      positivity
    exact div_nonneg (mul_nonneg hm hlog) (Real.rpow_pos_of_pos hX0 _).le
  · filter_upwards [eventually_ge_atTop (3 : ℝ)] with X hX
    have hX0 : (0 : ℝ) < X := by linarith
    have hlog : (0 : ℝ) ≤ Real.log X := Real.log_nonneg (by linarith)
    have hfloor3 : 3 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
    have hfloor2 : 2 ≤ ⌊X⌋₊ := by omega
    have hmert := Sieve.mertensS_le_logLog_add hfloor2
    have hfloorR : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le (by linarith)
    have hfloor3R : (3 : ℝ) ≤ ((⌊X⌋₊ : ℕ) : ℝ) := by exact_mod_cast hfloor3
    have hlogfloor : (0 : ℝ) < Real.log ((⌊X⌋₊ : ℕ) : ℝ) :=
      Real.log_pos (by linarith)
    have hlogle : Real.log ((⌊X⌋₊ : ℕ) : ℝ) ≤ Real.log X :=
      Real.log_le_log (by linarith) hfloorR
    have hloglog : Sieve.logLog ⌊X⌋₊ ≤ Real.log X := by
      rw [Sieve.logLog]
      calc Real.log (Real.log ((⌊X⌋₊ : ℕ) : ℝ)) ≤ Real.log (Real.log X) :=
            Real.log_le_log hlogfloor hlogle
        _ ≤ Real.log X - 1 :=
            Real.log_le_sub_one_of_pos (by linarith [hlogfloor, hlogle])
        _ ≤ Real.log X := by linarith
    have hmle : Sieve.mertensS ⌊X⌋₊ ≤ Real.log X + Sieve.mertensUpperConst := by
      linarith
    have hXpos : (0 : ℝ) < X ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hX0 _
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hmle hlog) hXpos.le

/-! ## The batch is the whole critical sum minus its prefix -/

/-- The prefix of the critical cosine sum below the window scale. -/
def prefixCosSum (Y X : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc 2 ⌊Y⌋₊,
    (if k.Prime then (k : ℝ) ^ (-(1 : ℝ) / 2) *
      Real.cos (terminalFrequency X * Real.log k) else 0)

theorem prefixCosSum_add_batchCosSum {Y X : ℝ} (h2 : 2 ≤ ⌊Y⌋₊) (hYX : ⌊Y⌋₊ ≤ ⌊X⌋₊) :
    prefixCosSum Y X + batchCosSum Y X = criticalCosSum X :=
  Finset.sum_Ioc_consecutive _ h2 hYX

/-- The prefix is dominated by the unsigned prefix mass. -/
theorem abs_prefixCosSum_le (Y X : ℝ) :
    |prefixCosSum Y X| ≤ primeWindowSumNoLog (1 / 2) 0 Y := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [primeWindowSumNoLog]
  refine Finset.sum_le_sum fun k hk => ?_
  by_cases hp : k.Prime
  · rw [if_pos hp, if_pos hp, pow_zero, mul_one, abs_mul]
    have hexp : ((1 : ℝ) / 2 - 1) = -(1 : ℝ) / 2 := by norm_num
    rw [hexp]
    have hk0 : (0 : ℝ) < (k : ℝ) := by
      rw [Finset.mem_Ioc] at hk
      have : 0 < k := by omega
      exact_mod_cast this
    have hrp : (0 : ℝ) < (k : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hk0 _
    rw [abs_of_pos hrp]
    nlinarith [Real.abs_cos_le_one (terminalFrequency X * Real.log k),
      abs_nonneg (Real.cos (terminalFrequency X * Real.log k))]
  · rw [if_neg hp, if_neg hp, abs_zero]

/-! ## The terminal batch rapidity -/

/-- **The batch rapidity at the terminal frequency.**  With the window scale
`Y = (log X)^A` the rapidity of the coherent batch obeys
`R(Y, X) = -4 √X / log X (1 + o(1))`: the `artanh` nonlinearity and the difference between the
critical half density `d_p` and `p^{-1/2}` contribute only a Mertens remainder, and the prefix
below `Y` is negligible. -/
theorem tendsto_batchRapidity {A : ℝ} (hA : 0 < A) :
    Tendsto (fun X : ℝ => batchRapidity (Real.log X ^ A) X * Real.log X / X ^ ((1 : ℝ) / 2))
      atTop (nhds (-4)) := by
  have hYtop : Tendsto (fun X : ℝ => Real.log X ^ A) atTop atTop :=
    (tendsto_rpow_atTop hA).comp Real.tendsto_log_atTop
  -- the prefix mass is below the window scale
  have hN0 : Tendsto (fun Y : ℝ => primeWindowSumNoLog (1 / 2) 0 Y / Y ^ ((1 : ℝ) / 2)) atTop
      (nhds 0) := tendsto_primeWindowSumNoLog (by norm_num) 0
  have hN0ev : ∀ᶠ Y : ℝ in atTop,
      primeWindowSumNoLog (1 / 2) 0 Y ≤ Y ^ ((1 : ℝ) / 2) := by
    have hlt := hN0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hlt, eventually_gt_atTop (0 : ℝ)] with Y hY hY0
    have hYpos : (0 : ℝ) < Y ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hY0 _
    exact le_of_lt ((div_lt_one hYpos).mp hY)
  -- the window scale is below `X`
  have hYleX : ∀ᶠ X : ℝ in atTop, Real.log X ^ A ≤ X := by
    have h := tendsto_logRpow_div_rpow (a := (1 : ℝ)) one_pos A
    have hlt := h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hlt, eventually_gt_atTop (0 : ℝ)] with X hX hX0
    have hXpos : (0 : ℝ) < X ^ (1 : ℝ) := Real.rpow_pos_of_pos hX0 _
    have hlt2 := (div_lt_one hXpos).mp hX
    rw [Real.rpow_one] at hlt2
    exact hlt2.le
  -- the majorant
  have hmaj : Tendsto (fun X : ℝ =>
      18 * (Sieve.mertensS ⌊X⌋₊ * Real.log X / X ^ ((1 : ℝ) / 2))
        + 2 * (Real.log X ^ (A / 2 + 1) / X ^ ((1 : ℝ) / 2))) atTop (nhds 0) := by
    have h1 := tendsto_mertensS_floor_mul_log_div_sqrt.const_mul (18 : ℝ)
    have h2 := (tendsto_logRpow_div_rpow (a := (1 : ℝ) / 2) (by norm_num)
      (A / 2 + 1)).const_mul (2 : ℝ)
    have h := h1.add h2
    rwa [mul_zero, mul_zero, add_zero] at h
  have hdiff : Tendsto (fun X : ℝ =>
      batchRapidity (Real.log X ^ A) X * Real.log X / X ^ ((1 : ℝ) / 2)
        - 2 * (criticalCosSum X * Real.log X / X ^ ((1 : ℝ) / 2))) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [hYtop.eventually hN0ev, hYtop.eventually_ge_atTop (16 : ℝ), hYleX,
      eventually_ge_atTop (3 : ℝ)] with X hprefix hY16 hYX hX3
    set Y : ℝ := Real.log X ^ A with hYdef
    have hX0 : (0 : ℝ) < X := by linarith
    have hlog : (1 : ℝ) ≤ Real.log X := by
      have hE : Real.exp 1 ≤ X := by
        have hd9 := Real.exp_one_lt_d9
        linarith
      have hle := Real.log_le_log (Real.exp_pos 1) hE
      rwa [Real.log_exp] at hle
    have hlog0 : (0 : ℝ) ≤ Real.log X := by linarith
    have hlogpos : (0 : ℝ) < Real.log X := by linarith
    have hD : (0 : ℝ) < X ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hX0 _
    have hfloorY : 16 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY16)
    have hfloorle : ⌊Y⌋₊ ≤ ⌊X⌋₊ := Nat.floor_le_floor hYX
    -- split the difference into the nonlinearity and the prefix
    have hsplit := prefixCosSum_add_batchCosSum (Y := Y) (X := X) (by omega) hfloorle
    have hrap := abs_batchRapidity_sub_two_mul_batchCosSum_le (Y := Y) (X := X)
      (by linarith) hYX
    have hpre := abs_prefixCosSum_le Y X
    have hkey : |batchRapidity Y X - 2 * criticalCosSum X|
        ≤ 18 * Sieve.mertensS ⌊X⌋₊ + 2 * primeWindowSumNoLog (1 / 2) 0 Y := by
      have hid : batchRapidity Y X - 2 * criticalCosSum X
          = (batchRapidity Y X - 2 * batchCosSum Y X) + (-2) * prefixCosSum Y X := by
        rw [← hsplit]
        ring
      rw [hid]
      calc |(batchRapidity Y X - 2 * batchCosSum Y X) + (-2) * prefixCosSum Y X|
          ≤ |batchRapidity Y X - 2 * batchCosSum Y X| + |(-2) * prefixCosSum Y X| :=
            abs_add_le _ _
        _ ≤ 18 * Sieve.mertensS ⌊X⌋₊ + 2 * primeWindowSumNoLog (1 / 2) 0 Y := by
            have habs : |(-2 : ℝ) * prefixCosSum Y X| = 2 * |prefixCosSum Y X| := by
              rw [abs_mul]
              norm_num
            rw [habs]
            linarith
    -- turn the prefix mass into a power of the logarithm
    have hYhalf : Y ^ ((1 : ℝ) / 2) = Real.log X ^ (A / 2) := by
      rw [hYdef, ← Real.rpow_mul hlog0]
      congr 1
      ring
    have hprod : Real.log X ^ (A / 2) * Real.log X = Real.log X ^ (A / 2 + 1) := by
      rw [Real.rpow_add hlogpos, Real.rpow_one]
    have hpref2 : primeWindowSumNoLog (1 / 2) 0 Y * Real.log X
        ≤ Real.log X ^ (A / 2 + 1) := by
      calc primeWindowSumNoLog (1 / 2) 0 Y * Real.log X
          ≤ Y ^ ((1 : ℝ) / 2) * Real.log X :=
            mul_le_mul_of_nonneg_right hprefix hlog0
        _ = Real.log X ^ (A / 2 + 1) := by rw [hYhalf, hprod]
    -- assemble
    have hrwmain : batchRapidity Y X * Real.log X / X ^ ((1 : ℝ) / 2)
        - 2 * (criticalCosSum X * Real.log X / X ^ ((1 : ℝ) / 2))
        = (batchRapidity Y X - 2 * criticalCosSum X) *
          (Real.log X / X ^ ((1 : ℝ) / 2)) := by
      field_simp
    rw [Real.norm_eq_abs, hrwmain, abs_mul,
      abs_of_nonneg (div_nonneg hlog0 hD.le)]
    have hfac : (0 : ℝ) ≤ Real.log X / X ^ ((1 : ℝ) / 2) := div_nonneg hlog0 hD.le
    have hstep := mul_le_mul_of_nonneg_right hkey hfac
    refine le_trans hstep ?_
    have hexpand : (18 * Sieve.mertensS ⌊X⌋₊ + 2 * primeWindowSumNoLog (1 / 2) 0 Y) *
        (Real.log X / X ^ ((1 : ℝ) / 2))
        = 18 * (Sieve.mertensS ⌊X⌋₊ * Real.log X / X ^ ((1 : ℝ) / 2))
          + 2 * (primeWindowSumNoLog (1 / 2) 0 Y * Real.log X / X ^ ((1 : ℝ) / 2)) := by
      field_simp
    rw [hexpand]
    have hfinal : primeWindowSumNoLog (1 / 2) 0 Y * Real.log X / X ^ ((1 : ℝ) / 2)
        ≤ Real.log X ^ (A / 2 + 1) / X ^ ((1 : ℝ) / 2) :=
      div_le_div_of_nonneg_right hpref2 hD.le
    linarith
  have hsum := hdiff.add (tendsto_criticalCosSum.const_mul (2 : ℝ))
  rw [zero_add, show (2 : ℝ) * (-2) = -4 by norm_num] at hsum
  exact hsum.congr fun X => by ring

end

end RHTower
