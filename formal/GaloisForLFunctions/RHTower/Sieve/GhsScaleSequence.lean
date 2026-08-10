import GaloisForLFunctions.RHTower.Sieve.GhsOuterBlockPoly

/-!
# The geometric scale sequence of the outer partition

`block_balance_le` needs a family of blocks whose width and whose complementary scale are
proportional.  An arithmetic family does not have that property; a family geometric *in the
logarithm* does.  The scales are

```text
ghsScale N k = ⌊N^{1/2^k}⌋ ,        log(ghsScale N k) ≈ (log N)/2^k ,
```

so consecutive scales differ by a factor two in the logarithm — exactly the ratio the balance
consumes — and the family is exhausted after `≍ log log N` steps rather than `≍ log N`.  That
count is what multiplies the per-block bound, so it is the difference between a `log log N` and a
`log N` in the final estimate.

The two bounds below are the only facts about the sequence the partition uses: the logarithm is at
most `(log N)/2^k`, and at least that minus `log 2` — the floor costs one `log 2`, once.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The `k`-th scale of the geometric partition of the outer prime range. -/
def ghsScale (N k : ℕ) : ℕ := ⌊(N : ℝ) ^ ((1 : ℝ) / 2 ^ k)⌋₊

/-- Past the threshold `2^k·log 2 ≤ log N` the `k`-th scale is at least two. -/
theorem two_le_rpow_of_scale {N k : ℕ} (hN : 1 ≤ N)
    (hk : (2 : ℝ) ^ k * Real.log 2 ≤ Real.log N) :
    (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 ^ k) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpow : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hlog : Real.log 2 ≤ (1 / 2 ^ k) * Real.log N := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpow]
    linarith [hk]
  have hrw : (N : ℝ) ^ ((1 : ℝ) / 2 ^ k) = Real.exp ((1 / 2 ^ k) * Real.log N) := by
    rw [Real.rpow_def_of_pos hN0]
    ring_nf
  rw [hrw]
  have h2 : Real.exp (Real.log 2) ≤ Real.exp ((1 / 2 ^ k) * Real.log N) :=
    Real.exp_le_exp.mpr hlog
  rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h2

/-- The scale is positive past the threshold. -/
theorem ghsScale_pos {N k : ℕ} (hN : 1 ≤ N) (hk : (2 : ℝ) ^ k * Real.log 2 ≤ Real.log N) :
    2 ≤ ghsScale N k := by
  rw [ghsScale]
  exact Nat.le_floor (by exact_mod_cast two_le_rpow_of_scale hN hk)

/-- **The scale's logarithm is at most `(log N)/2^k`.** -/
theorem log_ghsScale_le {N k : ℕ} (hN : 1 ≤ N)
    (hk : (2 : ℝ) ^ k * Real.log 2 ≤ Real.log N) :
    Real.log (ghsScale N k) ≤ Real.log N / 2 ^ k := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hy0 : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 2 ^ k) := Real.rpow_pos_of_pos hN0 _
  have hs2 : 2 ≤ ghsScale N k := ghsScale_pos hN hk
  have hs0 : (0 : ℝ) < (ghsScale N k : ℝ) := by
    have : (2 : ℝ) ≤ (ghsScale N k : ℝ) := by exact_mod_cast hs2
    linarith
  have hfloor : ((ghsScale N k : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 ^ k) := by
    rw [ghsScale]
    exact Nat.floor_le hy0.le
  have hle := Real.log_le_log hs0 hfloor
  rwa [Real.log_rpow hN0, show (1 : ℝ) / 2 ^ k * Real.log N = Real.log N / 2 ^ k by ring] at hle

/-- **The scale's logarithm is at least `(log N)/2^k − log 2`.**  The floor costs one `log 2`. -/
theorem le_log_ghsScale {N k : ℕ} (hN : 1 ≤ N)
    (hk : (2 : ℝ) ^ k * Real.log 2 ≤ Real.log N) :
    Real.log N / 2 ^ k - Real.log 2 ≤ Real.log (ghsScale N k) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hy0 : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 2 ^ k) := Real.rpow_pos_of_pos hN0 _
  have hy2 : (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 ^ k) := two_le_rpow_of_scale hN hk
  have hfl : (N : ℝ) ^ ((1 : ℝ) / 2 ^ k) - 1 < ((ghsScale N k : ℕ) : ℝ) := by
    rw [ghsScale]
    linarith [Nat.lt_floor_add_one ((N : ℝ) ^ ((1 : ℝ) / 2 ^ k))]
  have hhalf : (N : ℝ) ^ ((1 : ℝ) / 2 ^ k) / 2 ≤ ((ghsScale N k : ℕ) : ℝ) := by
    linarith [hfl, hy2]
  have hhalf0 : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 2 ^ k) / 2 := by positivity
  have hle := Real.log_le_log hhalf0 hhalf
  rw [Real.log_div (ne_of_gt hy0) (by norm_num), Real.log_rpow hN0,
    show (1 : ℝ) / 2 ^ k * Real.log N = Real.log N / 2 ^ k by ring] at hle
  linarith

/-- Consecutive scales are nested. -/
theorem ghsScale_antitone {N k : ℕ} (hN : 1 ≤ N) :
    ghsScale N (k + 1) ≤ ghsScale N k := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hexp : (1 : ℝ) / 2 ^ (k + 1) ≤ (1 : ℝ) / 2 ^ k := by
    have h1 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have h2 : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) := by
      rw [pow_succ]
      nlinarith [h1]
    exact one_div_le_one_div_of_le h1 h2
  have hrpow : (N : ℝ) ^ ((1 : ℝ) / 2 ^ (k + 1)) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 ^ k) :=
    Real.rpow_le_rpow_of_exponent_le hN1 hexp
  rw [ghsScale, ghsScale]
  exact Nat.floor_le_floor hrpow

end RHTower.Sieve

end

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The left endpoint of the `k`-th block of the outer prime range. -/
def ghsBlockLeft (N k : ℕ) : ℕ := N / ghsScale N k

/-- The right endpoint of the `k`-th block of the outer prime range. -/
def ghsBlockRight (N k : ℕ) : ℕ := N / ghsScale N (k + 1)

theorem ghsBlockLeft_le_right {N k : ℕ} (hN : 1 ≤ N)
    (hk1 : (2 : ℝ) ^ (k + 1) * Real.log 2 ≤ Real.log N) :
    ghsBlockLeft N k ≤ ghsBlockRight N k := by
  have h2 : 2 ≤ ghsScale N (k + 1) := ghsScale_pos hN hk1
  exact Nat.div_le_div_left (ghsScale_antitone hN) (by omega)

/-- The complementary scale of a floor quotient is at least the divisor. -/
theorem le_div_div {N D : ℕ} (hD : 1 ≤ D) (hND : D ≤ N) : D ≤ N / (N / D) := by
  have hm : 0 < N / D := Nat.div_pos hND hD
  rw [Nat.le_div_iff_mul_le hm]
  calc D * (N / D) = (N / D) * D := by ring
    _ ≤ N := Nat.div_mul_le_self N D

/-- A floor quotient plus one, times the divisor, exceeds the dividend. -/
theorem lt_div_add_one_mul {N D : ℕ} (hD : 0 < D) : N < (N / D + 1) * D := by
  rw [add_mul, one_mul]
  have h1 := Nat.div_add_mod N D
  have h2 : N % D < D := Nat.mod_lt _ hD
  nlinarith [h1, h2]

/-- The complementary scale of a floor quotient is less than twice the divisor. -/
theorem div_div_lt_two_mul {N D : ℕ} (hD : 1 ≤ D) (hND : 2 * D ≤ N) : N / (N / D) < 2 * D := by
  have hm : 0 < N / D := Nat.div_pos (by omega) hD
  rw [Nat.div_lt_iff_lt_mul hm]
  have hlt : N < (N / D + 1) * D := lt_div_add_one_mul (by omega)
  nlinarith [hlt, hm, hD, hND]

/-- **The `k`-th block is balanced.**  Its width and the whole inner range are both bounded by a
constant multiple of its own complementary scale, so `block_balance_le` applies with `κ = 2`,
`κ' = 3`. -/
theorem ghs_block_balanced {N k : ℕ} (hN : 1 ≤ N)
    (hk : (2 : ℝ) ^ (k + 1) * (4 * Real.log 2) ≤ Real.log N)
    (hDk : 2 * ghsScale N k ≤ N) :
    1 ≤ Real.log ((N / ghsBlockRight N k : ℕ) : ℝ)
    ∧ Real.log (ghsBlockRight N k) - Real.log (ghsBlockLeft N k)
        ≤ 2 * Real.log ((N / ghsBlockRight N k : ℕ) : ℝ)
    ∧ Real.log ((N / ghsBlockLeft N k : ℕ) : ℝ)
        ≤ 3 * Real.log ((N / ghsBlockRight N k : ℕ) : ℝ) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
  have hpowk : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hpowsucc : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have h2k : Real.log N / 2 ^ k = 2 * (Real.log N / 2 ^ (k + 1)) := by
    rw [hpowsucc]
    field_simp
  have hk1 : (2 : ℝ) ^ (k + 1) * Real.log 2 ≤ Real.log N := by nlinarith [hk, hlog2, hpow]
  have hkk : (2 : ℝ) ^ k * Real.log 2 ≤ Real.log N := by
    have hmono : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) := by
      rw [pow_succ]; nlinarith [hpowk]
    nlinarith [hk1, hmono, hlog2]
  -- the two scales
  have hDk1 : 2 ≤ ghsScale N (k + 1) := ghsScale_pos hN hk1
  have hDk2 : 2 ≤ ghsScale N k := ghsScale_pos hN hkk
  have hlow1 := le_log_ghsScale hN hk1
  have hup1 := log_ghsScale_le hN hk1
  have hupk := log_ghsScale_le hN hkk
  -- the scale of the block
  have hDkN : ghsScale N (k + 1) ≤ N := by
    have := ghsScale_antitone (N := N) (k := k) hN
    omega
  have hge : ghsScale N (k + 1) ≤ N / ghsBlockRight N k := by
    rw [ghsBlockRight]
    exact le_div_div (by omega) hDkN
  have hgeR : ((ghsScale N (k + 1) : ℕ) : ℝ) ≤ ((N / ghsBlockRight N k : ℕ) : ℝ) := by
    exact_mod_cast hge
  have hDk1R : (2 : ℝ) ≤ ((ghsScale N (k + 1) : ℕ) : ℝ) := by exact_mod_cast hDk1
  have hSlow : Real.log (ghsScale N (k + 1)) ≤ Real.log ((N / ghsBlockRight N k : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) hgeR
  -- the scale is large
  have hquart : 4 * Real.log 2 ≤ Real.log N / 2 ^ (k + 1) := by
    rw [le_div_iff₀ hpow]
    nlinarith [hk]
  have hS3 : 3 * Real.log 2 ≤ Real.log ((N / ghsBlockRight N k : ℕ) : ℝ) := by
    linarith [hSlow, hlow1, hquart]
  have hlog2gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hS1 : 1 ≤ Real.log ((N / ghsBlockRight N k : ℕ) : ℝ) := by linarith [hS3, hlog2gt]
  refine ⟨hS1, ?_, ?_⟩
  · -- the width
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hBle : ((ghsBlockRight N k : ℕ) : ℝ) ≤ (N : ℝ) / ((ghsScale N (k + 1) : ℕ) : ℝ) := by
      rw [ghsBlockRight]
      exact_mod_cast Nat.cast_div_le
    have hB0 : 0 < ghsBlockRight N k := by
      rw [ghsBlockRight]
      exact Nat.div_pos hDkN (by omega)
    have hB0R : (0 : ℝ) < ((ghsBlockRight N k : ℕ) : ℝ) := by exact_mod_cast hB0
    have hlogB : Real.log (ghsBlockRight N k) ≤ Real.log N - Real.log (ghsScale N (k + 1)) := by
      have h := Real.log_le_log hB0R hBle
      rwa [Real.log_div (ne_of_gt hNR) (by linarith)] at h
    -- the left endpoint is at least half the real quotient
    have hAhalf : (N : ℝ) / (2 * ((ghsScale N k : ℕ) : ℝ)) ≤ ((ghsBlockLeft N k : ℕ) : ℝ) := by
      have hDkR : (2 : ℝ) ≤ ((ghsScale N k : ℕ) : ℝ) := by exact_mod_cast hDk2
      have hfl : (N : ℝ) / ((ghsScale N k : ℕ) : ℝ) - 1 < ((ghsBlockLeft N k : ℕ) : ℝ) := by
        rw [ghsBlockLeft]
        have := lt_div_add_one_mul (N := N) (show 0 < ghsScale N k by omega)
        have hcast : (N : ℝ) < (((N / ghsScale N k : ℕ) : ℝ) + 1) * ((ghsScale N k : ℕ) : ℝ) := by
          exact_mod_cast this
        rw [sub_lt_iff_lt_add, div_lt_iff₀ (by linarith)]
        linarith [hcast]
      have hbig : (2 : ℝ) ≤ (N : ℝ) / ((ghsScale N k : ℕ) : ℝ) := by
        rw [le_div_iff₀ (by linarith)]
        have : (2 : ℝ) * ((ghsScale N k : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hDk
        linarith
      have hdiv : (N : ℝ) / (2 * ((ghsScale N k : ℕ) : ℝ))
          = ((N : ℝ) / ((ghsScale N k : ℕ) : ℝ)) / 2 := by
        field_simp
      rw [hdiv]
      linarith [hfl, hbig]
    have hA0 : (0 : ℝ) < (N : ℝ) / (2 * ((ghsScale N k : ℕ) : ℝ)) := by
      have hDkR : (2 : ℝ) ≤ ((ghsScale N k : ℕ) : ℝ) := by exact_mod_cast hDk2
      positivity
    have hlogA : Real.log N - Real.log (ghsScale N k) - Real.log 2
        ≤ Real.log (ghsBlockLeft N k) := by
      have h := Real.log_le_log hA0 hAhalf
      have hDkR : (2 : ℝ) ≤ ((ghsScale N k : ℕ) : ℝ) := by exact_mod_cast hDk2
      rw [Real.log_div (ne_of_gt hNR) (by positivity),
        Real.log_mul (by norm_num) (by linarith)] at h
      linarith
    linarith [hlogB, hlogA, hupk, hlow1, hSlow, hS3, h2k]
  · -- the inner range
    have hDkR : (2 : ℝ) ≤ ((ghsScale N k : ℕ) : ℝ) := by exact_mod_cast hDk2
    have hup : N / ghsBlockLeft N k < 2 * ghsScale N k := by
      rw [ghsBlockLeft]
      exact div_div_lt_two_mul (by omega) hDk
    have hupR : ((N / ghsBlockLeft N k : ℕ) : ℝ) ≤ 2 * ((ghsScale N k : ℕ) : ℝ) := by
      have : ((N / ghsBlockLeft N k : ℕ) : ℝ) < 2 * ((ghsScale N k : ℕ) : ℝ) := by
        exact_mod_cast hup
      linarith
    have hUpos : (0 : ℝ) < 2 * ((ghsScale N k : ℕ) : ℝ) := by linarith
    have hlogU : Real.log ((N / ghsBlockLeft N k : ℕ) : ℝ)
        ≤ Real.log 2 + Real.log (ghsScale N k) := by
      rcases Nat.eq_zero_or_pos (N / ghsBlockLeft N k) with hz | hz
      · rw [hz]
        simp only [Nat.cast_zero, Real.log_zero]
        have : (0 : ℝ) ≤ Real.log (ghsScale N k) := Real.log_nonneg (by linarith)
        linarith
      · have hz0 : (0 : ℝ) < ((N / ghsBlockLeft N k : ℕ) : ℝ) := by exact_mod_cast hz
        have h := Real.log_le_log hz0 hupR
        rwa [Real.log_mul (by norm_num) (by linarith)] at h
    linarith [hlogU, hupk, hlow1, hSlow, hS3, hquart, h2k]

end RHTower.Sieve

end
