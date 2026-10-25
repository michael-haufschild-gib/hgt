import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheDiniThresholdOfTheHarmonicDefectIsOne
import GaloisForLFunctions.TransHorizonIncidenceMechanics.MultiFrequencyPrimePatternsAndGeneralMultiplicativeSpectra
import GaloisForLFunctions.RHTower.Sieve.AlmostPrimeGlobalCount

/-!
# The Dini threshold of the log-log amplitude is one

For `0 ≤ c ≤ 2` and `t₀ > 0` let `f_c(p) = (1 − c/ℓ(p)) cos(t₀ log p)` with
`ℓ(p) = max(1, log log p)` (`logLogPattern`). Then

`f_c(d) d^{-1/2}` is paid  ⟺  `c > 1` or `ζ(1/2 + it₀) = 0`  (`receiverBounded_logLogPattern_iff`),

while the critical-line mass `Σ_p |f_c(p) − cos(t₀ log p)|/p` is infinite at every `c > 0`
(`not_summable_criticalLineMass_logLog`).

* **The harmonic defect is `1/log log` to second order** (`abs_cmDefect_harmonic_sub_le`): in the
  variable `y = log log x`, `g(x) = Σ_k exp(−e^{y−k−1})/((k+1)(k+2))` smooths the step `1/(k+1)` at
  `k ≈ y` by a Gumbel profile, so `|g(x) − 1/y| ≤ 3600/y²`.
* **`Σ_p 1/(p ℓ(p)²) < ∞`** (`summable_inv_mul_logLogFloor_sq`), by Abel summation against Mertens'
  bound `Σ_{p ≤ N} 1/p ≤ log log N + O(1)`.

So `f_c` differs from the harmonic defect pattern by a summable critical-line mass, and inherits its
Dini threshold.
-/

open Filter Topology MeasureTheory Complex Set
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Elementary bounds -/

/-- `e^{-x} ≤ 4/x²` for `x > 0`. -/
theorem exp_neg_le_four_div_sq {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 4 / x ^ 2 := by
  have h1 := Real.add_one_le_exp (x / 2)
  have hsq : Real.exp x = Real.exp (x / 2) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hge : x ^ 2 / 4 ≤ Real.exp x := by
    rw [hsq]; nlinarith [mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ x / 2 + 1) h1]
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos x) (by positivity)]
  nlinarith

/-- `Σ_{k<n} 1/(k+1)² ≤ 2 − 2/(n+1)`. -/
theorem sum_range_inv_succ_sq_le (n : ℕ) :
    ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) ^ 2 ≤ 2 - 2 / ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h : 1 / ((n : ℝ) + 1) ^ 2 ≤ 2 / ((n : ℝ) + 1) - 2 / ((n : ℝ) + 1 + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    push_cast
    linarith

/-- A discrete convolution: `Σ_{k<K} 1/((k+1)²(K−k)²) ≤ 16/(K+1)²`. -/
theorem sum_range_inv_sq_mul_inv_sq_le (K : ℕ) :
    ∑ k ∈ Finset.range K, 1 / (((k : ℝ) + 1) ^ 2 * ((K : ℝ) - k) ^ 2) ≤
      16 / ((K : ℝ) + 1) ^ 2 := by
  have hpt : ∀ k ∈ Finset.range K, 1 / (((k : ℝ) + 1) ^ 2 * ((K : ℝ) - k) ^ 2) ≤
      4 / ((K : ℝ) + 1) ^ 2 * (1 / ((k : ℝ) + 1) ^ 2 + 1 / ((K : ℝ) - k) ^ 2) := by
    intro k hk
    have hkK : (k : ℝ) + 1 ≤ K := by exact_mod_cast Finset.mem_range.mp hk
    set a : ℝ := (k : ℝ) + 1
    set b : ℝ := (K : ℝ) - k
    have ha : 0 < a := by positivity
    have hb : 0 < b := by simp only [b, a] at hkK ⊢; linarith
    have hab : a + b = (K : ℝ) + 1 := by simp only [a, b]; ring
    have ha' : a ≠ 0 := ha.ne'
    have hb' : b ≠ 0 := hb.ne'
    have hab' : a + b ≠ 0 := by positivity
    rw [← hab]
    have key : (a + b) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
    calc 1 / (a ^ 2 * b ^ 2) = (a + b) ^ 2 / ((a + b) ^ 2 * (a ^ 2 * b ^ 2)) := by
          field_simp
      _ ≤ 4 * (a ^ 2 + b ^ 2) / ((a + b) ^ 2 * (a ^ 2 * b ^ 2)) :=
          div_le_div_of_nonneg_right key (by positivity)
      _ = 4 / (a + b) ^ 2 * (1 / a ^ 2 + 1 / b ^ 2) := by field_simp; ring
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have h1 := sum_range_inv_succ_sq_le K
  have h2 : ∑ k ∈ Finset.range K, 1 / ((K : ℝ) - k) ^ 2 =
      ∑ k ∈ Finset.range K, 1 / ((k : ℝ) + 1) ^ 2 := by
    rw [← Finset.sum_range_reflect (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) K]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [show ((K - 1 - k : ℕ) : ℝ) = (K : ℝ) - 1 - k by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring]
    congr 2; ring
  rw [h2]
  have hK : 0 < 4 / ((K : ℝ) + 1) ^ 2 := by positivity
  have h3 : 0 ≤ 2 / ((K : ℝ) + 1) := by positivity
  calc 4 / ((K : ℝ) + 1) ^ 2 * (∑ k ∈ Finset.range K, 1 / ((k : ℝ) + 1) ^ 2 +
        ∑ k ∈ Finset.range K, 1 / ((k : ℝ) + 1) ^ 2)
      ≤ 4 / ((K : ℝ) + 1) ^ 2 * (2 + 2) := mul_le_mul_of_nonneg_left (by linarith) hK.le
    _ = 16 / ((K : ℝ) + 1) ^ 2 := by ring

theorem exp_four_lt : Real.exp 4 < 55 := by
  have h := Real.exp_one_lt_d9
  have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h4]
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  calc Real.exp 1 ^ 4 < (2.7182818286 : ℝ) ^ 4 := pow_lt_pow_left₀ h h0.le (by norm_num)
    _ < 55 := by norm_num

/-! ### The harmonic defect is `1/log log` to second order -/

/-- The partial sums of the shifted harmonic weights converge: `Σ_{k ≥ K} w_k = 1/(K+1)`. -/
theorem hasSum_harmonicWeight_add (K : ℕ) :
    HasSum (fun k => harmonicWeight (k + K)) (1 / ((K : ℝ) + 1)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => harmonicWeight_nonneg _)]
  simp_rw [sum_range_harmonicWeight_add K]
  have hlim : Tendsto (fun n : ℕ => 1 / ((K : ℝ) + n + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1
      (tendsto_atTop_add_const_left atTop (K : ℝ) tendsto_natCast_atTop_atTop))
  simpa using tendsto_const_nhds.sub hlim

/-- **The harmonic defect is `1/log log` to second order.** For `x ≥ e^e`,
`|g(x) − 1/log log x| ≤ 3600/(log log x)²`. With `y = log log x` and `K = ⌈y⌉`, the terms
`k < K` are killed by `exp(−e^{y−k−1}) ≤ 4e⁴/(K−k)²`, the terms `k ≥ K` differ from the step
`Σ_{k ≥ K} w_k = 1/(K+1)` by at most `1/(K+1)²`, and `|1/(K+1) − 1/y| ≤ 2/y²`. -/
theorem abs_cmDefect_harmonic_sub_le {x : ℝ} (hx : Real.exp (Real.exp 1) ≤ x) :
    |cmDefect harmonicWeight harmonicShift x - 1 / Real.log (Real.log x)| ≤
      3600 / Real.log (Real.log x) ^ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp (Real.exp_pos 1).le) hx
  set L := Real.log x
  have hL : Real.exp 1 ≤ L := by
    have := Real.log_le_log (Real.exp_pos _) hx; rwa [Real.log_exp] at this
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hL
  set y := Real.log L
  have hy1 : 1 ≤ y := by
    have := Real.log_le_log (Real.exp_pos 1) hL; rwa [Real.log_exp] at this
  have hy0 : 0 < y := by linarith
  have hLy : L = Real.exp y := (Real.exp_log hL0).symm
  set K := ⌈y⌉₊
  have hyK : y ≤ K := Nat.le_ceil y
  have hKy : (K : ℝ) < y + 1 := Nat.ceil_lt_add_one (by linarith)
  set φ : ℕ → ℝ := fun k => Real.exp (-Real.exp (y - ((k : ℝ) + 1)))
  have hφ0 : ∀ k, 0 ≤ φ k := fun k => (Real.exp_pos _).le
  have hφ1 : ∀ k, φ k ≤ 1 := fun k =>
    Real.exp_le_one_iff.mpr (by linarith [Real.exp_pos (y - ((k : ℝ) + 1))])
  have hterm : ∀ k, harmonicWeight k * x ^ (-harmonicShift k) = harmonicWeight k * φ k :=
    fun k => by
      rw [Real.rpow_def_of_pos hx0, harmonicShift]
      simp only [φ]
      congr 2
      rw [show y - ((k : ℝ) + 1) = y + -((k : ℝ) + 1) by ring, Real.exp_add, ← hLy]
      ring
  have hd := admissibleDefect_harmonic
  have hs : Summable fun k => harmonicWeight k * φ k :=
    (hd.summable_mul_rpow hx1).congr hterm
  have hg : cmDefect harmonicWeight harmonicShift x = ∑' k, harmonicWeight k * φ k :=
    tsum_congr hterm
  -- the head `k < K`
  have hhead : ∑ k ∈ Finset.range K, harmonicWeight k * φ k ≤
      64 * Real.exp 4 / ((K : ℝ) + 1) ^ 2 := by
    have hpt : ∀ k ∈ Finset.range K, harmonicWeight k * φ k ≤
        4 * Real.exp 4 * (1 / (((k : ℝ) + 1) ^ 2 * ((K : ℝ) - k) ^ 2)) := by
      intro k hk
      have hkK : (k : ℝ) + 1 ≤ K := by exact_mod_cast Finset.mem_range.mp hk
      have hw : harmonicWeight k ≤ 1 / ((k : ℝ) + 1) ^ 2 := by
        unfold harmonicWeight
        exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
      have hφk : φ k ≤ 4 * Real.exp 4 / ((K : ℝ) - k) ^ 2 := by
        set z := y - ((k : ℝ) + 1)
        have hz : (K : ℝ) - k - 2 < z := by simp only [z]; linarith
        have hKk : 0 < (K : ℝ) - k := by linarith
        have h1 : φ k ≤ 4 / Real.exp z ^ 2 := exp_neg_le_four_div_sq (Real.exp_pos z)
        have h2 : Real.exp z ^ 2 = Real.exp (2 * z) := by rw [sq, ← Real.exp_add]; ring_nf
        have h3 : ((K : ℝ) - k) ^ 2 ≤ Real.exp (2 * ((K : ℝ) - k)) := by
          have h6 := Real.add_one_le_exp ((K : ℝ) - k)
          have h4 : Real.exp (2 * ((K : ℝ) - k)) = Real.exp ((K : ℝ) - k) ^ 2 := by
            rw [sq, ← Real.exp_add]; ring_nf
          rw [h4]; nlinarith
        have h5 : Real.exp (2 * ((K : ℝ) - k)) * Real.exp (-4) ≤ Real.exp (2 * z) := by
          rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
        rw [h2] at h1
        calc φ k ≤ 4 / Real.exp (2 * z) := h1
          _ ≤ 4 / (Real.exp (2 * ((K : ℝ) - k)) * Real.exp (-4)) :=
              div_le_div_of_nonneg_left (by norm_num) (by positivity) h5
          _ ≤ 4 / (((K : ℝ) - k) ^ 2 * Real.exp (-4)) :=
              div_le_div_of_nonneg_left (by norm_num) (by positivity)
                (mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le)
          _ = 4 * Real.exp 4 / ((K : ℝ) - k) ^ 2 := by
              rw [Real.exp_neg, div_mul_eq_div_div, div_inv_eq_mul]; ring
      calc harmonicWeight k * φ k
          ≤ 1 / ((k : ℝ) + 1) ^ 2 * (4 * Real.exp 4 / ((K : ℝ) - k) ^ 2) :=
            mul_le_mul hw hφk (hφ0 k) (by positivity)
        _ = 4 * Real.exp 4 * (1 / (((k : ℝ) + 1) ^ 2 * ((K : ℝ) - k) ^ 2)) := by
            rw [div_mul_div_comm, one_mul, mul_one_div]
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum]
    calc _ ≤ 4 * Real.exp 4 * (16 / ((K : ℝ) + 1) ^ 2) :=
          mul_le_mul_of_nonneg_left (sum_range_inv_sq_mul_inv_sq_le K) (by positivity)
      _ = 64 * Real.exp 4 / ((K : ℝ) + 1) ^ 2 := by ring
  -- the tail `k ≥ K` against the step
  have hT := hasSum_harmonicWeight_add K
  have hwK : Summable fun k => harmonicWeight (k + K) := hT.summable
  have hsK : Summable fun k => harmonicWeight (k + K) * φ (k + K) :=
    hs.comp_injective (add_left_injective K)
  have h1φ : ∀ k, 1 - φ (k + K) ≤ (1 / 2) ^ k * (1 / 2) := fun k => by
    have hz : Real.exp (y - (((k + K : ℕ) : ℝ) + 1)) ≤ Real.exp (-((k : ℝ) + 1)) :=
      Real.exp_le_exp.mpr (by push_cast; linarith)
    have hexp : Real.exp (-((k : ℝ) + 1)) ≤ (1 / 2) ^ k * (1 / 2) := by
      rw [show -((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) * (-1) by push_cast; ring, Real.exp_nat_mul,
        ← pow_succ]
      exact pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_neg_one_lt_half.le _
    have := Real.add_one_le_exp (-Real.exp (y - (((k + K : ℕ) : ℝ) + 1)))
    simp only [φ]; linarith
  have hgeo : Summable fun k : ℕ => 1 / ((K : ℝ) + 1) ^ 2 * ((1 / 2) ^ k * (1 / 2)) :=
    ((summable_geometric_two.mul_right (1 / 2))).mul_left _
  have hgeo_val : ∑' k : ℕ, 1 / ((K : ℝ) + 1) ^ 2 * ((1 / 2) ^ k * (1 / 2)) =
      1 / ((K : ℝ) + 1) ^ 2 := by
    rw [tsum_mul_left, tsum_mul_right, tsum_geometric_two]; ring
  have htail : 0 ≤ ∑' k, harmonicWeight (k + K) - ∑' k, harmonicWeight (k + K) * φ (k + K) ∧
      ∑' k, harmonicWeight (k + K) - ∑' k, harmonicWeight (k + K) * φ (k + K) ≤
        1 / ((K : ℝ) + 1) ^ 2 := by
    rw [← hwK.tsum_sub hsK]
    constructor
    · exact tsum_nonneg fun k => by
        rw [← mul_one_sub]; exact mul_nonneg (harmonicWeight_nonneg _) (by linarith [hφ1 (k + K)])
    · refine ((hwK.sub hsK).tsum_le_tsum (fun k => ?_) hgeo).trans (le_of_eq hgeo_val)
      have hwk : harmonicWeight (k + K) ≤ 1 / ((K : ℝ) + 1) ^ 2 := by
        unfold harmonicWeight
        exact one_div_le_one_div_of_le (by positivity) (by push_cast; nlinarith)
      rw [← mul_one_sub]
      exact mul_le_mul hwk (h1φ k) (by linarith [hφ1 (k + K)]) (by positivity)
  -- assembly
  rw [hg, ← hs.sum_add_tsum_nat_add K]
  rw [hT.tsum_eq] at htail
  set head := ∑ k ∈ Finset.range K, harmonicWeight k * φ k
  set tl := ∑' k, harmonicWeight (k + K) * φ (k + K)
  have hhead0 : 0 ≤ head := Finset.sum_nonneg fun k _ => mul_nonneg (harmonicWeight_nonneg k) (hφ0 k)
  set D := 1 / y ^ 2
  have hD : 0 ≤ D := by positivity
  have hK1 : y ≤ (K : ℝ) + 1 := by linarith
  have hKD : 1 / ((K : ℝ) + 1) ^ 2 ≤ D :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hy0.le hK1 2)
  have hheadD : head ≤ 64 * Real.exp 4 * D := by
    refine hhead.trans ?_
    calc 64 * Real.exp 4 / ((K : ℝ) + 1) ^ 2 = 64 * Real.exp 4 * (1 / ((K : ℝ) + 1) ^ 2) := by
          ring
      _ ≤ 64 * Real.exp 4 * D := mul_le_mul_of_nonneg_left hKD (by positivity)
  have hy2 : 0 ≤ 1 / y - 1 / ((K : ℝ) + 1) ∧ 1 / y - 1 / ((K : ℝ) + 1) ≤ 2 * D := by
    have he : 1 / y - 1 / ((K : ℝ) + 1) = ((K : ℝ) + 1 - y) / (y * ((K : ℝ) + 1)) := by
      rw [div_sub_div _ _ hy0.ne' (by positivity : ((K : ℝ) + 1) ≠ 0)]; ring
    rw [he]
    constructor
    · exact div_nonneg (by linarith) (by positivity)
    · rw [div_le_iff₀ (by positivity)]
      simp only [D]
      have hrw : 2 * (1 / y ^ 2) * (y * ((K : ℝ) + 1)) = 2 * (((K : ℝ) + 1) / y) := by
        field_simp
      rw [hrw]
      have : 1 ≤ ((K : ℝ) + 1) / y := by rw [le_div_iff₀ hy0]; linarith
      nlinarith
  have he4 := exp_four_lt
  rw [show 3600 / y ^ 2 = 3600 * D by simp only [D]; ring, abs_le]
  have hED := mul_le_mul_of_nonneg_right he4.le hD
  constructor <;> linarith [htail.1, htail.2, hy2.1, hy2.2, hKD, hheadD, hhead0]

/-! ### The log-log floor and its Abel summation -/

/-- `ℓ(n) = max(1, log log n)`. -/
def logLogFloor (n : ℕ) : ℝ := max 1 (Real.log (Real.log n))

theorem one_le_logLogFloor (n : ℕ) : 1 ≤ logLogFloor n := le_max_left _ _

theorem logLogFloor_mono {m n : ℕ} (h : m ≤ n) : logLogFloor m ≤ logLogFloor n := by
  unfold logLogFloor
  rcases le_or_gt (Real.log (Real.log m)) 1 with h1 | h1
  · exact max_le (le_max_left _ _) (h1.trans (le_max_left _ _))
  · have hm2 : 2 ≤ m := by
      by_contra hc
      have hc' := not_le.mp hc
      interval_cases m <;> simp at h1 <;> linarith
    have hm : 0 < Real.log m := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
    have hmn : Real.log m ≤ Real.log n :=
      Real.log_le_log (by exact_mod_cast (show 0 < m by omega)) (by exact_mod_cast h)
    exact max_le_max le_rfl (Real.log_le_log hm hmn)

/-- The prime indicator weight `P(n) = 1_{n prime}/n`. -/
def primeRecipTerm (n : ℕ) : ℝ := if n.Prime then 1 / (n : ℝ) else 0

theorem primeRecipTerm_nonneg (n : ℕ) : 0 ≤ primeRecipTerm n := by
  unfold primeRecipTerm; split_ifs <;> positivity

theorem sum_range_primeRecipTerm (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), primeRecipTerm n = RHTower.Sieve.mertensS N := by
  rw [RHTower.Sieve.mertensS, Nat.primesLE_eq_filter_range, Finset.sum_filter]
  rfl

/-- **Abel summation**: `Σ_{n ≤ N} a_n P_n = a_N S_N + Σ_{n < N} (a_n − a_{n+1}) S_n`,
`S_n = Σ_{m ≤ n} P_m`. -/
theorem sum_range_mul_eq_abel (a P : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), a n * P n =
      a N * ∑ m ∈ Finset.range (N + 1), P m +
        ∑ n ∈ Finset.range N, (a n - a (n + 1)) * ∑ m ∈ Finset.range (n + 1), P m := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih,
      Finset.sum_range_succ (fun n => (a n - a (n + 1)) * ∑ m ∈ Finset.range (n + 1), P m) N,
      Finset.sum_range_succ P (N + 1)]
    ring

/-- `(1/u² − 1/v²) u ≤ 2(1/u − 1/v)` for `1 ≤ u ≤ v`. -/
theorem inv_sq_sub_inv_sq_mul_le {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) :
    (1 / u ^ 2 - 1 / v ^ 2) * u ≤ 2 * (1 / u - 1 / v) := by
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have hu' : u ≠ 0 := hu0.ne'
  have hv' : v ≠ 0 := hv0.ne'
  have key : 2 * (1 / u - 1 / v) - (1 / u ^ 2 - 1 / v ^ 2) * u = (v - u) ^ 2 / (u * v ^ 2) := by
    field_simp
    ring
  have : 0 ≤ (v - u) ^ 2 / (u * v ^ 2) := by positivity
  linarith

/-- **`Σ_p 1/(p ℓ(p)²) < ∞`**: by Abel summation against `Σ_{p ≤ N} 1/p ≤ ℓ(N) + C`, the sum is
at most `a_N(ℓ_N + C) + Σ_n (a_n − a_{n+1})(ℓ_n + C)`, and `(a_n − a_{n+1}) ℓ_n` telescopes. -/
theorem summable_inv_mul_logLogFloor_sq :
    Summable fun n : ℕ => primeRecipTerm n / logLogFloor n ^ 2 := by
  set C : ℝ := max 0 RHTower.Sieve.mertensUpperConst
  have hC : 0 ≤ C := le_max_left _ _
  set a : ℕ → ℝ := fun n => 1 / logLogFloor n ^ 2
  have hℓ1 := one_le_logLogFloor
  have ha0 : ∀ n, 0 ≤ a n := fun n => by simp only [a]; positivity
  have hamono : ∀ n, a (n + 1) ≤ a n := fun n => by
    simp only [a]
    exact one_div_le_one_div_of_le (by have := hℓ1 n; positivity)
      (pow_le_pow_left₀ (by linarith [hℓ1 n]) (logLogFloor_mono (Nat.le_succ n)) 2)
  have hS : ∀ n, ∑ m ∈ Finset.range (n + 1), primeRecipTerm m ≤ logLogFloor n + C := fun n => by
    rw [sum_range_primeRecipTerm]
    rcases lt_or_ge n 2 with hn | hn
    · have : RHTower.Sieve.mertensS n = 0 := by
        rw [RHTower.Sieve.mertensS]
        refine Finset.sum_eq_zero fun p hp => ?_
        obtain ⟨h1, h2⟩ := Nat.mem_primesLE.mp hp
        exact absurd h2.two_le (by omega)
      rw [this]; linarith [hℓ1 n]
    · have h := RHTower.Sieve.mertensS_le_logLog_add hn
      have h2 : RHTower.Sieve.logLog n ≤ logLogFloor n := le_max_right _ _
      have h3 : RHTower.Sieve.mertensUpperConst ≤ C := le_max_right _ _
      linarith
  have hbound : ∀ N, ∑ n ∈ Finset.range (N + 1), primeRecipTerm n / logLogFloor n ^ 2 ≤
      3 + 2 * C := by
    intro N
    have habel := sum_range_mul_eq_abel a primeRecipTerm N
    have hrw : ∑ n ∈ Finset.range (N + 1), primeRecipTerm n / logLogFloor n ^ 2 =
        ∑ n ∈ Finset.range (N + 1), a n * primeRecipTerm n :=
      Finset.sum_congr rfl fun n _ => by simp only [a]; ring
    rw [hrw, habel]
    -- the boundary term
    have hb1 : a N * ∑ m ∈ Finset.range (N + 1), primeRecipTerm m ≤ 1 + C := by
      have hl := hℓ1 N
      calc a N * ∑ m ∈ Finset.range (N + 1), primeRecipTerm m ≤ a N * (logLogFloor N + C) :=
            mul_le_mul_of_nonneg_left (hS N) (ha0 N)
        _ = (logLogFloor N + C) / logLogFloor N ^ 2 := by simp only [a]; ring
        _ ≤ 1 + C := by
            rw [div_le_iff₀ (by positivity)]
            nlinarith [mul_le_mul hl hl zero_le_one (by linarith),
              mul_nonneg hC (by nlinarith : (0 : ℝ) ≤ logLogFloor N ^ 2 - 1)]
    -- the interior terms
    have hb2 : ∑ n ∈ Finset.range N, (a n - a (n + 1)) *
        ∑ m ∈ Finset.range (n + 1), primeRecipTerm m ≤ 2 + C := by
      calc ∑ n ∈ Finset.range N, (a n - a (n + 1)) * ∑ m ∈ Finset.range (n + 1), primeRecipTerm m
          ≤ ∑ n ∈ Finset.range N, ((a n - a (n + 1)) * logLogFloor n + C * (a n - a (n + 1))) :=
            Finset.sum_le_sum fun n _ => by
              have := mul_le_mul_of_nonneg_left (hS n) (sub_nonneg.mpr (hamono n))
              linarith
        _ ≤ ∑ n ∈ Finset.range N, (2 * (1 / logLogFloor n - 1 / logLogFloor (n + 1)) +
              C * (a n - a (n + 1))) :=
            Finset.sum_le_sum fun n _ => by
              have := inv_sq_sub_inv_sq_mul_le (hℓ1 n) (logLogFloor_mono (Nat.le_succ n))
              simp only [a]; linarith
        _ = 2 * (1 / logLogFloor 0 - 1 / logLogFloor N) + C * (a 0 - a N) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
              Finset.sum_range_sub' (fun n => 1 / logLogFloor n),
              Finset.sum_range_sub' a]
        _ ≤ 2 + C := by
            have h0 : 1 / logLogFloor 0 ≤ 1 := by
              rw [div_le_one (by linarith [hℓ1 0])]; exact hℓ1 0
            have hN : 0 ≤ 1 / logLogFloor N := by have := hℓ1 N; positivity
            have ha00 : a 0 ≤ 1 := by
              simp only [a]; rw [div_le_one (by have := hℓ1 0; positivity)]; nlinarith [hℓ1 0]
            nlinarith [ha0 N]
    linarith
  refine summable_of_sum_range_le (c := 3 + 2 * C) (fun n =>
    div_nonneg (primeRecipTerm_nonneg n) (by have := hℓ1 n; positivity)) fun M => ?_
  rcases M with _ | N
  · simp only [Finset.range_zero, Finset.sum_empty]; linarith
  · exact hbound N

/-! ### The log-log pattern -/

/-- The log-log amplitude pattern `f_c(p) = (1 − c/ℓ(p)) cos(t₀ log p)`. -/
def logLogPattern (c t₀ : ℝ) : ℕ →*₀ ℝ :=
  primeValueHom fun p => (1 - c / logLogFloor p) * Real.cos (t₀ * Real.log p)

theorem logLogPattern_prime (c t₀ : ℝ) {p : ℕ} (hp : p.Prime) :
    logLogPattern c t₀ p = (1 - c / logLogFloor p) * Real.cos (t₀ * Real.log p) :=
  primeValueHom_prime _ hp

theorem abs_logLogPattern_prime_le {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 2) (t₀ : ℝ) {p : ℕ}
    (hp : p.Prime) : |logLogPattern c t₀ p| ≤ 1 := by
  rw [logLogPattern_prime c t₀ hp, abs_mul]
  have hl := one_le_logLogFloor p
  have h0 : 0 ≤ c / logLogFloor p := div_nonneg hc (by linarith)
  have h1 : c / logLogFloor p ≤ c := div_le_self hc hl
  refine mul_le_one₀ ?_ (abs_nonneg _) (Real.abs_cos_le_one _)
  rw [abs_le]; constructor <;> linarith

/-- `|g(p) − 1/ℓ(p)| ≤ 3600/ℓ(p)²` at every natural number `p ≥ 1`. -/
theorem abs_cmDefect_harmonic_sub_inv_logLogFloor_le {n : ℕ} (hn : 1 ≤ n) :
    |cmDefect harmonicWeight harmonicShift n - 1 / logLogFloor n| ≤
      3600 / logLogFloor n ^ 2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rcases le_or_gt (Real.exp (Real.exp 1)) (n : ℝ) with h | h
  · have hll : 1 ≤ Real.log (Real.log n) := by
      have h1 := Real.log_le_log (Real.exp_pos _) h
      rw [Real.log_exp] at h1
      have h2 := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at h2
    have hfl : logLogFloor n = Real.log (Real.log n) := max_eq_right hll
    rw [hfl]
    exact abs_cmDefect_harmonic_sub_le h
  · have hll : Real.log (Real.log n) ≤ 1 := by
      have hlogn : Real.log n < Real.exp 1 := by
        rw [Real.log_lt_iff_lt_exp (by linarith)]; exact h
      rcases eq_or_lt_of_le (Real.log_nonneg hn1) with h0 | h0
      · rw [← h0, Real.log_zero]; norm_num
      · have := Real.log_lt_log h0 hlogn
        rw [Real.log_exp] at this; linarith
    have hfl : logLogFloor n = 1 := max_eq_left hll
    rw [hfl]
    have hd := admissibleDefect_harmonic
    have g0 := cmDefect_nonneg hd hn1
    have g1 := (cmDefect_le hd hn1).trans tsum_harmonicWeight_le
    rw [abs_le]; constructor <;> norm_num <;> linarith

/-- **The log-log pattern and the harmonic defect pattern differ by a summable critical-line
mass.** -/
theorem summable_logLogPattern_sub_defectPattern {c : ℝ} (hc : 0 ≤ c) (t₀ : ℝ) :
    Summable (fun p : ℕ => if p.Prime then
      |logLogPattern c t₀ p - defectPattern c t₀ harmonicWeight harmonicShift p| *
        (p : ℝ) ^ (-(1 / 2 + 1 / 2 : ℝ)) else 0) := by
  refine (summable_inv_mul_logLogFloor_sq.mul_left (3600 * c)).of_nonneg_of_le
    (fun p => by split_ifs <;> positivity) fun p => ?_
  split_ifs with hp
  · have hp1 : 1 ≤ p := hp.one_lt.le
    rw [logLogPattern_prime c t₀ hp, defectPattern_prime c t₀ hp,
      show (1 - c / logLogFloor p) * Real.cos (t₀ * Real.log p) -
          (1 - c * cmDefect harmonicWeight harmonicShift p) * Real.cos (t₀ * Real.log p) =
        c * (cmDefect harmonicWeight harmonicShift p - 1 / logLogFloor p) *
          Real.cos (t₀ * Real.log p) by ring,
      abs_mul, abs_mul, abs_of_nonneg hc,
      show (-(1 / 2 + 1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
    have hA := abs_cmDefect_harmonic_sub_inv_logLogFloor_le hp1
    have hcos := Real.abs_cos_le_one (t₀ * Real.log p)
    have hpinv : 0 ≤ (p : ℝ)⁻¹ := by positivity
    simp only [primeRecipTerm, if_pos hp]
    calc c * |cmDefect harmonicWeight harmonicShift p - 1 / logLogFloor p| *
          |Real.cos (t₀ * Real.log p)| * (p : ℝ)⁻¹
        ≤ c * (3600 / logLogFloor p ^ 2) * 1 * (p : ℝ)⁻¹ := by gcongr
      _ = 3600 * c * (1 / (p : ℝ) / logLogFloor p ^ 2) := by ring
  · simp only [primeRecipTerm, if_neg hp, zero_div, mul_zero, le_refl]

/-- **The Dini threshold of the log-log amplitude is one.** For `0 ≤ c ≤ 2` and `t₀ > 0`, the
half-damped weight of `f_c(p) = (1 − c/max(1, log log p)) cos(t₀ log p)` has bounded receiver iff
`c > 1` or `ζ(1/2 + it₀) = 0`. -/
theorem receiverBounded_logLogPattern_iff {c t₀ : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 2) (ht₀ : 0 < t₀) :
    ReceiverBounded (dampedSignWeight (logLogPattern c t₀) (1 / 2)) ↔
      1 < c ∨ riemannZeta (1 / 2 + t₀ * I) = 0 := by
  have hd := admissibleDefect_harmonic
  have hcW : c * ∑' k, harmonicWeight k ≤ 2 := by
    have := mul_le_mul_of_nonneg_left tsum_harmonicWeight_le hc; linarith
  have hf : ∀ p : ℕ, p.Prime → |defectPattern c t₀ harmonicWeight harmonicShift p| ≤ 1 :=
    fun p _ => abs_defectPattern_le hd hc hcW t₀ p
  have hf' : ∀ p : ℕ, p.Prime → |logLogPattern c t₀ p| ≤ 1 :=
    fun p hp => abs_logLogPattern_prime_le hc hc2 t₀ hp
  rw [receiverBounded_iff_of_summable_prime_diff hf hf' (by norm_num)
    (summable_logLogPattern_sub_defectPattern hc t₀)]
  exact receiverBounded_harmonicDefect_iff hc hc2 ht₀

/-- **The critical-line mass of the log-log pattern diverges** at every `0 < c ≤ 2`. -/
theorem not_summable_criticalLineMass_logLog {c t₀ : ℝ} (hc : 0 < c) (ht₀ : 0 < t₀) :
    ¬ Summable fun p : Nat.Primes =>
      |logLogPattern c t₀ p - oscPattern 1 t₀ p| / ((p : ℕ) : ℝ) := by
  intro hsum
  have hdiff := (summable_logLogPattern_sub_defectPattern hc.le t₀).comp_injective
    Nat.Primes.coe_nat_injective
  refine not_summable_criticalLineMass_harmonic hc ht₀ ((hsum.add hdiff).of_nonneg_of_le
    (fun p => by positivity) fun p => ?_)
  simp only [Function.comp_apply, if_pos p.2,
    show (-(1 / 2 + 1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
  rw [div_eq_mul_inv, div_eq_mul_inv, ← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  calc |defectPattern c t₀ harmonicWeight harmonicShift p - oscPattern 1 t₀ p|
      = |(logLogPattern c t₀ p - oscPattern 1 t₀ p) -
          (logLogPattern c t₀ p - defectPattern c t₀ harmonicWeight harmonicShift p)| := by
        congr 1; ring
    _ ≤ _ := abs_sub _ _

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
