import GaloisForLFunctions.HTGeometry.StonehamParityDriftVanishes

/-!
# The exact drift law of the Stoneham constant

For `α = Σ_{j ≥ 1} 3^{−j} 2^{−3^j}` the parity drift at the window ends `Nₖ = (3^{k+1} + 1)/2` is

`D_α(Nₖ) = 3k`  (`drift_stoneham_windowEnd`).

Inside the `k`-th window the base-4 digits of `α` are exactly the first base-4 digits of the orbit
`2Aₖ 4ⁱ/3ᵏ` (the tail of `α` shifts each point by less than `1/(4·3ᵏ)`, too little to cross a digit
boundary).  The window runs three times through the class `2 mod 3`, on which the drift weight sums
to exactly `1`: with `cₐ = ⌊(a 3ᵏ + 3)/12⌋` the class sum is `c₁ − 2c₂ + c₃ = 1`.

So the drift of `α` is `o(N)` but unbounded, growing like `3 log₃ N` along the window ends.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry.StonehamParityDrift

open BinaryParityDrift

theorem three_pow_mod_twelve {k : ℕ} (hk : 1 ≤ k) : 3 ^ k % 12 = 3 ∨ 3 ^ k % 12 = 9 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  induction m with
  | zero => left; norm_num
  | succ m ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih (by omega) with h | h <;> rw [h] <;> norm_num

theorem sum_range_ite_le (c τ : ℕ) (h : c ≤ τ) :
    ∑ u ∈ range τ, (if c ≤ u then (1 : ℤ) else 0) = τ - c := by
  rw [sum_boole]
  have : {u ∈ range τ | c ≤ u} = Ico c τ := by
    ext u; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [this, Nat.card_Ico]
  push_cast [h]
  ring

/-- **Exact balance on the residue class.**  The drift weight of the points `r/3ᵏ` with
`r ≡ 2 (mod 3)` sums to exactly `1`. -/
theorem sum_residueClass_two_cellWeight {k : ℕ} (hk : 1 ≤ k) :
    ∑ r ∈ residueClass k 2, cellWeight k r = 1 := by
  have hq := three_pow_eq_three_mul hk
  rw [sum_residueClass_two hk,
    sum_congr rfl fun u hu => cellWeight_three_mul_add_two (by have := mem_range.mp hu; omega),
    sum_sub_distrib, sum_add_distrib, sum_neg_distrib, ← mul_sum]
  have hthr : ∀ d ≤ 3, cellThreshold k d ≤ 3 ^ (k - 1) := by
    intro d hd; unfold cellThreshold; interval_cases d <;> omega
  rw [sum_range_ite_le _ _ (hthr 1 (by norm_num)), sum_range_ite_le _ _ (hthr 2 (by norm_num)),
    sum_range_ite_le _ _ (hthr 3 (by norm_num))]
  have hmod := three_pow_mod_twelve hk
  unfold cellThreshold
  omega

/-- Inside the `k`-th window the base-4 digits of `α` are the cell digits of its orbit. -/
theorem quatDigit_stoneham_window_eq {k i : ℕ} (hk : 1 ≤ k) (hi : i < 3 ^ k) :
    quatDigit stoneham ((3 ^ k + 1) / 2 + i + 1) =
      cellDigit k (2 * stonehamA k * 4 ^ i % 3 ^ k) := by
  obtain ⟨t, ht0, ht1, hq⟩ := quatDigit_stoneham_window hk hi
  rw [hq, cellDigit_eq_div]
  set ρ := 2 * stonehamA k * 4 ^ i % 3 ^ k with hρ
  set D := 4 * ρ / 3 ^ k with hD
  have hqpos : 0 < 3 ^ k := by positivity
  have hlo : D * 3 ^ k ≤ 4 * ρ := Nat.div_mul_le_self _ _
  have hhi : 4 * ρ + 1 ≤ (D + 1) * 3 ^ k := by
    have h := Nat.lt_mul_div_succ (4 * ρ) hqpos
    rw [← hD] at h
    rw [mul_comm (D + 1)]
    exact h
  have hloR : (D : ℝ) * 3 ^ k ≤ 4 * ρ := by exact_mod_cast hlo
  have hhiR : 4 * (ρ : ℝ) + 1 ≤ (D + 1) * 3 ^ k := by exact_mod_cast hhi
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  rw [Int.floor_eq_iff]
  push_cast
  constructor
  · rw [mul_add, mul_div_assoc']
    have : (D : ℝ) ≤ 4 * ρ / 3 ^ k := by rw [le_div_iff₀ h3]; exact hloR
    linarith
  · have ht' : 4 * t * 3 ^ k < 1 := by
      have := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ 4 * 3 ^ k)
      have e : 4 * 3 ^ k * (2 / (9 * 3 ^ k)) = (8 / 9 : ℝ) := by field_simp; norm_num
      nlinarith
    rw [show (4 : ℝ) * (ρ / 3 ^ k + t) = (4 * ρ + 4 * t * 3 ^ k) / 3 ^ k by field_simp,
      div_lt_iff₀ h3]
    linarith

/-- **Each complete window carries drift exactly `3`.** -/
theorem sum_window_eq_three {k : ℕ} (hk : 1 ≤ k) :
    ∑ i ∈ range (3 ^ k), digitWeight (quatDigit stoneham ((3 ^ k + 1) / 2 + i + 1)) = 3 := by
  have hbmod : (2 * stonehamA k) % 3 = 2 := by rw [Nat.mul_mod, stonehamA_mod_three hk]
  have hb3 : ¬ 3 ∣ 2 * stonehamA k := by omega
  rw [sum_congr rfl fun i hi => by rw [quatDigit_stoneham_window_eq hk (mem_range.mp hi)]]
  change ∑ i ∈ range (3 ^ k), cellWeight k (2 * stonehamA k * 4 ^ i % 3 ^ k) = 3
  rw [sum_range_three_periods hk _ (cellWeight k), sum_range_orbit_eq hk hb3, hbmod,
    sum_residueClass_two_cellWeight hk]
  norm_num

theorem stoneham_lt_one_sixteenth : stoneham < 1 / 16 := by
  have hb : ∀ j, stonehamTerm j ≤ 1 / 24 * (1 / 8 : ℝ) ^ j := by
    intro j
    unfold stonehamTerm
    rw [one_div_pow, one_div_mul_one_div, one_div_le_one_div (by positivity) (by positivity)]
    have hj : 3 * j + 3 ≤ 3 ^ (j + 1) := by
      have : 1 + j ≤ 3 ^ j := by
        induction j with
        | zero => simp
        | succ j ih => rw [pow_succ]; omega
      rw [pow_succ]; omega
    have h1 : (2 : ℝ) ^ (3 * j + 3) ≤ 2 ^ 3 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) hj
    have h2 : (3 : ℝ) ≤ 3 ^ (j + 1) := by
      calc (3 : ℝ) = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have e : (24 : ℝ) * 8 ^ j = 3 * 2 ^ (3 * j + 3) := by
      rw [pow_add, pow_mul]; norm_num; ring
    rw [e]
    exact mul_le_mul h2 h1 (by positivity) (by positivity)
  have hg : Summable fun j : ℕ => 1 / 24 * (1 / 8 : ℝ) ^ j :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  calc stoneham ≤ ∑' j : ℕ, 1 / 24 * (1 / 8 : ℝ) ^ j :=
        Summable.tsum_le_tsum hb summable_stonehamTerm hg
    _ = 1 / 21 := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
    _ < 1 / 16 := by norm_num

theorem stoneham_pos : 0 < stoneham :=
  summable_stonehamTerm.tsum_pos (fun j => (stonehamTerm_pos j).le) 0 (stonehamTerm_pos 0)

/-- **The exact drift law.**  `D_α((3^{k+1} + 1)/2) = 3k`. -/
theorem drift_stoneham_windowEnd (k : ℕ) : drift stoneham (windowEnd k) = 3 * k := by
  induction k with
  | zero =>
    have h2 : windowEnd 0 = 2 := by decide
    have hq : ∀ n ∈ range 2, quatDigit stoneham (n + 1) = 0 := by
      intro n hn
      have hn' := mem_range.mp hn
      unfold quatDigit
      have h0 : 0 ≤ (4 : ℝ) ^ (n + 1) * stoneham := by positivity [stoneham_pos.le]
      have h1 : (4 : ℝ) ^ (n + 1) * stoneham < 1 := by
        have h16 : (4 : ℝ) ^ (n + 1) ≤ 16 := by
          calc (4 : ℝ) ^ (n + 1) ≤ 4 ^ 2 := pow_le_pow_right₀ (by norm_num) (by omega)
            _ = 16 := by norm_num
        have := stoneham_lt_one_sixteenth
        nlinarith [stoneham_pos]
      rw [Int.floor_eq_zero_iff.mpr ⟨h0, h1⟩]
      rfl
    rw [h2, drift_eq_sum_digitWeight, sum_congr rfl fun n hn => by rw [hq n hn]]
    simp [digitWeight]
  | succ k ih =>
    have hsplit : drift stoneham (windowEnd (k + 1)) = drift stoneham (windowEnd k) +
        ∑ i ∈ range (3 ^ (k + 1)),
          digitWeight (quatDigit stoneham ((3 ^ (k + 1) + 1) / 2 + i + 1)) := by
      rw [windowEnd_succ, drift_eq_sum_digitWeight, drift_eq_sum_digitWeight, sum_range_add]
      rfl
    rw [hsplit, ih, sum_window_eq_three (by omega)]
    push_cast
    ring

/-- The parity drift of `α` is unbounded: it tends to `+∞` along the window ends. -/
theorem tendsto_drift_stoneham_windowEnd :
    Tendsto (fun k => drift stoneham (windowEnd k)) atTop atTop := by
  simp_rw [drift_stoneham_windowEnd]
  exact tendsto_natCast_atTop_atTop.const_mul_atTop' (by norm_num)

end GaloisForLFunctions.HTGeometry.StonehamParityDrift
