import GaloisForLFunctions.RHTower.WeilFullConeZeroFreeWindowRigidity

/-!
# Square-root-scale rigidity of the full Weil cone

**Theorem** (`eq_vonMangoldt_of_weilPositiveFull_of_sqrt_scale`, unconditional). Let `lam` be
full-cone Weil-positive with `|lam(n) − Λ(n)| ≤ C (1 + log n)^B / √n` for all `n ≥ 2`. Then
`lam = Λ`.

The deviation may be dense on `ℕ` and two-sided, and it need not be absolutely summable against
`n^{−½}`. Its partial sums may reach the `√x` scale with slowly varying oscillation, e.g.
`√x · f(log x)`. This lies beyond the power-saving exact-primes gate (MUST-507, partial sums
`O(x^θ)` with `θ < ½`) and beyond the `ℓ¹(n^{−½})` class.

**Proof.** The zero-free-window method of `WeilFullConeZeroFreeWindowRigidity` is used, with the
separation hypothesis replaced by an integer kernel bound:
- `|log n − log m| ≥ |n − m|/max(n,m)` (`inv_log_sub_log_le`);
- the harmonic bound `Σ_{n<m} 1/(m − n) ≤ 1 + log m`.

These give `Σ_n F(n) κ(n,m) ≤ 2 + 3ΣF + log m` for `F(n) = 1/(n(1 + log n)³)`
(`tsum_invLogWeight_mul_intLogKernel_le`). The pointwise size `n^{−½}` makes the coefficients
`c_n = v(n)B(η log n)` of size `η^{−J} F(n)`. Consequently:
- the extraction error is `O(η^{−J} log m)`;
- the off-diagonal mean-square error is `O(η^{−2J})`;
- both are negligible at height `T = η^{−(2J+1)}`.

**Sharpness of the method.** For `|lam − Λ| ≍ n^{−θ}` with `θ < ½`, the near-diagonal Schur sum
`Σ_m |c_m| m^{½−θ}` diverges. So pointwise size `n^{−½+o(1)}` is exactly the reach of zero-free
windows on the full integer support.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate Convolution FourierTransform
open Zeta23

namespace RHTower

noncomputable section

/-! ## Integer log-kernel sums -/

/-- `F_D(n) = 1/(n (1 + log n)^D)`. -/
def invLogWeight (D n : ℕ) : ℝ := ((n : ℝ) * (1 + Real.log n) ^ D)⁻¹

theorem invLogWeight_nonneg (D n : ℕ) : 0 ≤ invLogWeight D n := by
  unfold invLogWeight
  have := Real.log_natCast_nonneg n
  positivity

theorem invLogWeight_le_one (D n : ℕ) : invLogWeight D n ≤ 1 := by
  unfold invLogWeight
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hl := Real.log_natCast_nonneg n
    have h1 : (1 : ℝ) ≤ (n : ℝ) * (1 + Real.log n) ^ D :=
      one_le_mul_of_one_le_of_one_le hn1 (one_le_pow₀ (by linarith))
    exact inv_le_one_of_one_le₀ h1

theorem invLogWeight_antitone (D : ℕ) ⦃m n : ℕ⦄ (hm : 0 < m) (hmn : m ≤ n) :
    invLogWeight D n ≤ invLogWeight D m := by
  unfold invLogWeight
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hlm := Real.log_natCast_nonneg m
  have hlog : Real.log m ≤ Real.log n := Real.log_le_log (by linarith) hmn'
  refine inv_anti₀ (by positivity) (mul_le_mul hmn' (pow_le_pow_left₀ (by linarith) (by linarith) D)
    (by positivity) (by linarith))

/-- `Σ 1/(n (1 + log n)^D) < ∞` for `D ≥ 2` (Cauchy condensation). -/
theorem summable_invLogWeight {D : ℕ} (hD : 2 ≤ D) : Summable (invLogWeight D) := by
  refine (summable_condensed_iff_of_nonneg (invLogWeight_nonneg D)
    (invLogWeight_antitone D)).mp ?_
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl21 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  refine (summable_inv_one_add_nat_sq.mul_left ((Real.log 2)⁻¹ ^ 2)).of_nonneg_of_le
    (fun k => by have := invLogWeight_nonneg D (2 ^ k); positivity) fun k => ?_
  unfold invLogWeight
  push_cast
  rw [Real.log_pow]
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hb : (1 : ℝ) ≤ 1 + k * Real.log 2 := by
    have : (0 : ℝ) ≤ k * Real.log 2 := by positivity
    linarith
  have hge : Real.log 2 * (1 + k) ≤ 1 + k * Real.log 2 := by nlinarith
  rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ h2k.ne', one_mul]
  calc ((1 + (k : ℝ) * Real.log 2) ^ D)⁻¹ ≤ ((1 + (k : ℝ) * Real.log 2) ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_right₀ hb hD)
    _ ≤ ((Real.log 2 * (1 + k)) ^ 2)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hge 2)
    _ = (Real.log 2)⁻¹ ^ 2 * (((1 : ℝ) + k) ^ 2)⁻¹ := by rw [mul_pow, mul_inv, inv_pow]

/-- `1/(log n − log m) ≤ n/(n − m)` for `n > m ≥ 1`. -/
theorem inv_log_sub_log_le {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    (Real.log n - Real.log m)⁻¹ ≤ (n : ℝ) / ((n : ℝ) - m) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmn' : (m : ℝ) < n := by exact_mod_cast hmn
  have hpos : 0 < (n : ℝ) / m := div_pos (by linarith) (by linarith)
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hm0 : (m : ℝ) ≠ 0 := by linarith
  rw [inv_div, Real.log_div hn0 hm0] at h
  have hd : 0 < ((n : ℝ) - m) / n := div_pos (by linarith) (by linarith)
  have e : 1 - (m : ℝ) / n = ((n : ℝ) - m) / n := by field_simp
  rw [e] at h
  calc (Real.log n - Real.log m)⁻¹ ≤ (((n : ℝ) - m) / n)⁻¹ := inv_anti₀ hd h
    _ = (n : ℝ) / ((n : ℝ) - m) := by rw [inv_div]


/-- The integer mean-value kernel `κ(n, m)`. -/
def intLogKernel (n m : ℕ) : ℝ := if n = m then 1 else |Real.log n - Real.log m|⁻¹ + 1

/-- The majorant of `F(n) κ(n, m)`. -/
def intLogMajorant (D m n : ℕ) : ℝ :=
  (if n = m then 1 else 0) + invLogWeight D n + (if m < n then invLogWeight D (n - m) else 0) +
    (if n < m then invLogWeight D n + ((m : ℝ) - n)⁻¹ else 0)

theorem invLogWeight_mul_intLogKernel_le (D : ℕ) {m : ℕ} (hm : 2 ≤ m) (n : ℕ) :
    invLogWeight D n * intLogKernel n m ≤ intLogMajorant D m n := by
  have hF0 := invLogWeight_nonneg D n
  unfold intLogMajorant intLogKernel
  by_cases hnm : n = m
  · subst hnm
    simp only [if_true, lt_irrefl, if_false, add_zero, mul_one]
    have := invLogWeight_le_one D n
    linarith
  rw [if_neg hnm, if_neg hnm, zero_add]
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · have h0 : invLogWeight D 0 = 0 := by simp [invLogWeight]
    rw [h0, zero_mul, if_neg (by omega : ¬ m < 0), if_pos (by omega : 0 < m)]
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    push_cast; positivity
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · -- `n < m`
    rw [if_neg (not_lt.mpr hlt.le), if_pos hlt, add_zero]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    have hmn : (n : ℝ) < m := by exact_mod_cast hlt
    have hl := inv_log_sub_log_le (m := n) (n := m) hn0 hlt
    have habs : |Real.log n - Real.log m|⁻¹ = (Real.log m - Real.log n)⁻¹ := by
      rw [abs_sub_comm, abs_of_pos (sub_pos.mpr (Real.log_lt_log (by linarith) hmn))]
    rw [habs]
    have hlog0 := Real.log_natCast_nonneg n
    have hpow : 1 ≤ (1 + Real.log n) ^ D := one_le_pow₀ (by linarith)
    have key : invLogWeight D n * ((m : ℝ) / ((m : ℝ) - n)) ≤ invLogWeight D n + ((m : ℝ) - n)⁻¹ := by
      unfold invLogWeight
      have hd : 0 < (m : ℝ) - n := by linarith
      have e : ((n : ℝ) * (1 + Real.log n) ^ D)⁻¹ * ((m : ℝ) / ((m : ℝ) - n)) =
          ((1 + Real.log n) ^ D)⁻¹ * ((n : ℝ)⁻¹ + ((m : ℝ) - n)⁻¹) := by
        field_simp; ring
      rw [e, mul_add]
      have h3 : ((1 + Real.log n) ^ D)⁻¹ * ((m : ℝ) - n)⁻¹ ≤ ((m : ℝ) - n)⁻¹ :=
        mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ hpow)
      have h4 : ((1 + Real.log n) ^ D)⁻¹ * (n : ℝ)⁻¹ = ((n : ℝ) * (1 + Real.log n) ^ D)⁻¹ := by
        rw [mul_inv, mul_comm]
      linarith
    have := mul_le_mul_of_nonneg_left hl hF0
    nlinarith
  · -- `m < n`
    rw [if_pos hgt, if_neg (not_lt.mpr hgt.le), add_zero]
    have hm1 : 1 ≤ m := by omega
    have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hmn : (m : ℝ) < n := by exact_mod_cast hgt
    have hl := inv_log_sub_log_le hm1 hgt
    have habs : |Real.log n - Real.log m|⁻¹ = (Real.log n - Real.log m)⁻¹ := by
      rw [abs_of_pos (sub_pos.mpr (Real.log_lt_log (by linarith) hmn))]
    rw [habs]
    have key : invLogWeight D n * ((n : ℝ) / ((n : ℝ) - m)) ≤ invLogWeight D (n - m) := by
      unfold invLogWeight
      have hk : 1 ≤ n - m := by omega
      have hk' : (1 : ℝ) ≤ ((n - m : ℕ) : ℝ) := by exact_mod_cast hk
      have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := by push_cast [Nat.cast_sub hgt.le]; ring
      have hlk : Real.log ((n - m : ℕ) : ℝ) ≤ Real.log n :=
        Real.log_le_log (by linarith) (by rw [hcast]; linarith)
      have hlk0 := Real.log_natCast_nonneg (n - m)
      have e : ((n : ℝ) * (1 + Real.log n) ^ D)⁻¹ * ((n : ℝ) / ((n : ℝ) - m)) =
          (((n : ℝ) - m) * (1 + Real.log n) ^ D)⁻¹ := by
        have : (n : ℝ) ≠ 0 := by linarith
        have : (n : ℝ) - m ≠ 0 := by linarith
        field_simp
      rw [e, ← hcast]
      exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith) (by linarith) D) (by linarith))
    have := mul_le_mul_of_nonneg_left hl hF0
    nlinarith

theorem summable_shift_invLogWeight {D : ℕ} (hD : 2 ≤ D) (m : ℕ) :
    Summable fun n : ℕ => if m < n then invLogWeight D (n - m) else 0 := by
  have h1 : Summable fun i : ℕ => invLogWeight D (i + 1) :=
    (summable_nat_add_iff 1).mpr (summable_invLogWeight hD)
  refine (summable_nat_add_iff (m + 1)).mp (h1.congr fun i => ?_)
  rw [if_pos (by omega), show i + (m + 1) - m = i + 1 by omega]

theorem tsum_shift_invLogWeight_le {D : ℕ} (hD : 2 ≤ D) (m : ℕ) :
    ∑' n : ℕ, (if m < n then invLogWeight D (n - m) else 0) ≤ ∑' n, invLogWeight D n := by
  have hs := summable_shift_invLogWeight hD m
  have h := hs.sum_add_tsum_nat_add (m + 1)
  have hz : ∑ i ∈ Finset.range (m + 1), (if m < i then invLogWeight D (i - m) else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [Finset.mem_range] at hi; rw [if_neg (by omega)]
  rw [hz, zero_add] at h
  have e : (fun i : ℕ => if m < i + (m + 1) then invLogWeight D (i + (m + 1) - m) else 0) =
      fun i => invLogWeight D (i + 1) := by
    funext i; rw [if_pos (by omega), show i + (m + 1) - m = i + 1 by omega]
  rw [e] at h
  have hF := summable_invLogWeight hD
  have h2 := hF.sum_add_tsum_nat_add 1
  simp only [Finset.range_one, Finset.sum_singleton] at h2
  have h0 : invLogWeight D 0 = 0 := by simp [invLogWeight]
  rw [h0, zero_add] at h2
  rw [← h, h2]

theorem sum_range_inv_sub_le (m : ℕ) :
    ∑ n ∈ Finset.range m, ((m : ℝ) - n)⁻¹ ≤ 1 + Real.log m := by
  have e : ∑ n ∈ Finset.range m, ((m : ℝ) - n)⁻¹ = ∑ j ∈ Finset.range m, (((j + 1 : ℕ) : ℝ))⁻¹ := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    congr 1
    push_cast [Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_sub (show j ≤ m - 1 by omega)]
    ring
  rw [e]
  have h := harmonic_le_one_add_log m
  have hh : ((harmonic m : ℚ) : ℝ) = ∑ j ∈ Finset.range m, (((j + 1 : ℕ) : ℝ))⁻¹ := by
    unfold harmonic; push_cast; rfl
  rw [← hh]; exact h

/-- **The integer Schur bound.** `Σ_n F(n) κ(n, m) ≤ 2 + 3 Σ F + log m`. -/
theorem tsum_invLogWeight_mul_intLogKernel_le {D : ℕ} (hD : 2 ≤ D) {m : ℕ} (hm : 2 ≤ m) :
    Summable (fun n => invLogWeight D n * intLogKernel n m) ∧
      ∑' n, invLogWeight D n * intLogKernel n m ≤
        2 + 3 * (∑' n, invLogWeight D n) + Real.log m := by
  have hF := summable_invLogWeight hD
  have hS1 : Summable fun n : ℕ => (if n = m then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {m}) fun n hn => by
      rw [Finset.mem_singleton] at hn; rw [if_neg hn]
  have hS3 := summable_shift_invLogWeight hD m
  have hS4 : Summable fun n : ℕ => (if n < m then invLogWeight D n + ((m : ℝ) - n)⁻¹ else 0) :=
    summable_of_ne_finset_zero (s := Finset.range m) fun n hn => by
      rw [Finset.mem_range] at hn; rw [if_neg hn]
  have hM : Summable (intLogMajorant D m) := ((hS1.add hF).add hS3).add hS4
  have hle := invLogWeight_mul_intLogKernel_le D hm
  have hnn : ∀ n, 0 ≤ invLogWeight D n * intLogKernel n m := fun n => by
    unfold intLogKernel; have := invLogWeight_nonneg D n; split_ifs <;> positivity
  have hsum : Summable (fun n => invLogWeight D n * intLogKernel n m) :=
    hM.of_nonneg_of_le hnn hle
  refine ⟨hsum, (hsum.tsum_le_tsum hle hM).trans ?_⟩
  unfold intLogMajorant
  rw [(hS1.add hF).add hS3 |>.tsum_add hS4, (hS1.add hF).tsum_add hS3, hS1.tsum_add hF,
    tsum_ite_eq]
  have h3 := tsum_shift_invLogWeight_le hD m
  have h4 : ∑' n : ℕ, (if n < m then invLogWeight D n + ((m : ℝ) - n)⁻¹ else 0) ≤
      ∑' n, invLogWeight D n + (1 + Real.log m) := by
    rw [tsum_eq_sum (s := Finset.range m) fun n hn => by
      rw [Finset.mem_range] at hn; rw [if_neg hn]]
    rw [Finset.sum_congr rfl fun n hn => by rw [if_pos (Finset.mem_range.mp hn)],
      Finset.sum_add_distrib]
    have h5 : ∑ n ∈ Finset.range m, invLogWeight D n ≤ ∑' n, invLogWeight D n :=
      hF.sum_le_tsum _ fun n _ => invLogWeight_nonneg D n
    have h6 := sum_range_inv_sub_le m
    linarith
  linarith


/-! ## Mean values with the integer kernel -/

/-- The pointwise mean-value kernel bound on integer frequencies. -/
theorem abs_meanKernel_le_intLogKernel {c : ℕ → ℝ} (hc2 : ∀ n, c n ≠ 0 → 2 ≤ n) {m : ℕ}
    (hm2 : 2 ≤ m) (a b : ℝ) (n : ℕ) :
    |c n * (∫ t in a..b, Real.cos (2 * π * t * Real.log n) * Real.cos (2 * π * t * Real.log m)) -
        (if n = m then (b - a) / 2 * c m else 0)| ≤ |c n| * intLogKernel n m := by
  have hπ := Real.pi_gt_three
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlm : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) (by exact_mod_cast hm2)
  unfold intLogKernel
  by_cases hnm : n = m
  · subst hnm
    rw [if_pos rfl, if_pos rfl, show c n * (∫ t in a..b, Real.cos (2 * π * t * Real.log n) *
      Real.cos (2 * π * t * Real.log n)) - (b - a) / 2 * c n = c n *
      ((∫ t in a..b, Real.cos (2 * π * t * Real.log n) * Real.cos (2 * π * t * Real.log n)) -
        (b - a) / 2) by ring, abs_mul, mul_one]
    have hlpos : 0 < Real.log n := by linarith
    have h := abs_integral_cos_sq_sub_le (lA := Real.log n) hlpos a b
    have h1 : 1 / (4 * π * Real.log n) ≤ 1 := by
      rw [div_le_one (mul_pos (by positivity) hlpos)]; nlinarith
    exact mul_le_of_le_one_right (abs_nonneg _) (h.trans h1)
  rw [if_neg hnm, if_neg hnm, sub_zero, abs_mul]
  by_cases hn : c n = 0
  · rw [hn, abs_zero, zero_mul, zero_mul]
  have hln : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hc2 n hn)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by have := hc2 n hn; omega : 1 < n)
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hne : Real.log n ≠ Real.log m := by
    intro h
    have h' : (n : ℝ) = m :=
      Real.log_injOn_pos (Set.mem_Ioi.mpr (by linarith)) (Set.mem_Ioi.mpr (by linarith)) h
    exact hnm (by exact_mod_cast h')
  have h := abs_integral_cos_mul_cos_le (lA := Real.log n) (lB := Real.log m) (by linarith)
    (by linarith) hne a b
  have hd : 0 < |Real.log n - Real.log m| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have h1 : 1 / (2 * π * |Real.log n - Real.log m|) ≤ |Real.log n - Real.log m|⁻¹ := by
    rw [one_div]; exact inv_anti₀ hd (by nlinarith)
  have h2 : 1 / (2 * π * (Real.log n + Real.log m)) ≤ 1 := by
    rw [div_le_one (mul_pos (by positivity) (by linarith))]; nlinarith
  exact mul_le_mul_of_nonneg_left (h.trans (add_le_add h1 h2)) (abs_nonneg _)

/-- The coefficient extraction with an arbitrary summable kernel majorant. -/
theorem abs_integral_windowCosSeries_mul_cos_sub_le_of_bound {c : ℕ → ℝ}
    (hc : Summable fun n => |c n|) {m : ℕ} (a b : ℝ) {E : ℕ → ℝ}
    (hE : ∀ n, |c n * (∫ t in a..b, Real.cos (2 * π * t * Real.log n) *
      Real.cos (2 * π * t * Real.log m)) - (if n = m then (b - a) / 2 * c m else 0)| ≤ E n)
    (hEs : Summable E) :
    |(∫ t in a..b, windowCosSeries c t * Real.cos (2 * π * t * Real.log m)) - (b - a) / 2 * c m| ≤
      ∑' n, E n := by
  have e1 : (fun t => windowCosSeries c t * Real.cos (2 * π * t * Real.log m)) = fun t =>
      ∑' n, c n * (Real.cos (2 * π * t * Real.log n) * Real.cos (2 * π * t * Real.log m)) := by
    funext t; unfold windowCosSeries; rw [← tsum_mul_right]; exact tsum_congr fun n => by ring
  rw [e1, integral_tsum_mul_of_abs_le hc (M := 1) (fun n => by fun_prop) (fun n t => by
    rw [abs_mul]; exact mul_le_one₀ (Real.abs_cos_le_one _) (abs_nonneg _) (Real.abs_cos_le_one _))]
  set I : ℕ → ℝ := fun n => ∫ t in a..b, Real.cos (2 * π * t * Real.log n) *
    Real.cos (2 * π * t * Real.log m) with hI
  have hIb : ∀ n, |I n| ≤ |b - a| := fun n => by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := 1)
      (f := fun t => Real.cos (2 * π * t * Real.log n) * Real.cos (2 * π * t * Real.log m))
      (fun t _ => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_one₀ (Real.abs_cos_le_one _) (abs_nonneg _) (Real.abs_cos_le_one _))
    rw [one_mul, Real.norm_eq_abs] at h
    exact h
  have hs1 : Summable fun n => c n * I n := (hc.mul_right |b - a|).of_norm_bounded fun n => by
    rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul_of_nonneg_left (hIb n) (abs_nonneg _)
  have hs2 : Summable fun n : ℕ => if n = m then (b - a) / 2 * c m else 0 :=
    summable_of_ne_finset_zero (s := {m}) fun n hn => by
      rw [Finset.mem_singleton] at hn; rw [if_neg hn]
  have hsum : (∑' n, c n * I n) - (b - a) / 2 * c m =
      ∑' n, (c n * I n - if n = m then (b - a) / 2 * c m else 0) := by
    rw [hs1.tsum_sub hs2, tsum_ite_eq]
  rw [hsum]
  have hs4 : Summable fun n => |c n * I n - if n = m then (b - a) / 2 * c m else 0| :=
    hEs.of_nonneg_of_le (fun n => abs_nonneg _) hE
  calc |∑' n, (c n * I n - if n = m then (b - a) / 2 * c m else 0)|
      ≤ ∑' n, |c n * I n - if n = m then (b - a) / 2 * c m else 0| := by
        rw [← Real.norm_eq_abs]
        exact (norm_tsum_le_tsum_norm (by simpa [Real.norm_eq_abs] using hs4)).trans
          (le_of_eq (tsum_congr fun n => Real.norm_eq_abs _))
    _ ≤ ∑' n, E n := hs4.tsum_le_tsum hE hEs

/-- The mean square with arbitrary extraction bounds. -/
theorem abs_integral_windowCosSeries_sq_sub_le_of_bound {c : ℕ → ℝ}
    (hc : Summable fun n => |c n|) (a b : ℝ) {R : ℕ → ℝ}
    (hR : ∀ m, c m ≠ 0 → |(∫ t in a..b, windowCosSeries c t * Real.cos (2 * π * t * Real.log m)) -
      (b - a) / 2 * c m| ≤ R m)
    (hRs : Summable fun m => |c m| * R m) :
    |(∫ t in a..b, windowCosSeries c t ^ 2) - (b - a) / 2 * ∑' n, c n ^ 2| ≤
      ∑' m, |c m| * R m := by
  set A := ∑' n, |c n| with hAdef
  have e1 : (fun t => windowCosSeries c t ^ 2) = fun t =>
      ∑' m, c m * (Real.cos (2 * π * t * Real.log m) * windowCosSeries c t) := by
    funext t
    rw [sq]
    conv_lhs => rw [show windowCosSeries c t * windowCosSeries c t =
      (∑' m, c m * Real.cos (2 * π * t * Real.log m)) * windowCosSeries c t from rfl]
    rw [← tsum_mul_right]; exact tsum_congr fun m => by ring
  rw [e1, integral_tsum_mul_of_abs_le hc (M := A) (fun m => by
    have := continuous_windowCosSeries hc; fun_prop) (fun m t => by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _) |>.trans
      (abs_windowCosSeries_le hc t))]
  have hIb : ∀ m : ℕ, |∫ t in a..b, Real.cos (2 * π * t * Real.log m) * windowCosSeries c t| ≤
      A * |b - a| := by
    intro m
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := A)
      (f := fun t => Real.cos (2 * π * t * Real.log m) * windowCosSeries c t)
      (fun t _ => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _) |>.trans
          (abs_windowCosSeries_le hc t))
    rwa [Real.norm_eq_abs] at h
  have hs1 : Summable fun m => c m * ∫ t in a..b, Real.cos (2 * π * t * Real.log m) *
      windowCosSeries c t :=
    (hc.mul_right (A * |b - a|)).of_norm_bounded fun m => by
      rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul_of_nonneg_left (hIb m) (abs_nonneg _)
  have hA0 : 0 ≤ A := tsum_nonneg fun _ => abs_nonneg _
  have hs2 : Summable fun m => c m ^ 2 := (hc.mul_left A).of_norm_bounded fun m => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq, ← abs_mul_abs_self]
    exact mul_le_mul_of_nonneg_right (by rw [hAdef]; exact hc.le_tsum m (fun _ _ => abs_nonneg _))
      (abs_nonneg _)
  have hsum : (∑' m, c m * ∫ t in a..b, Real.cos (2 * π * t * Real.log m) * windowCosSeries c t) -
      (b - a) / 2 * ∑' n, c n ^ 2 =
      ∑' m, c m * ((∫ t in a..b, windowCosSeries c t * Real.cos (2 * π * t * Real.log m)) -
        (b - a) / 2 * c m) := by
    rw [← tsum_mul_left, ← hs1.tsum_sub (hs2.mul_left _)]
    refine tsum_congr fun m => ?_
    have : (∫ t in a..b, Real.cos (2 * π * t * Real.log m) * windowCosSeries c t) =
        ∫ t in a..b, windowCosSeries c t * Real.cos (2 * π * t * Real.log m) := by
      congr 1; funext t; ring
    rw [this]; ring
  rw [hsum]
  have hb : ∀ m, |c m * ((∫ t in a..b, windowCosSeries c t * Real.cos (2 * π * t * Real.log m)) -
      (b - a) / 2 * c m)| ≤ |c m| * R m := by
    intro m
    by_cases hm : c m = 0
    · simp [hm]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hR m hm) (abs_nonneg _)
  have hs4 := hRs.of_nonneg_of_le (fun m => abs_nonneg _) hb
  calc |∑' m, c m * ((∫ t in a..b, windowCosSeries c t * Real.cos (2 * π * t * Real.log m)) -
        (b - a) / 2 * c m)|
      ≤ ∑' m, |c m * ((∫ t in a..b, windowCosSeries c t * Real.cos (2 * π * t * Real.log m)) -
        (b - a) / 2 * c m)| := by
        rw [← Real.norm_eq_abs]
        exact (norm_tsum_le_tsum_norm (by simpa [Real.norm_eq_abs] using hs4)).trans
          (le_of_eq (tsum_congr fun n => Real.norm_eq_abs _))
    _ ≤ ∑' m, |c m| * R m := hs4.tsum_le_tsum hb hRs

/-- **Assembly with arbitrary mean-value bounds.** -/
theorem half_mul_abs_le_of_zeroFree_of_bounds {c : ℕ → ℝ}
    (hc2 : ∀ n, c n ≠ 0 → 2 ≤ n) (hc : Summable fun n => |c n|) {T l η : ℝ} (hT : 1 ≤ T) (hl : 0 < l)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hpos : ∀ t, T ≤ t → t ≤ 2 * T → (∀ ξ, |ξ - t| < η → phiFourierReal ξ ≠ 0) →
      0 ≤ windowCosSeries c t)
    {m : ℕ} {Rm QQ : ℝ}
    (hext : |(∫ t in T..2 * T, windowCosSeries c t * Real.cos (2 * π * t * Real.log m)) -
      T / 2 * c m| ≤ Rm)
    (hsq : |(∫ t in T..2 * T, windowCosSeries c t ^ 2) - T / 2 * ∑' n, c n ^ 2| ≤ QQ) :
    T / 2 * |c m| ≤ (∑' n, |c n|) / (π * Real.log 2) +
      2 * (1 / (2 * l) * (T / 2 * ∑' n, c n ^ 2 + QQ)
        + l / 2 * (2 * η * ((((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1) *
          unitZeroBound (|T - 1| + (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1))))) + Rm := by
  set Y := windowCosSeries c with hYdef
  have hYc : Continuous Y := continuous_windowCosSeries hc
  set N : ℕ := ⌈T⌉₊ + 1 with hN
  obtain ⟨hZf, hZc⟩ := realZeroSet_multi (T - 1) N
  set Zf := hZf.toFinset with hZfdef
  set Sf : ℝ → ℝ := fun t => ∑ z ∈ Zf, (Ioo (z - η) (z + η)).indicator (1 : ℝ → ℝ) t with hSf
  have hab : T ≤ 2 * T := by linarith
  have hNT : T + 1 ≤ (N : ℝ) := by
    rw [hN]; push_cast; linarith [Nat.le_ceil T]
  -- the pointwise bound
  have hpt : ∀ t ∈ Icc T (2 * T), max (-Y t) 0 ≤ Y t ^ 2 / (2 * l) + l / 2 * Sf t := by
    rintro t ⟨ht1, ht2⟩
    have hS0 : 0 ≤ Sf t := Finset.sum_nonneg fun z _ =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) t
    by_cases hz : ∃ z ∈ Zf, t ∈ Ioo (z - η) (z + η)
    · obtain ⟨z, hzZ, hzt⟩ := hz
      have h1 : 1 ≤ Sf t := by
        have := Finset.single_le_sum (f := fun z => (Ioo (z - η) (z + η)).indicator
          (1 : ℝ → ℝ) t) (fun z _ => Set.indicator_nonneg (fun _ _ => zero_le_one) t) hzZ
        simp only [Set.indicator_of_mem hzt, Pi.one_apply] at this
        exact this
      have := neg_part_le (Y t) hl
      nlinarith
    · push Not at hz
      have hfree : ∀ ξ, |ξ - t| < η → phiFourierReal ξ ≠ 0 := by
        intro ξ hξ h0
        rw [abs_lt] at hξ
        have hmem : ξ ∈ realZeroSet (T - 1) (T - 1 + (N + 1)) :=
          ⟨⟨by linarith, by linarith⟩, h0⟩
        exact hz ξ (hZf.mem_toFinset.mpr hmem) ⟨by linarith, by linarith⟩
      have h0 := hpos t ht1 ht2 hfree
      rw [max_eq_right (by linarith)]
      positivity
  have hSint : Integrable Sf := by
    rw [hSf]
    exact integrable_finsetSum _ fun z _ => integrable_indicator_Ioo z η
  have hSi : IntervalIntegrable Sf volume T (2 * T) := hSint.intervalIntegrable
  have hYi : IntervalIntegrable Y volume T (2 * T) := hYc.intervalIntegrable _ _
  have hY2i : IntervalIntegrable (fun t => Y t ^ 2) volume T (2 * T) :=
    (hYc.pow 2).intervalIntegrable _ _
  have hNi : IntervalIntegrable (fun t => max (-Y t) 0) volume T (2 * T) :=
    (hYc.neg.max continuous_const).intervalIntegrable _ _
  -- (a) the coefficient extraction
  have ha := hext
  set I1 := ∫ t in T..2 * T, windowCosSeries c t * Real.cos (2 * π * t * Real.log m) with hI1
  -- (b) `|I1| ≤ ∫ |Y|`
  have hb : |I1| ≤ ∫ t in T..2 * T, |Y t| := by
    refine (intervalIntegral.abs_integral_le_integral_abs hab).trans
      (intervalIntegral.integral_mono_on hab ?_ ((hYc.abs).intervalIntegrable _ _) fun t _ => ?_)
    · exact ((hYc.mul (by fun_prop)).abs).intervalIntegrable _ _
    · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  -- (c) `∫ |Y| = ∫ Y + 2 ∫ Y⁻`
  have hc' : (∫ t in T..2 * T, |Y t|) = (∫ t in T..2 * T, Y t) +
      2 * ∫ t in T..2 * T, max (-Y t) 0 := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hYi (hNi.const_mul 2)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rcases le_or_gt 0 (Y t) with h | h
    · rw [abs_of_nonneg h, max_eq_right (by linarith)]; ring
    · rw [abs_of_neg h, max_eq_left (by linarith)]; ring
  -- (d) the negative part
  have hd : (∫ t in T..2 * T, max (-Y t) 0) ≤
      1 / (2 * l) * (∫ t in T..2 * T, Y t ^ 2) + l / 2 * ∫ t in T..2 * T, Sf t := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hY2i.const_mul _) (hSi.const_mul _)]
    refine intervalIntegral.integral_mono_on hab hNi ((hY2i.const_mul _).add (hSi.const_mul _))
      fun t ht => ?_
    have := hpt t ht
    calc max (-Y t) 0 ≤ Y t ^ 2 / (2 * l) + l / 2 * Sf t := this
      _ = 1 / (2 * l) * Y t ^ 2 + l / 2 * Sf t := by ring
  -- (e) the bad-set mass
  have he : (∫ t in T..2 * T, Sf t) ≤ 2 * η * ((((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1) *
      unitZeroBound (|T - 1| + (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1))) := by
    rw [hSf, intervalIntegral.integral_finsetSum fun z _ =>
      (integrable_indicator_Ioo z η).intervalIntegrable]
    calc ∑ z ∈ Zf, ∫ t in T..2 * T, (Ioo (z - η) (z + η)).indicator (1 : ℝ → ℝ) t
        ≤ ∑ _z ∈ Zf, 2 * η := Finset.sum_le_sum fun z _ => integral_indicator_Ioo_le hab z hη
      _ = 2 * η * Zf.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hZfdef, ← Set.ncard_eq_toFinset_card _ hZf]
          exact hZc
  -- (f), (g)
  have hf := abs_integral_windowCosSeries_le hc2 hc T (2 * T)
  have hg := hsq
  have hl2 : 0 < 1 / (2 * l) := by positivity
  have hfY : (∫ t in T..2 * T, Y t) ≤ (∑' n, |c n|) / (π * Real.log 2) := (le_abs_self _).trans hf
  have hgY : (∫ t in T..2 * T, Y t ^ 2) ≤ T / 2 * ∑' n, c n ^ 2 + QQ := by
    have := (le_abs_self _).trans hg; linarith
  have hTc : T / 2 * |c m| ≤ |I1| + Rm := by
    have h1 : |T / 2 * c m| ≤ |I1| + |I1 - T / 2 * c m| := by
      have := abs_sub_abs_le_abs_sub (T / 2 * c m) I1
      rw [abs_sub_comm] at this; linarith
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < T / 2)] at h1
    linarith
  have hmono1 := mul_le_mul_of_nonneg_left hgY hl2.le
  have hmono2 := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ l / 2)
  linarith



/-! ## Square-root-scale rigidity -/

theorem one_add_log_pow_le_mul (B : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (1 + Real.log n) ^ B ≤ B.factorial * Real.exp 1 * n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hl := Real.log_natCast_nonneg n
  have h := Real.pow_div_factorial_le_exp (1 + Real.log n) (by linarith) B
  rw [div_le_iff₀ (by positivity), Real.exp_add, Real.exp_log hn'] at h
  linarith

theorem invLogWeight_mul_log_le (n : ℕ) :
    invLogWeight 3 n * Real.log n ≤ invLogWeight 2 n := by
  unfold invLogWeight
  have hl := Real.log_natCast_nonneg n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [pow_succ, ← mul_assoc, mul_inv, mul_assoc]
  refine mul_le_of_le_one_right (by positivity) ?_
  rw [inv_mul_le_iff₀ (by linarith)]; linarith

/-- The final real arithmetic with general mean-value bounds. -/
theorem le_of_assembly_bounds_general {x T η ε l Ka Kq Kr QQ Rm A1 S2 Zc B2V CX a0 P L2 : ℝ}
    (hT : 1 ≤ T) (hl : 0 < l) (hη : 0 < η) (hL2 : 0 < L2)
    (hass : T / 2 * x ≤ A1 / L2 +
      2 * (1 / (2 * l) * (T / 2 * S2 + QQ) + l / 2 * (2 * η * Zc)) + Rm)
    (hA1 : A1 ≤ Ka * (T * η)) (hQQ : QQ ≤ Kq * (T * η)) (hRm : Rm ≤ Kr * (T * η))
    (hS2 : S2 ≤ B2V) (hB2V : B2V / l ≤ ε / 4)
    (hZc : Zc ≤ 4 * T * (CX * (a0 * 1 - P * Real.log η)))
    (hη3 : 16 * l * (CX * (a0 * η - P * (η * Real.log η))) ≤ ε / 4)
    (hη4 : η * (2 * Ka / L2 + 2 * Kq / l + 2 * Kr) ≤ ε / 2) :
    x ≤ ε := by
  have hT2 : 0 < T / 2 := by linarith
  have e1 : A1 / L2 ≤ T / 2 * (η * (2 * Ka / L2)) := by
    rw [div_le_iff₀ hL2]
    have : T / 2 * (η * (2 * Ka / L2)) * L2 = Ka * (T * η) := by field_simp
    rw [this]; linarith
  have e2 : 2 * (1 / (2 * l) * (T / 2 * S2)) ≤ T / 2 * (ε / 4) := by
    have : 2 * (1 / (2 * l) * (T / 2 * S2)) = T / 2 * (S2 / l) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left ((div_le_div_of_nonneg_right hS2 hl.le).trans hB2V) hT2.le
  have e3 : 2 * (1 / (2 * l) * QQ) ≤ T / 2 * (η * (2 * Kq / l)) := by
    have h1 : T / 2 * (η * (2 * Kq / l)) = Kq * (T * η) / l := by field_simp
    have h2 : 2 * (1 / (2 * l) * QQ) = QQ / l := by field_simp
    rw [h1, h2]
    exact div_le_div_of_nonneg_right hQQ hl.le
  have e4 : 2 * (l / 2 * (2 * η * Zc)) ≤
      T / 2 * (16 * l * (CX * (a0 * η - P * (η * Real.log η)))) := by
    have h := mul_le_mul_of_nonneg_left hZc (by positivity : (0 : ℝ) ≤ 2 * l * η)
    have h1 : T / 2 * (16 * l * (CX * (a0 * η - P * (η * Real.log η)))) =
        2 * l * η * (4 * T * (CX * (a0 * 1 - P * Real.log η))) := by ring
    rw [h1]
    linarith
  have e5 : Rm ≤ T / 2 * (η * (2 * Kr)) := by
    have : T / 2 * (η * (2 * Kr)) = Kr * (T * η) := by ring
    rw [this]; exact hRm
  have hsum := mul_le_mul_of_nonneg_left hη4 hT2.le
  have hsum2 := mul_le_mul_of_nonneg_left hη3 hT2.le
  have eH : T / 2 * (η * (2 * Ka / L2 + 2 * Kq / l + 2 * Kr)) =
      T / 2 * (η * (2 * Ka / L2)) + T / 2 * (η * (2 * Kq / l)) + T / 2 * (η * (2 * Kr)) := by ring
  have ehass : T / 2 * x ≤ A1 / L2 + 2 * (1 / (2 * l) * (T / 2 * S2)) +
      2 * (1 / (2 * l) * QQ) + 2 * (l / 2 * (2 * η * Zc)) + Rm := by
    have : 2 * (1 / (2 * l) * (T / 2 * S2 + QQ) + l / 2 * (2 * η * Zc)) =
        2 * (1 / (2 * l) * (T / 2 * S2)) + 2 * (1 / (2 * l) * QQ) +
          2 * (l / 2 * (2 * η * Zc)) := by ring
    linarith
  have htot : T / 2 * x ≤ T / 2 * ε := by linarith
  exact le_of_mul_le_mul_left htot hT2


/-- **Square-root-scale rigidity.** A full-cone Weil-positive system with
`|lam(n) − Λ(n)| ≤ C (1 + log n)^B / √n` for all `n ≥ 2` is `Λ`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_sqrt_scale {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {C : ℝ} {B : ℕ}
    (hdev : ∀ n, 2 ≤ n →
      |lam n - ArithmeticFunction.vonMangoldt n| ≤ C * (1 + Real.log n) ^ B / Real.sqrt n) :
    ∀ m, 2 ≤ m → lam m = ArithmeticFunction.vonMangoldt m := by
  set v := normDeficit lam with hvdef
  have hv2 : ∀ n, v n ≠ 0 → 2 ≤ n := by
    intro n hn; by_contra h; exact hn (by simp only [hvdef, normDeficit, if_neg h])
  have hC : 0 ≤ C := by
    have h := hdev 2 le_rfl
    have hp : 0 < (1 + Real.log (2 : ℕ)) ^ B / Real.sqrt (2 : ℕ) := by
      have := Real.log_natCast_nonneg 2; positivity
    have h0 := (abs_nonneg _).trans h
    rw [mul_div_assoc] at h0
    exact nonneg_of_mul_nonneg_left h0 hp
  -- the pointwise bound `|v n| ≤ C (1 + log n)^B / n`
  have hvb : ∀ n, |v n| ≤ C * ((1 + Real.log n) ^ B * (n : ℝ)⁻¹) := by
    intro n
    by_cases hn : 2 ≤ n
    · simp only [hvdef, normDeficit, if_pos hn]
      have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn'
      rw [abs_div, abs_of_pos hs, abs_sub_comm, div_le_iff₀ hs]
      calc |lam n - (ArithmeticFunction.vonMangoldt n : ℝ)| ≤ C * (1 + Real.log n) ^ B / Real.sqrt n :=
            hdev n hn
        _ = C * ((1 + Real.log n) ^ B * (n : ℝ)⁻¹) * Real.sqrt n := by
            have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn'.le
            have e : (n : ℝ)⁻¹ * Real.sqrt n = (Real.sqrt n)⁻¹ := by
              have h1 : ((n : ℕ) : ℝ)⁻¹ = (Real.sqrt n * Real.sqrt n)⁻¹ := by rw [hsq]
              rw [h1, mul_inv, mul_assoc, inv_mul_cancel₀ hs.ne', mul_one]
            rw [mul_assoc, mul_assoc, e, div_eq_mul_inv, mul_assoc]
    · simp only [hvdef, normDeficit, if_neg hn, abs_zero]
      have := Real.log_natCast_nonneg n
      positivity
  set A := C * (B.factorial * Real.exp 1) with hAdef
  have hA : ∀ n, |v n| ≤ A := by
    intro n
    refine (hvb n).trans (mul_le_mul_of_nonneg_left ?_ hC)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp; positivity
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [← div_eq_mul_inv, div_le_iff₀ hn']
    exact one_add_log_pow_le_mul B hn
  have hF2 := summable_invLogWeight (D := 2) le_rfl
  have hF3 := summable_invLogWeight (D := 3) (by norm_num)
  set S2 := ∑' n, invLogWeight 2 n with hS2def
  set S3 := ∑' n, invLogWeight 3 n with hS3def
  have hS3 : 0 ≤ S3 := tsum_nonneg fun n => invLogWeight_nonneg 3 n
  have hS2 : 0 ≤ S2 := tsum_nonneg fun n => invLogWeight_nonneg 2 n
  -- `(1 + log n)^B / n ≤ invLogWeight` bounds
  have hpow : ∀ (n : ℕ) (k : ℕ), (1 + Real.log n) ^ B * (n : ℝ)⁻¹ * ((1 + Real.log n) ^ (B + k))⁻¹ =
      ((n : ℝ) * (1 + Real.log n) ^ k)⁻¹ := by
    intro n k
    have := Real.log_natCast_nonneg n
    have h1 : (0 : ℝ) < (1 + Real.log n) ^ B := by positivity
    rw [pow_add, mul_inv, mul_inv]
    field_simp
  have hZ : Summable fun n : ℕ => |v n| * ((1 + |Real.log n|) ^ (B + 2))⁻¹ := by
    refine (hF2.mul_left C).of_nonneg_of_le (fun n => by positivity) fun n => ?_
    rw [abs_of_nonneg (Real.log_natCast_nonneg n)]
    calc |v n| * ((1 + Real.log n) ^ (B + 2))⁻¹
        ≤ C * ((1 + Real.log n) ^ B * (n : ℝ)⁻¹) * ((1 + Real.log n) ^ (B + 2))⁻¹ :=
          mul_le_mul_of_nonneg_right (hvb n) (by have := Real.log_natCast_nonneg n; positivity)
      _ = C * invLogWeight 2 n := by rw [mul_assoc, hpow]; rfl
  have hsq : Summable fun n => v n ^ 2 := by
    have hK : (0 : ℝ) ≤ C ^ 2 * ((2 * B + 2).factorial * Real.exp 1) := by positivity
    refine (hF2.mul_left (C ^ 2 * ((2 * B + 2).factorial * Real.exp 1))).of_nonneg_of_le
      (fun n => sq_nonneg _) fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : v 0 = 0 := by simp [hvdef, normDeficit]
      rw [this]; simp [invLogWeight]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hl := Real.log_natCast_nonneg n
    have h1 := one_add_log_pow_le_mul (2 * B + 2) hn
    have h2 : v n ^ 2 ≤ (C * ((1 + Real.log n) ^ B * (n : ℝ)⁻¹)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hvb n) 2
    refine h2.trans ?_
    unfold invLogWeight
    rw [mul_pow, mul_pow, inv_pow, ← pow_mul]
    have e : ((1 + Real.log n) ^ (B * 2)) = (1 + Real.log n) ^ (2 * B + 2) *
        ((1 + Real.log n) ^ 2)⁻¹ := by
      rw [show 2 * B + 2 = B * 2 + 2 by ring, pow_add]
      have : (0 : ℝ) < (1 + Real.log n) ^ 2 := by positivity
      field_simp
    rw [e]
    have h3 : (1 + Real.log n) ^ (2 * B + 2) * ((1 + Real.log n) ^ 2)⁻¹ * ((n : ℝ) ^ 2)⁻¹ ≤
        (2 * B + 2).factorial * Real.exp 1 * ((n : ℝ) * (1 + Real.log n) ^ 2)⁻¹ := by
      rw [mul_inv]
      have : (1 + Real.log n) ^ (2 * B + 2) * ((1 + Real.log n) ^ 2)⁻¹ * ((n : ℝ) ^ 2)⁻¹ =
          ((1 + Real.log n) ^ (2 * B + 2) * (n : ℝ)⁻¹) * ((n : ℝ)⁻¹ * ((1 + Real.log n) ^ 2)⁻¹) := by
        rw [sq (n : ℝ), mul_inv]; ring
      rw [this]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [← div_eq_mul_inv, div_le_iff₀ hn']; exact h1
    calc C ^ 2 * ((1 + Real.log n) ^ (2 * B + 2) * ((1 + Real.log n) ^ 2)⁻¹ * ((n : ℝ) ^ 2)⁻¹)
        ≤ C ^ 2 * ((2 * B + 2).factorial * Real.exp 1 * ((n : ℝ) * (1 + Real.log n) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left h3 (sq_nonneg C)
      _ = _ := by ring
  set V := ∑' n, v n ^ 2 with hV
  have hV0 : 0 ≤ V := tsum_nonneg fun _ => sq_nonneg _
  -- constants
  have hB0 := bumpCos_zero_pos
  set B0 := bumpCos 0 with hB0def
  set J := B + 3 with hJ
  obtain ⟨KJ, hKJ0, hKJ⟩ := exists_abs_bumpCos_le J
  set K0 := C * KJ with hK0def
  have hK00 : 0 ≤ K0 := by positivity
  set cf : ℝ → ℕ → ℝ := fun η n => v n * bumpCos (η * Real.log n) with hcf
  have hcfb : ∀ η, 0 < η → η ≤ 1 → ∀ n, |cf η n| ≤ K0 * (η ^ J)⁻¹ * invLogWeight 3 n := by
    intro η hη0 hη1 n
    have hl := Real.log_natCast_nonneg n
    have h2 := hKJ (η * Real.log n)
    rw [abs_of_nonneg (by positivity : 0 ≤ η * Real.log n)] at h2
    have h3 := pow_mul_one_add_pow_le hη0 hη1 hl J
    have h5 : ((1 + η * Real.log n) ^ J)⁻¹ ≤ (η ^ J)⁻¹ * ((1 + Real.log n) ^ J)⁻¹ := by
      rw [← mul_inv]; exact inv_anti₀ (by positivity) h3
    have hb : |bumpCos (η * Real.log n)| ≤ KJ * ((η ^ J)⁻¹ * ((1 + Real.log n) ^ J)⁻¹) :=
      h2.trans (mul_le_mul_of_nonneg_left h5 hKJ0)
    simp only [hcf]
    rw [abs_mul]
    calc |v n| * |bumpCos (η * Real.log n)|
        ≤ C * ((1 + Real.log n) ^ B * (n : ℝ)⁻¹) * (KJ * ((η ^ J)⁻¹ * ((1 + Real.log n) ^ J)⁻¹)) :=
          mul_le_mul (hvb n) hb (abs_nonneg _) (by positivity)
      _ = K0 * (η ^ J)⁻¹ * ((1 + Real.log n) ^ B * (n : ℝ)⁻¹ * ((1 + Real.log n) ^ (B + 3))⁻¹) := by
          rw [hK0def, hJ]; ring
      _ = K0 * (η ^ J)⁻¹ * invLogWeight 3 n := by rw [hpow]; rfl
  have hcs : ∀ η, Summable (fun n => |cf η n|) → ∑' n, cf η n ^ 2 ≤ B0 ^ 2 * V := by
    intro η _
    have hpt : ∀ n, cf η n ^ 2 ≤ B0 ^ 2 * v n ^ 2 := by
      intro n
      simp only [hcf]
      rw [mul_pow, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      rw [← sq_abs, ← sq_abs B0]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_bumpCos_le _).trans (le_abs_self _)) 2
    calc ∑' n, cf η n ^ 2 ≤ ∑' n, B0 ^ 2 * v n ^ 2 :=
          ((hsq.mul_left _).of_nonneg_of_le (fun _ => sq_nonneg _) hpt).tsum_le_tsum hpt
            (hsq.mul_left _)
      _ = B0 ^ 2 * V := tsum_mul_left
  have hU0 : ∀ a, 0 ≤ unitZeroBound a := fun a =>
    le_trans (Nat.cast_nonneg _) (realZeroSet_unit a).2
  have hmain : ∀ m, v m = 0 := by
    intro m
    by_contra hm
    have hm2 := hv2 m hm
    have key : ∀ ε > 0, |v m| * (B0 / 2) ≤ ε := by
      intro ε hε
      set l := 4 * (B0 ^ 2 * V + 1) / ε with hl
      have hl0 : 0 < l := by positivity
      set CX := 8 * (1 + π ^ 2) with hCX
      set a0 := |xiLineTwoLogDerivConstant| + Real.log 50 with ha0
      set p : ℕ := 2 * J + 1 with hp
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlm : 0 ≤ Real.log m := Real.log_natCast_nonneg m
      set Ka := K0 * S3 with hKa
      set Kq := K0 ^ 2 * ((2 + 3 * S3) * S3 + S2) with hKq
      set Kr := K0 * (2 + 3 * S3 + Real.log m) with hKr
      set H := 2 * Ka / (π * Real.log 2) + 2 * Kq / l + 2 * Kr with hH
      have hH0 : 0 ≤ H := by positivity
      have hev1 : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η ∧ η ≤ 1 := by
        filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with η hη
        exact ⟨hη.1, hη.2⟩
      have hev2 : ∀ᶠ η in 𝓝[>] (0 : ℝ), B0 / 2 < bumpCos (η * Real.log m) := by
        have ht : Tendsto (fun η : ℝ => bumpCos (η * Real.log m)) (𝓝 0) (𝓝 B0) := by
          have hc : Continuous fun η : ℝ => bumpCos (η * Real.log m) :=
            continuous_bumpCos.comp (continuous_id.mul continuous_const)
          have := hc.tendsto 0
          simpa [hB0def] using this
        exact nhdsWithin_le_nhds (ht.eventually_const_lt (by linarith))
      have hev3 : ∀ᶠ η in 𝓝[>] (0 : ℝ),
          16 * l * (CX * (a0 * η - (p : ℝ) * (η * Real.log η))) ≤ ε / 4 := by
        have ht : Tendsto (fun η : ℝ => 16 * l * (CX * (a0 * η - (p : ℝ) * (η * Real.log η))))
            (𝓝 0) (𝓝 0) := by
          have h1 : Tendsto (fun η : ℝ => η * Real.log η) (𝓝 0) (𝓝 0) := by
            have := Real.continuous_mul_log.tendsto 0; simpa using this
          have := (((tendsto_id.const_mul a0).sub (h1.const_mul (p : ℝ))).const_mul CX).const_mul
            (16 * l)
          simpa using this
        exact nhdsWithin_le_nhds (ht.eventually_le_const (by positivity))
      have hev4 : ∀ᶠ η in 𝓝[>] (0 : ℝ), η * H ≤ ε / 2 := by
        have ht : Tendsto (fun η : ℝ => η * H) (𝓝 0) (𝓝 0) := by
          have := (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const H; simpa using this
        exact nhdsWithin_le_nhds (ht.eventually_le_const (by positivity))
      obtain ⟨η, hηall⟩ := (((hev1.and hev2).and hev3).and hev4).exists
      obtain ⟨⟨⟨⟨hη0, hη1⟩, hη2⟩, hη3⟩, hη4⟩ := hηall
      set y := η⁻¹ with hy
      have hy1 : 1 ≤ y := (one_le_inv₀ hη0).mpr hη1
      set T := y ^ p with hT
      have hT1 : 1 ≤ T := one_le_pow₀ hy1
      set Kp := K0 * (η ^ J)⁻¹ with hKp
      have hKp0 : 0 ≤ Kp := by positivity
      -- summability and the kernel bounds
      have hcs1 : Summable fun n => |cf η n| :=
        (hF3.mul_left Kp).of_nonneg_of_le (fun _ => abs_nonneg _) (hcfb η hη0 hη1)
      have hA1 : ∑' n, |cf η n| ≤ Kp * S3 := by
        rw [← tsum_mul_left]
        exact hcs1.tsum_le_tsum (hcfb η hη0 hη1) (hF3.mul_left Kp)
      have hRm : ∀ k, 2 ≤ k → Summable (fun n => |cf η n| * intLogKernel n k) ∧
          ∑' n, |cf η n| * intLogKernel n k ≤ Kp * (2 + 3 * S3 + Real.log k) := by
        intro k hk
        obtain ⟨hs, hb⟩ := tsum_invLogWeight_mul_intLogKernel_le (D := 3) (by norm_num) hk
        have hker0 : ∀ n, 0 ≤ intLogKernel n k := fun n => by
          unfold intLogKernel; split_ifs <;> positivity
        have hpt : ∀ n, |cf η n| * intLogKernel n k ≤ Kp * (invLogWeight 3 n * intLogKernel n k) :=
          fun n => by
            rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hcfb η hη0 hη1 n) (hker0 n)
        have hs' := (hs.mul_left Kp).of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (hker0 n)) hpt
        refine ⟨hs', (hs'.tsum_le_tsum hpt (hs.mul_left Kp)).trans ?_⟩
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left hb hKp0
      set R : ℕ → ℝ := fun k => Kp * (2 + 3 * S3 + Real.log k) with hRdef
      have hext : ∀ k, cf η k ≠ 0 → ∀ a b : ℝ,
          |(∫ t in a..b, windowCosSeries (cf η) t * Real.cos (2 * π * t * Real.log k)) -
            (b - a) / 2 * cf η k| ≤ R k := by
        intro k hk a b
        have hk2 : 2 ≤ k := hv2 k (left_ne_zero_of_mul hk)
        obtain ⟨hs, hb⟩ := hRm k hk2
        exact (abs_integral_windowCosSeries_mul_cos_sub_le_of_bound hcs1 a b
          (fun n => abs_meanKernel_le_intLogKernel (c := cf η)
            (fun n hn => hv2 n (left_ne_zero_of_mul hn)) hk2 a b n) hs).trans hb
      have hRs : Summable fun k => |cf η k| * R k := by
        have hpt : ∀ k, |cf η k| * R k ≤ Kp ^ 2 * ((2 + 3 * S3) * invLogWeight 3 k +
            invLogWeight 2 k) := by
          intro k
          have h1 := hcfb η hη0 hη1 k
          have h2 := invLogWeight_mul_log_le k
          have hl := Real.log_natCast_nonneg k
          have hw := invLogWeight_nonneg 3 k
          calc |cf η k| * R k ≤ (Kp * invLogWeight 3 k) * (Kp * (2 + 3 * S3 + Real.log k)) :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = Kp ^ 2 * ((2 + 3 * S3) * invLogWeight 3 k + invLogWeight 3 k * Real.log k) := by
                ring
            _ ≤ _ := by gcongr
        exact ((hF3.mul_left (2 + 3 * S3)).add hF2).mul_left (Kp ^ 2) |>.of_nonneg_of_le
          (fun k => mul_nonneg (abs_nonneg _) (by positivity)) hpt
      have hQQ : ∑' k, |cf η k| * R k ≤ Kp ^ 2 * ((2 + 3 * S3) * S3 + S2) := by
        have hpt : ∀ k, |cf η k| * R k ≤ Kp ^ 2 * ((2 + 3 * S3) * invLogWeight 3 k +
            invLogWeight 2 k) := by
          intro k
          have h1 := hcfb η hη0 hη1 k
          have h2 := invLogWeight_mul_log_le k
          have hl := Real.log_natCast_nonneg k
          have hw := invLogWeight_nonneg 3 k
          calc |cf η k| * R k ≤ (Kp * invLogWeight 3 k) * (Kp * (2 + 3 * S3 + Real.log k)) :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = Kp ^ 2 * ((2 + 3 * S3) * invLogWeight 3 k + invLogWeight 3 k * Real.log k) := by
                ring
            _ ≤ _ := by gcongr
        have hsum := ((hF3.mul_left (2 + 3 * S3)).add hF2).mul_left (Kp ^ 2)
        calc ∑' k, |cf η k| * R k ≤ ∑' k, Kp ^ 2 * ((2 + 3 * S3) * invLogWeight 3 k +
              invLogWeight 2 k) := hRs.tsum_le_tsum hpt hsum
          _ = Kp ^ 2 * ((2 + 3 * S3) * S3 + S2) := by
              rw [tsum_mul_left, (hF3.mul_left _).tsum_add hF2, tsum_mul_left]
      have hsqb := abs_integral_windowCosSeries_sq_sub_le_of_bound hcs1 T (2 * T)
        (fun k hk => hext k hk T (2 * T)) hRs
      rw [show 2 * T - T = T by ring] at hsqb
      have hbm : 0 < bumpCos (η * Real.log m) := by linarith
      have hcm : cf η m ≠ 0 := by simp only [hcf]; exact mul_ne_zero hm hbm.ne'
      have hext' := hext m hcm T (2 * T)
      rw [show 2 * T - T = T by ring] at hext'
      have hpos : ∀ t, T ≤ t → t ≤ 2 * T → (∀ ξ, |ξ - t| < η → phiFourierReal ξ ≠ 0) →
          0 ≤ windowCosSeries (cf η) t := by
        intro t _ _ hfree
        have := localized_deviation_nonneg hW hA hZ hη0 (ξ₀ := t) hfree
        simpa [windowCosSeries, hcf] using this
      have hc2' : ∀ n, cf η n ≠ 0 → 2 ≤ n := fun n hn => hv2 n (left_ne_zero_of_mul hn)
      have hass := half_mul_abs_le_of_zeroFree_of_bounds hc2' hcs1 hT1 hl0 hη0 hη1 hpos hext' hsqb
      -- sizes
      have hyJ : (η ^ J)⁻¹ = y ^ J := by rw [hy, inv_pow]
      have hTη : T * η = y ^ (2 * J) := by
        rw [hT, hp, pow_succ, mul_assoc, hy, inv_mul_cancel₀ hη0.ne', mul_one]
      have hyJ2 : y ^ J ≤ y ^ (2 * J) := pow_le_pow_right₀ hy1 (by omega)
      have hKpT : Kp ≤ K0 * (T * η) := by
        rw [hKp, hyJ, hTη]; exact mul_le_mul_of_nonneg_left hyJ2 hK00
      have hKp2 : Kp ^ 2 ≤ K0 ^ 2 * (T * η) := by
        rw [hKp, hyJ, hTη, mul_pow, ← pow_mul, mul_comm J 2]
      have hA1' : ∑' n, |cf η n| ≤ Ka * (T * η) := by
        calc ∑' n, |cf η n| ≤ Kp * S3 := hA1
          _ ≤ K0 * (T * η) * S3 := mul_le_mul_of_nonneg_right hKpT hS3
          _ = Ka * (T * η) := by rw [hKa]; ring
      have hQQ' : ∑' k, |cf η k| * R k ≤ Kq * (T * η) := by
        have hq0 : 0 ≤ (2 + 3 * S3) * S3 + S2 := by positivity
        calc ∑' k, |cf η k| * R k ≤ Kp ^ 2 * ((2 + 3 * S3) * S3 + S2) := hQQ
          _ ≤ K0 ^ 2 * (T * η) * ((2 + 3 * S3) * S3 + S2) := mul_le_mul_of_nonneg_right hKp2 hq0
          _ = Kq * (T * η) := by rw [hKq]; ring
      have hRm' : R m ≤ Kr * (T * η) := by
        have hr0 : 0 ≤ 2 + 3 * S3 + Real.log m := by positivity
        calc R m = Kp * (2 + 3 * S3 + Real.log m) := rfl
          _ ≤ K0 * (T * η) * (2 + 3 * S3 + Real.log m) := mul_le_mul_of_nonneg_right hKpT hr0
          _ = Kr * (T * η) := by rw [hKr]; ring
      have hS2' := hcs η hcs1
      -- the zero count
      have hceil : (⌈T⌉₊ : ℝ) < T + 1 := Nat.ceil_lt_add_one (by linarith)
      have hN1 : (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1) ≤ 4 * T := by push_cast; linarith
      have hU1 : unitZeroBound (|T - 1| + (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1)) ≤ unitZeroBound (5 * T) := by
        refine unitZeroBound_le_of_le (by linarith) ?_
        rw [abs_of_nonneg (by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T - 1)]; positivity)]
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T - 1)]
        push_cast; linarith
      have hU5 := unitZeroBound_five_mul_le hT1
      have hlogT : Real.log T = -((p : ℝ) * Real.log η) := by
        rw [hT, Real.log_pow, hy, Real.log_inv]; ring
      have hZc : (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1) * unitZeroBound (|T - 1| + (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1))
          ≤ 4 * T * (CX * (a0 * 1 - (p : ℝ) * Real.log η)) := by
        have hUpos := hU0 (|T - 1| + (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1))
        calc (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1) * unitZeroBound (|T - 1| + (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1))
            ≤ 4 * T * unitZeroBound (5 * T) :=
              mul_le_mul hN1 hU1 hUpos (by linarith)
          _ ≤ 4 * T * (CX * (a0 + Real.log T)) := mul_le_mul_of_nonneg_left hU5 (by linarith)
          _ = 4 * T * (CX * (a0 * 1 - (p : ℝ) * Real.log η)) := by rw [hlogT]; ring
      have hB2V : B0 ^ 2 * V / l ≤ ε / 4 := by
        rw [hl]; exact div_four_mul_add_one_div_le (by positivity) hε
      have hcfm : |cf η m| ≤ ε :=
        le_of_assembly_bounds_general (x := |cf η m|) (T := T) (η := η) (ε := ε) (l := l)
          (Ka := Ka) (Kq := Kq) (Kr := Kr) (QQ := ∑' k, |cf η k| * R k) (Rm := R m)
          (A1 := ∑' n, |cf η n|) (S2 := ∑' n, cf η n ^ 2)
          (Zc := (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1) * unitZeroBound (|T - 1| + (((⌈T⌉₊ + 1 : ℕ) : ℝ) + 1)))
          (B2V := B0 ^ 2 * V) (CX := CX) (a0 := a0) (P := (p : ℝ)) (L2 := π * Real.log 2)
          hT1 hl0 hη0 (by positivity) hass hA1' hQQ' hRm' hS2' hB2V hZc hη3 hη4
      calc |v m| * (B0 / 2) ≤ |v m| * |bumpCos (η * Real.log m)| :=
            mul_le_mul_of_nonneg_left (by rw [abs_of_pos hbm]; linarith) (abs_nonneg _)
        _ = |cf η m| := by simp only [hcf, abs_mul]
        _ ≤ ε := hcfm
    have h0 : |v m| * (B0 / 2) ≤ 0 := le_of_forall_pos_le_add fun ε hε => by
      have := key ε hε; linarith
    have : |v m| * (B0 / 2) = 0 := le_antisymm h0 (by positivity)
    rcases mul_eq_zero.mp this with h | h
    · exact hm (abs_eq_zero.mp h)
    · linarith
  intro m hm2
  have hv := hmain m
  simp only [hvdef, normDeficit, if_pos hm2] at hv
  have hsq0 : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < m))).ne'
  rw [div_eq_zero_iff, sub_eq_zero] at hv
  rcases hv with hv | hv
  · exact hv.symm
  · exact absurd hv hsq0


/-- **RH as a square-root-scale deformation problem.** -/
theorem riemannHypothesis_iff_exists_weilPositiveFull_sqrt_scale :
    RiemannHypothesis ↔ ∃ lam : ℕ → ℝ, WeilPositiveFull lam ∧ ∃ C : ℝ, ∃ B : ℕ,
      ∀ n, 2 ≤ n →
        |lam n - ArithmeticFunction.vonMangoldt n| ≤ C * (1 + Real.log n) ^ B / Real.sqrt n := by
  constructor
  · intro hRH
    refine ⟨_, riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH, 0, 0, fun n _ => ?_⟩
    simp
  · rintro ⟨lam, hW, C, B, hdev⟩
    have h := eq_vonMangoldt_of_weilPositiveFull_of_sqrt_scale hW hdev
    refine riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr fun f hf hfc => ?_
    rw [weilFullFunctional_congr (lam' := lam) (fun n hn => (h n hn).symm)]
    exact hW f hf hfc

end

end RHTower
