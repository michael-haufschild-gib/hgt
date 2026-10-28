import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheArchimedeanCrossEnergyIsOneSided
import GaloisForLFunctions.ArithmeticLorentzianGeometry.ThePoleDefectControlsTheVRow

/-!
# The sharp multiplicative Hardy inequality

`ThePoleDefectControlsTheVRow` proves `(Σ_{n ≤ N} √n x_n)² ≤ C_H (N²/log N)(D_N(x) + |x|²)` with
`C_H = 48B² + 51 ≈ 1443`. The two weights it bounds have sharp sizes. The edge weight satisfies
`Σ_{n ≤ N} n/log n ~ N²/(2 log N)`, and with Chebyshev's constant the up-row weight satisfies
`Σ_m m R_m² ≤ (B_ψ² + o(1)) N²/log N`. The split that loses the constants is `mt ≷ √N`, where
`log(mt) ≥ ½ log N`. Splitting at `N^b`, `b < 1`, instead gives `log(mt) ≥ b log N` above and an
`O(N^b)` count below.

* **The split** (`log_gt_of_rpow_lt`): `n > N^b ⇒ log n > b log N`.
* **The edge weight** (`sum_div_log_le_split`):
  `Σ_{n ≤ N} n/log n ≤ N(N + 1)/(2b log N) + N·N^b/log 2`.
* **The up-rows** (`mul_upRow_le_split`, `sum_mul_upRow_sq_le_split`):
  `m R_m ≤ B_ψ N/(b log N) + N^b` and `Σ_m m R_m² ≤ (B_ψ N/(b log N) + N^b)²(1 + log N)`.
* **The sharp Hardy inequality** (`sq_vRow_le_split`): for `θ, ζ > 0`,
  `(Σ √n x_n)² ≤ (1 + θ) E_N D_N(x) + (1 + 1/θ)((1 + ζ) U_N + 1 + 1/ζ) |x|²`, with `E_N`, `U_N`
  the two weights above. Eventually in `N`, `E_N ≤ (1/(2b) + η) N²/log N` and
  `U_N ≤ (B_ψ²/b² + η) N²/log N` (`eventually_hardyWeights_le`).
-/

noncomputable section

open Finset Filter Asymptotics
open scoped ArithmeticFunction.vonMangoldt Topology

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-! ### The split at `N^b` -/

theorem log_gt_of_rpow_lt {N n : ℕ} (hN : 1 ≤ N) {b : ℝ} (h : (N : ℝ) ^ b < n) :
    b * Real.log N < Real.log n := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h0 : 0 < (N : ℝ) ^ b := Real.rpow_pos_of_pos hN0 b
  have := Real.log_lt_log h0 h
  rwa [Real.log_rpow hN0] at this

/-- Gauss: `Σ_{n ≤ N} n = N(N + 1)/2`. -/
theorem sum_Icc_natCast (N : ℕ) : ∑ n ∈ Icc 1 N, (n : ℝ) = N * (N + 1) / 2 := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast; ring

/-- **The edge weight**: `Σ_{n ≤ N} n/log n ≤ N(N + 1)/(2b log N) + N·N^b/log 2` for `0 < b`. -/
theorem sum_div_log_le_split {N : ℕ} (hN : 2 ≤ N) {b : ℝ} (hb0 : 0 < b) :
    ∑ n ∈ Icc 1 N, (n : ℝ) / Real.log n ≤
      N * (N + 1) / (2 * b * Real.log N) + N * ((N : ℝ) ^ b / Real.log 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNb : 0 ≤ (N : ℝ) ^ b / Real.log 2 := by positivity
  have hterm : ∀ n ∈ Icc 1 N, (n : ℝ) / Real.log n ≤
      (n : ℝ) / (b * Real.log N) + (N : ℝ) ^ b / Real.log 2 := fun n hn => by
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    have h0 : 0 ≤ (n : ℝ) / (b * Real.log N) := by positivity
    by_cases hns : (N : ℝ) ^ b < n
    · have hlog := log_gt_of_rpow_lt (by omega) hns
      have : (n : ℝ) / Real.log n ≤ (n : ℝ) / (b * Real.log N) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg n) (by positivity) hlog.le
      linarith
    · push Not at hns
      rcases eq_or_ne n 1 with rfl | h1
      · simp; positivity
      · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
        have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
        have : (n : ℝ) / Real.log n ≤ (N : ℝ) ^ b / Real.log 2 := by
          rw [div_le_div_iff₀ (by linarith) hl2]
          nlinarith [Real.rpow_nonneg hN0.le b]
        linarith
  calc ∑ n ∈ Icc 1 N, (n : ℝ) / Real.log n
      ≤ ∑ n ∈ Icc 1 N, ((n : ℝ) / (b * Real.log N) + (N : ℝ) ^ b / Real.log 2) :=
        sum_le_sum hterm
    _ = (∑ n ∈ Icc 1 N, (n : ℝ)) / (b * Real.log N) + N * ((N : ℝ) ^ b / Real.log 2) := by
        rw [sum_add_distrib, ← sum_div, sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
    _ = N * (N + 1) / (2 * b * Real.log N) + N * ((N : ℝ) ^ b / Real.log 2) := by
        rw [sum_Icc_natCast]; field_simp

/-- **The up-rows at the split**: `m R_m ≤ B_ψ N/(b log N) + N^b`. -/
theorem mul_upRow_le_split {N m : ℕ} (hN : 2 ≤ N) (hm : m ∈ Icc 1 N) {b : ℝ} (hb0 : 0 < b) :
    (m : ℝ) * upRow N m ≤ psiConstant * N / (b * Real.log N) + (N : ℝ) ^ b := by
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  set s := ⌊(N : ℝ) ^ b⌋₊
  have hs : (s : ℝ) ≤ (N : ℝ) ^ b := Nat.floor_le (Real.rpow_nonneg hN0.le b)
  have hterm : ∀ t ∈ Icc 1 (N / m), Λ t / Real.log ((m : ℝ) * t) ≤
      Λ t / (b * Real.log N) + (if m * t ≤ s then 1 else 0) := fun t ht => by
    have ht1 := (Finset.mem_Icc.mp ht).1
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := t)
    have hlog0 := log_mul_nonneg hm1 ht1
    split_ifs with hst
    · have h2 : 0 ≤ Λ t / (b * Real.log N) := by positivity
      have h1 : Λ t / Real.log ((m : ℝ) * t) ≤ 1 := by
        rcases hlog0.lt_or_eq with hpos | hzero
        · rw [div_le_one hpos]
          refine ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log
            (by exact_mod_cast (show 0 < t by omega)) ?_)
          have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
          have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
          nlinarith
        · rw [← hzero, div_zero]; norm_num
      linarith
    · push Not at hst
      have hlt : (N : ℝ) ^ b < ((m * t : ℕ) : ℝ) := by
        have : (s : ℝ) + 1 ≤ ((m * t : ℕ) : ℝ) := by exact_mod_cast hst
        have := Nat.lt_floor_add_one ((N : ℝ) ^ b)
        linarith
      have hlog := log_gt_of_rpow_lt (by omega) hlt
      push_cast at hlog
      rw [add_zero]
      exact div_le_div_of_nonneg_left hΛ (by positivity) hlog.le
  have hsum : upRow N m ≤ 1 / (b * Real.log N) * ∑ t ∈ Icc 1 (N / m), Λ t +
      ∑ t ∈ Icc 1 (N / m), (if m * t ≤ s then (1 : ℝ) else 0) := by
    unfold upRow
    refine (sum_le_sum hterm).trans (le_of_eq ?_)
    rw [sum_add_distrib, mul_sum]
    congr 1
    exact sum_congr rfl fun t _ => by ring
  have hq1 : (1 : ℝ) ≤ ((N / m : ℕ) : ℝ) := by exact_mod_cast Nat.div_pos hmN hm1
  have hcheb : ∑ t ∈ Icc 1 (N / m), Λ t ≤ psiConstant * ((N / m : ℕ) : ℝ) := by
    rw [sum_vonMangoldt_Icc_eq_psi]; exact psi_le_psiConstant hq1
  have hdiv : (m : ℝ) * ((N / m : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.mul_div_le N m
  have hcount : (m : ℝ) * ∑ t ∈ Icc 1 (N / m), (if m * t ≤ s then (1 : ℝ) else 0) ≤ s := by
    rw [← Finset.sum_filter, sum_const, nsmul_eq_mul, mul_one]
    have hsub : (Icc 1 (N / m)).filter (fun t => m * t ≤ s) ⊆ Icc 1 (s / m) := fun t h => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp h
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp h1).1,
        (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith [mul_comm m t])⟩
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at hc
    have : (m : ℝ) * (((Icc 1 (N / m)).filter (fun t => m * t ≤ s)).card : ℝ) ≤ m * (s / m : ℕ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hc) hm0.le
    exact this.trans (by exact_mod_cast Nat.mul_div_le s m)
  have hB := psiConstant_pos
  have h1 : (m : ℝ) * ∑ t ∈ Icc 1 (N / m), Λ t ≤ psiConstant * N :=
    calc (m : ℝ) * ∑ t ∈ Icc 1 (N / m), Λ t ≤ m * (psiConstant * (N / m : ℕ)) :=
          mul_le_mul_of_nonneg_left hcheb hm0.le
      _ = psiConstant * (m * (N / m : ℕ)) := by ring
      _ ≤ psiConstant * N := mul_le_mul_of_nonneg_left hdiv hB.le
  have h2 : 1 / (b * Real.log N) * ((m : ℝ) * ∑ t ∈ Icc 1 (N / m), Λ t) ≤
      1 / (b * Real.log N) * (psiConstant * N) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 := mul_le_mul_of_nonneg_left hsum hm0.le
  have e1 : (m : ℝ) * (1 / (b * Real.log N) * ∑ t ∈ Icc 1 (N / m), Λ t +
      ∑ t ∈ Icc 1 (N / m), (if m * t ≤ s then (1 : ℝ) else 0)) =
      1 / (b * Real.log N) * ((m : ℝ) * ∑ t ∈ Icc 1 (N / m), Λ t) +
        m * ∑ t ∈ Icc 1 (N / m), (if m * t ≤ s then (1 : ℝ) else 0) := by ring
  have e2 : 1 / (b * Real.log N) * (psiConstant * N) = psiConstant * N / (b * Real.log N) := by
    ring
  rw [e1] at h3
  linarith

/-- **The up-row weight**: `Σ_m m R_m² ≤ (B_ψ N/(b log N) + N^b)²(1 + log N)`. -/
theorem sum_mul_upRow_sq_le_split {N : ℕ} (hN : 2 ≤ N) {b : ℝ} (hb0 : 0 < b) :
    ∑ m ∈ Icc 1 N, (m : ℝ) * upRow N m ^ 2 ≤
      (psiConstant * N / (b * Real.log N) + (N : ℝ) ^ b) ^ 2 * (1 + Real.log N) := by
  set R := psiConstant * N / (b * Real.log N) + (N : ℝ) ^ b
  have hharm : ∑ m ∈ Icc 1 N, (1 : ℝ) / m ≤ 1 + Real.log N := by
    have h := harmonic_le_one_add_log N
    simp only [_root_.harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
    simpa only [one_div] using h
  have hterm : ∀ m ∈ Icc 1 N, (m : ℝ) * upRow N m ^ 2 ≤ R ^ 2 * (1 / m) := fun m hm => by
    have hm1 := (Finset.mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have h1 := mul_upRow_le_split hN hm hb0
    have h0 : 0 ≤ (m : ℝ) * upRow N m := mul_nonneg hm0.le (upRow_nonneg hm1)
    have hsq : ((m : ℝ) * upRow N m) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ h0 h1 2
    rw [show (m : ℝ) * upRow N m ^ 2 = ((m : ℝ) * upRow N m) ^ 2 * (1 / m) by field_simp]
    exact mul_le_mul_of_nonneg_right hsq (by positivity)
  calc ∑ m ∈ Icc 1 N, (m : ℝ) * upRow N m ^ 2
      ≤ ∑ m ∈ Icc 1 N, R ^ 2 * (1 / m) := sum_le_sum hterm
    _ = R ^ 2 * ∑ m ∈ Icc 1 N, (1 : ℝ) / m := by rw [mul_sum]
    _ ≤ R ^ 2 * (1 + Real.log N) := mul_le_mul_of_nonneg_left hharm (sq_nonneg _)

/-! ### The sharp Hardy inequality -/

/-- The edge weight `E_N = N(N + 1)/(2b log N) + N·N^b/log 2`. -/
def edgeWeight (N : ℕ) (b : ℝ) : ℝ :=
  N * (N + 1) / (2 * b * Real.log N) + N * ((N : ℝ) ^ b / Real.log 2)

/-- The up-row weight `U_N = (B_ψ N/(b log N) + N^b)²(1 + log N)`. -/
def upWeight (N : ℕ) (b : ℝ) : ℝ :=
  (psiConstant * N / (b * Real.log N) + (N : ℝ) ^ b) ^ 2 * (1 + Real.log N)

/-- **The sharp multiplicative Hardy inequality.** For `N ≥ 2`, `b, θ, ζ > 0`,
`(Σ √n x_n)² ≤ (1 + θ) E_N D_N(x) + (1 + 1/θ)((1 + ζ) U_N + 1 + 1/ζ) |x|²`. -/
theorem sq_vRow_le_split {N : ℕ} (hN : 2 ≤ N) {b : ℝ} (hb0 : 0 < b) {θ ζ : ℝ} (hθ : 0 < θ)
    (hζ : 0 < ζ) (x : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, Real.sqrt n * x n) ^ 2 ≤
      (1 + θ) * edgeWeight N b * poleDefect N x +
        (1 + 1 / θ) * ((1 + ζ) * upWeight N b + (1 + 1 / ζ)) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  set D := poleDefect N x
  set X := ∑ n ∈ Icc 1 N, x n ^ 2
  have hD := poleDefect_nonneg N x
  have hX : 0 ≤ X := sum_nonneg fun _ _ => sq_nonneg _
  have hx1 : x 1 ^ 2 ≤ X :=
    single_le_sum (f := fun n => x n ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  have hE := (sq_edgePart_le N x).trans
    (mul_le_mul_of_nonneg_left (sum_div_log_le_split hN hb0) hD)
  have hU := (sq_upPart_le N x).trans
    (mul_le_mul_of_nonneg_left (sum_mul_upRow_sq_le_split hN hb0) hX)
  rw [vRow_eq (by omega) x]
  set e := edgePart N x
  set u := ∑ m ∈ Icc 1 N, Real.sqrt m * x m * upRow N m
  -- `(e + v)² ≤ (1 + θ)e² + (1 + 1/θ)v²` and `(x₁ + u)² ≤ (1 + ζ)u² + (1 + 1/ζ)x₁²`
  have hsplit : ∀ {c : ℝ}, 0 < c → ∀ p q : ℝ, (p + q) ^ 2 ≤ (1 + c) * p ^ 2 + (1 + 1 / c) * q ^ 2 :=
    fun {c} hc p q => by
      have h : (1 + c) * p ^ 2 + (1 + 1 / c) * q ^ 2 - (p + q) ^ 2 = (c * p - q) ^ 2 / c := by
        field_simp; ring
      have : 0 ≤ (c * p - q) ^ 2 / c := div_nonneg (sq_nonneg _) hc.le
      linarith
  have h1 := hsplit hθ e (x 1 + u)
  have h2 := hsplit hζ u (x 1)
  rw [show x 1 + e + u = e + (x 1 + u) by ring]
  have hθ' : 0 ≤ 1 + 1 / θ := by positivity
  have hEw : e ^ 2 ≤ edgeWeight N b * D := by
    simp only [edgeWeight]; linarith [mul_comm D (N * (N + 1) / (2 * b * Real.log N) +
      N * ((N : ℝ) ^ b / Real.log 2))]
  have hUw : u ^ 2 ≤ upWeight N b * X := by
    simp only [upWeight]; linarith [mul_comm X ((psiConstant * N / (b * Real.log N) +
      (N : ℝ) ^ b) ^ 2 * (1 + Real.log N))]
  have h3 : (x 1 + u) ^ 2 ≤ ((1 + ζ) * upWeight N b + (1 + 1 / ζ)) * X := by
    have hζ' : 0 ≤ 1 + 1 / ζ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hUw (by linarith : (0 : ℝ) ≤ 1 + ζ),
      mul_le_mul_of_nonneg_left hx1 hζ']
  have h4 := mul_le_mul_of_nonneg_left h3 hθ'
  have h5 := mul_le_mul_of_nonneg_left hEw (by linarith : (0 : ℝ) ≤ 1 + θ)
  nlinarith

end GaloisForLFunctions.ArithmeticLorentzianGeometry
