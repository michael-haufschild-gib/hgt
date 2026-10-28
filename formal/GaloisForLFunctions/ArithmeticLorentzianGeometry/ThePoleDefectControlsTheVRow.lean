import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheDeficitOfThePrimeFormIsADirichletEnergy
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheTiltedPrimeRows

/-!
# The pole defect controls the `V`-row

The two pole rows of the atoms are `n^{−1/2}` (the `H`-row, the pole vector) and `n^{1/2}` (the
`V`-row). Cauchy–Schwarz bounds the `V`-row only by `(Σ_{n ≤ N} √n x_n)² ≤ N²|x|²`, which costs a
factor `log N` against the pole term: the root-logarithm barrier of a uniform margin
(`TheUniformMarginPaysThePoleOnlyUpToARootLogarithm`). The pole defect
`D_N(x) = Σ_{mt ≤ N} Λ(t)(x_{mt} − x_m/√t)²` — the Dirichlet energy of the pole relations, the
deficit of the prime form below its sharp counterterm (RenormalizedArithmeticPotentialTheory) —
recovers that logarithm.

* **The multiplicative Hardy inequality** (`sq_vRow_le`): for `N ≥ 3`,
  `(Σ_{n ≤ N} √n x_n)² ≤ C_H (N²/log N)(D_N(x) + |x|²)`, `C_H = 48B² + 51`, `B = log 4 + 4`.

Proof. Since `Σ_{t ∣ n} Λ(t) = log n`, every `n ≥ 2` distributes `√n x_n` over the edges
`n/t → n` with weights `Λ(t)/log n`, and along an edge
`√(mt) x_{mt} = √(mt)(x_{mt} − x_m/√t) + √m x_m` (`vRow_eq`). The first part is a sum of edge
defects, bounded by Cauchy–Schwarz through `D_N · Σ_n n/log n` (`sq_edgePart_le`); the second is
`Σ_m √m x_m R_m` with the up-row `R_m = Σ_{t ≤ N/m} Λ(t)/log(mt)`, and
`m R_m ≤ 2BN/log N + √N` by Chebyshev's bound and the split `mt ≷ √N` (`mul_upRow_le`). Both
parts are `O(N²/log N)` (`sum_div_log_le`, `sum_mul_upRow_sq_le`).
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- The up-row `R_m = Σ_{t ≤ N/m} Λ(t)/log(mt)`. -/
def upRow (N m : ℕ) : ℝ := ∑ t ∈ Icc 1 (N / m), Λ t / Real.log ((m : ℝ) * t)

/-- The edge part `Σ_{mt ≤ N} (Λ(t)/log(mt)) √(mt) (x_{mt} − x_m/√t)`. -/
def edgePart (N : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m),
    Λ t / Real.log ((m : ℝ) * t) * Real.sqrt ((m : ℝ) * t) * (x (m * t) - x m / Real.sqrt t)

theorem log_mul_nonneg {m t : ℕ} (hm : 1 ≤ m) (ht : 1 ≤ t) : 0 ≤ Real.log ((m : ℝ) * t) :=
  Real.log_nonneg (by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have : (1 : ℝ) ≤ t := by exact_mod_cast ht
    nlinarith)

theorem upRow_nonneg {N m : ℕ} (hm : 1 ≤ m) : 0 ≤ upRow N m :=
  sum_nonneg fun _ ht => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (log_mul_nonneg hm (Finset.mem_Icc.mp ht).1)

/-! ### The decomposition -/

/-- **The `V`-row along the edges**: `Σ √n x_n = x_1 + (edge defects) + Σ_m √m x_m R_m`. -/
theorem vRow_eq {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, Real.sqrt n * x n =
      x 1 + edgePart N x + ∑ m ∈ Icc 1 N, Real.sqrt m * x m * upRow N m := by
  -- `√n x_n = [n = 1] x_1 + Σ_{t ∣ n} (Λ(t)/log n) √n x_n`
  have h1 : ∀ n ∈ Icc 1 N, Real.sqrt n * x n = (if n = 1 then x 1 else 0) +
      ∑ t ∈ n.divisors, Λ t / Real.log n * (Real.sqrt n * x n) := fun n hn => by
    rw [← Finset.sum_mul, ← Finset.sum_div, ArithmeticFunction.vonMangoldt_sum]
    rcases eq_or_ne n 1 with rfl | h
    · simp
    · have hn2 : (2 : ℝ) ≤ n := by
        have := (Finset.mem_Icc.mp hn).1; exact_mod_cast (show 2 ≤ n by omega)
      have hlog : Real.log n ≠ 0 := (Real.log_pos (by linarith)).ne'
      rw [if_neg h, div_self hlog, zero_add, one_mul]
  rw [sum_congr rfl h1, sum_add_distrib, sum_ite_eq' (Icc 1 N) 1 (fun _ => x 1),
    if_pos (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩),
    ← sum_edges_eq_sum_divisors N (fun n t => Λ t / Real.log n * (Real.sqrt n * x n))]
  rw [add_assoc]
  congr 1
  rw [edgePart, ← sum_add_distrib]
  refine sum_congr rfl fun m hm => ?_
  rw [upRow, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun t ht => ?_
  have ht1 : (0 : ℝ) < t := by exact_mod_cast (Finset.mem_Icc.mp ht).1
  have hst : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht1).ne'
  have hsq : Real.sqrt ((m : ℝ) * t) = Real.sqrt m * Real.sqrt t :=
    Real.sqrt_mul (Nat.cast_nonneg m) t
  push_cast
  rw [hsq]
  field_simp
  ring

/-! ### The two parts -/

/-- **The edge defects**: `(edge part)² ≤ D_N(x) · Σ_{n ≤ N} n/log n`. -/
theorem sq_edgePart_le (N : ℕ) (x : ℕ → ℝ) :
    edgePart N x ^ 2 ≤ poleDefect N x * ∑ n ∈ Icc 1 N, (n : ℝ) / Real.log n := by
  set s := (Icc 1 N).sigma fun m => Icc 1 (N / m)
  have hΛ : ∀ t : ℕ, 0 ≤ Λ t := fun t => ArithmeticFunction.vonMangoldt_nonneg
  have h := sum_mul_sq_le_sq_mul_sq s
    (fun p => Real.sqrt (Λ p.2) * (x (p.1 * p.2) - x p.1 / Real.sqrt p.2))
    (fun p => Real.sqrt (Λ p.2) * Real.sqrt ((p.1 : ℝ) * p.2) / Real.log ((p.1 : ℝ) * p.2))
  have e1 : ∑ p ∈ s, Real.sqrt (Λ p.2) * (x (p.1 * p.2) - x p.1 / Real.sqrt p.2) *
      (Real.sqrt (Λ p.2) * Real.sqrt ((p.1 : ℝ) * p.2) / Real.log ((p.1 : ℝ) * p.2)) =
      edgePart N x := by
    rw [edgePart, sum_sigma]
    refine sum_congr rfl fun m _ => sum_congr rfl fun t _ => ?_
    have := Real.mul_self_sqrt (hΛ t)
    rw [div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (Real.sqrt ((m : ℝ) * t) * (x (m * t) - x m / Real.sqrt t) *
      (Real.log ((m : ℝ) * t))⁻¹) * this
  have e2 : ∑ p ∈ s, (Real.sqrt (Λ p.2) * (x (p.1 * p.2) - x p.1 / Real.sqrt p.2)) ^ 2 =
      poleDefect N x := by
    rw [poleDefect, sum_sigma]
    refine sum_congr rfl fun m _ => sum_congr rfl fun t _ => ?_
    rw [mul_pow, Real.sq_sqrt (hΛ t)]
  have e3 : ∑ p ∈ s, (Real.sqrt (Λ p.2) * Real.sqrt ((p.1 : ℝ) * p.2) /
      Real.log ((p.1 : ℝ) * p.2)) ^ 2 = ∑ n ∈ Icc 1 N, (n : ℝ) / Real.log n := by
    rw [sum_sigma]
    have h2 := sum_edges_eq_sum_divisors N (fun n t => Λ t * (n : ℝ) / Real.log n ^ 2)
    have e : ∀ m t : ℕ, (Real.sqrt (Λ t) * Real.sqrt ((m : ℝ) * t) / Real.log ((m : ℝ) * t)) ^ 2 =
        Λ t * ((m * t : ℕ) : ℝ) / Real.log ((m * t : ℕ) : ℝ) ^ 2 := fun m t => by
      rw [div_pow, mul_pow, Real.sq_sqrt (hΛ t),
        Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg t))]
      push_cast; ring
    simp_rw [e]
    rw [h2]
    refine sum_congr rfl fun n _ => ?_
    rw [← sum_div, ← sum_mul, ArithmeticFunction.vonMangoldt_sum]
    rcases eq_or_ne (Real.log n) 0 with h0 | h0
    · simp [h0]
    · field_simp
  rw [e1, e2, e3] at h
  exact h

/-- **The up-rows**: `(Σ_m √m x_m R_m)² ≤ |x|² Σ_m m R_m²`. -/
theorem sq_upPart_le (N : ℕ) (x : ℕ → ℝ) :
    (∑ m ∈ Icc 1 N, Real.sqrt m * x m * upRow N m) ^ 2 ≤
      (∑ m ∈ Icc 1 N, x m ^ 2) * ∑ m ∈ Icc 1 N, (m : ℝ) * upRow N m ^ 2 := by
  have h := sum_mul_sq_le_sq_mul_sq (Icc 1 N) x (fun m => Real.sqrt m * upRow N m)
  have e1 : ∑ m ∈ Icc 1 N, x m * (Real.sqrt m * upRow N m) =
      ∑ m ∈ Icc 1 N, Real.sqrt m * x m * upRow N m := sum_congr rfl fun m _ => by ring
  have e2 : ∑ m ∈ Icc 1 N, (Real.sqrt m * upRow N m) ^ 2 = ∑ m ∈ Icc 1 N, (m : ℝ) * upRow N m ^ 2 :=
    sum_congr rfl fun m _ => by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  rw [e1, e2] at h
  exact h

/-! ### The bounds -/

theorem log_gt_half_of_sqrt_lt {N n : ℕ} (hN : 2 ≤ N) (h : Nat.sqrt N < n) :
    Real.log N / 2 < Real.log n := by
  have hsq : N < n * n := Nat.sqrt_lt.mp h
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have : Real.log N < Real.log ((n : ℝ) * n) :=
    Real.log_lt_log hN0 (by exact_mod_cast hsq)
  rw [Real.log_mul hn0.ne' hn0.ne'] at this
  linarith

theorem log_le_two_sqrt (N : ℕ) : Real.log N ≤ 2 * Real.sqrt N := by
  have h := Real.log_le_rpow_div (Nat.cast_nonneg N) (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← Real.sqrt_eq_rpow] at h
  linarith

/-- **The weights of the edge defects**: `Σ_{n ≤ N} n/log n ≤ 5N²/log N` for `N ≥ 3`. -/
theorem sum_div_log_le {N : ℕ} (hN : 3 ≤ N) :
    ∑ n ∈ Icc 1 N, (n : ℝ) / Real.log n ≤ 5 * N ^ 2 / Real.log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hl2 : 2 / 3 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  set s := Nat.sqrt N
  have hsN : (s : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  -- termwise
  have hterm : ∀ n ∈ Icc 1 N, (n : ℝ) / Real.log n ≤ 2 * n / Real.log N + s / Real.log 2 :=
    fun n hn => by
      obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
      have hs0 : 0 ≤ (s : ℝ) / Real.log 2 := by positivity
      by_cases hns : s < n
      · have := log_gt_half_of_sqrt_lt (by omega) hns
        have hlogn : 0 < Real.log n := by linarith
        have : (n : ℝ) / Real.log n ≤ 2 * n / Real.log N := by
          rw [div_le_div_iff₀ hlogn hL]
          nlinarith [Nat.cast_nonneg (α := ℝ) n]
        linarith
      · push Not at hns
        have h2n : 0 ≤ 2 * (n : ℝ) / Real.log N := by positivity
        rcases eq_or_ne n 1 with rfl | h1
        · simp; positivity
        · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
          have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
          have hl2' : 0 < Real.log 2 := by linarith
          have : (n : ℝ) / Real.log n ≤ s / Real.log 2 := by
            rw [div_le_div_iff₀ (by linarith) hl2']
            have : (n : ℝ) ≤ s := by exact_mod_cast hns
            nlinarith
          linarith
  calc ∑ n ∈ Icc 1 N, (n : ℝ) / Real.log n
      ≤ ∑ n ∈ Icc 1 N, (2 * n / Real.log N + s / Real.log 2) := sum_le_sum hterm
    _ ≤ ∑ _n ∈ Icc 1 N, (2 * N / Real.log N + s / Real.log 2) := sum_le_sum fun n hn => by
        have : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
        gcongr
    _ = N * (2 * N / Real.log N + s / Real.log 2) := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
    _ ≤ 5 * N ^ 2 / Real.log N := by
        -- `N √N ≤ 2N² / log N` since `log N ≤ 2√N`
        have hLs := log_le_two_sqrt N
        have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
        have h1 : (N : ℝ) * s * Real.log N ≤ 2 * N ^ 2 := by
          have : (N : ℝ) * s * Real.log N ≤ N * Real.sqrt N * (2 * Real.sqrt N) := by
            have := mul_le_mul hsN hLs hL.le (Real.sqrt_nonneg _)
            nlinarith [hN0]
          nlinarith
        have hl2' : 0 < Real.log 2 := by linarith
        have h2 : (N : ℝ) * s ≤ 2 * N ^ 2 / Real.log N := by
          rw [le_div_iff₀ hL]; linarith
        have hQ : 0 ≤ (N : ℝ) ^ 2 / Real.log N := by positivity
        have h3 : (N : ℝ) * (s / Real.log 2) ≤ 3 * N ^ 2 / Real.log N := by
          rw [show (N : ℝ) * (s / Real.log 2) = N * s / Real.log 2 by ring, div_le_iff₀ hl2',
            show 3 * (N : ℝ) ^ 2 / Real.log N * Real.log 2 =
              3 * Real.log 2 * ((N : ℝ) ^ 2 / Real.log N) by ring]
          have h2' : (N : ℝ) * s ≤ 2 * ((N : ℝ) ^ 2 / Real.log N) := by
            rw [show 2 * ((N : ℝ) ^ 2 / Real.log N) = 2 * N ^ 2 / Real.log N by ring]; exact h2
          have h6 := mul_le_mul_of_nonneg_right hl2.le hQ
          linarith
        have h4 : (N : ℝ) * (2 * N / Real.log N) = 2 * N ^ 2 / Real.log N := by ring
        have h5 : 5 * (N : ℝ) ^ 2 / Real.log N = 2 * N ^ 2 / Real.log N + 3 * N ^ 2 / Real.log N := by
          ring
        rw [mul_add, h4, h5]
        linarith

/-- **The up-rows are `O(N/log N)`**: `m R_m ≤ 2BN/log N + √N`, `B = log 4 + 4`. -/
theorem mul_upRow_le {N m : ℕ} (hN : 2 ≤ N) (hm : 1 ≤ m) :
    (m : ℝ) * upRow N m ≤ 2 * (Real.log 4 + 4) * N / Real.log N + Nat.sqrt N := by
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set s := Nat.sqrt N
  -- termwise: a defect of `2Λ(t)/log N` above `√N`, at most one below
  have hterm : ∀ t ∈ Icc 1 (N / m), Λ t / Real.log ((m : ℝ) * t) ≤
      2 * Λ t / Real.log N + (if m * t ≤ s then 1 else 0) := fun t ht => by
    have ht1 := (Finset.mem_Icc.mp ht).1
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := t)
    have hlog0 := log_mul_nonneg hm ht1
    split_ifs with hs
    · have h2 : 0 ≤ 2 * Λ t / Real.log N := by positivity
      have h1 : Λ t / Real.log ((m : ℝ) * t) ≤ 1 := by
        rcases hlog0.lt_or_eq with hpos | hzero
        · rw [div_le_one hpos]
          refine ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log
            (by exact_mod_cast (show 0 < t by omega)) ?_)
          have : (1 : ℝ) ≤ m := by exact_mod_cast hm
          have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
          nlinarith
        · rw [← hzero, div_zero]; norm_num
      linarith
    · push Not at hs
      have hlt := log_gt_half_of_sqrt_lt (n := m * t) hN hs
      push_cast at hlt
      have hpos : 0 < Real.log ((m : ℝ) * t) := by linarith
      rw [add_zero, div_le_div_iff₀ hpos hL]
      nlinarith
  have hsum : upRow N m ≤ 2 / Real.log N * ∑ t ∈ Icc 1 (N / m), Λ t +
      ∑ t ∈ Icc 1 (N / m), (if m * t ≤ s then (1 : ℝ) else 0) := by
    unfold upRow
    refine (sum_le_sum hterm).trans (le_of_eq ?_)
    rw [sum_add_distrib, mul_sum]
    congr 1
    exact sum_congr rfl fun t _ => by ring
  -- Chebyshev for the first part
  have hcheb := SpacingScaleHarmonicAnalysis.sum_vonMangoldt_Icc_le (N / m)
  have hdiv : (m : ℝ) * ((N / m : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.mul_div_le N m
  -- counting for the second part
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
  have hB : 0 ≤ Real.log 4 + 4 := by have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  have h1 : (m : ℝ) * ∑ t ∈ Icc 1 (N / m), Λ t ≤ (Real.log 4 + 4) * N :=
    calc (m : ℝ) * ∑ t ∈ Icc 1 (N / m), Λ t ≤ m * ((Real.log 4 + 4) * (N / m : ℕ)) :=
          mul_le_mul_of_nonneg_left hcheb hm0.le
      _ = (Real.log 4 + 4) * (m * (N / m : ℕ)) := by ring
      _ ≤ (Real.log 4 + 4) * N := mul_le_mul_of_nonneg_left hdiv hB
  have h2 : 2 / Real.log N * ((m : ℝ) * ∑ t ∈ Icc 1 (N / m), Λ t) ≤
      2 / Real.log N * ((Real.log 4 + 4) * N) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 := mul_le_mul_of_nonneg_left hsum hm0.le
  have e1 : (m : ℝ) * (2 / Real.log N * ∑ t ∈ Icc 1 (N / m), Λ t +
      ∑ t ∈ Icc 1 (N / m), (if m * t ≤ s then (1 : ℝ) else 0)) =
      2 / Real.log N * ((m : ℝ) * ∑ t ∈ Icc 1 (N / m), Λ t) +
        m * ∑ t ∈ Icc 1 (N / m), (if m * t ≤ s then (1 : ℝ) else 0) := by ring
  have e2 : 2 / Real.log N * ((Real.log 4 + 4) * N) = 2 * (Real.log 4 + 4) * N / Real.log N := by
    ring
  rw [e1] at h3
  linarith

/-- **The up-row weights**: `Σ_m m R_m² ≤ (16B² + 16) N²/log N` for `N ≥ 3`. -/
theorem sum_mul_upRow_sq_le {N : ℕ} (hN : 3 ≤ N) :
    ∑ m ∈ Icc 1 N, (m : ℝ) * upRow N m ^ 2 ≤
      (16 * (Real.log 4 + 4) ^ 2 + 16) * N ^ 2 / Real.log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hL1 : 1 ≤ Real.log N := by
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have he : Real.exp 1 ≤ 3 := le_of_lt (Real.exp_one_lt_d9.trans (by norm_num))
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (he.trans h3)
  set B := Real.log 4 + 4
  set s := Nat.sqrt N
  set R := 2 * B * N / Real.log N + s
  have hR0 : 0 ≤ R := by positivity
  have hharm : ∑ m ∈ Icc 1 N, (1 : ℝ) / m ≤ 1 + Real.log N := by
    have h := harmonic_le_one_add_log N
    simp only [_root_.harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
    simpa only [one_div] using h
  have hterm : ∀ m ∈ Icc 1 N, (m : ℝ) * upRow N m ^ 2 ≤ R ^ 2 * (1 / m) := fun m hm => by
    have hm1 := (Finset.mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have h1 := mul_upRow_le (by omega) hm1 (N := N)
    have h0 : 0 ≤ (m : ℝ) * upRow N m := mul_nonneg hm0.le (upRow_nonneg hm1)
    have hsq : ((m : ℝ) * upRow N m) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ h0 h1 2
    rw [show (m : ℝ) * upRow N m ^ 2 = ((m : ℝ) * upRow N m) ^ 2 * (1 / m) by
      field_simp]
    exact mul_le_mul_of_nonneg_right hsq (by positivity)
  have hsN : (s : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hLs := log_le_two_sqrt N
  calc ∑ m ∈ Icc 1 N, (m : ℝ) * upRow N m ^ 2
      ≤ ∑ m ∈ Icc 1 N, R ^ 2 * (1 / m) := sum_le_sum hterm
    _ = R ^ 2 * ∑ m ∈ Icc 1 N, (1 : ℝ) / m := by rw [mul_sum]
    _ ≤ R ^ 2 * (2 * Real.log N) := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    _ ≤ (16 * B ^ 2 + 16) * N ^ 2 / Real.log N := by
        -- `R² ≤ 2(2BN/log N)² + 2N` and `N log² N ≤ 4N²`
        have hR2 : R ^ 2 ≤ 2 * (2 * B * N / Real.log N) ^ 2 + 2 * N := by
          have : (s : ℝ) ^ 2 ≤ N := by nlinarith [Nat.cast_nonneg (α := ℝ) s]
          simp only [R]; nlinarith [sq_nonneg (2 * B * N / Real.log N - s)]
        have hlogsq : Real.log N ^ 2 ≤ 4 * N := by nlinarith [Real.sqrt_nonneg (N : ℝ)]
        rw [le_div_iff₀ hL]
        have e : (2 * B * N / Real.log N) ^ 2 * Real.log N ^ 2 = 4 * B ^ 2 * N ^ 2 := by
          field_simp; ring
        nlinarith [mul_le_mul_of_nonneg_right hR2 (by positivity : (0 : ℝ) ≤ 2 * Real.log N ^ 2),
          sq_nonneg B]

/-! ### The multiplicative Hardy inequality -/

/-- **The multiplicative Hardy inequality**: for `N ≥ 3`,
`(Σ_{n ≤ N} √n x_n)² ≤ (48B² + 51)(N²/log N)(D_N(x) + |x|²)`, `B = log 4 + 4`. -/
theorem sq_vRow_le {N : ℕ} (hN : 3 ≤ N) (x : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, Real.sqrt n * x n) ^ 2 ≤
      (48 * (Real.log 4 + 4) ^ 2 + 51) * (N ^ 2 / Real.log N) *
        (poleDefect N x + ∑ n ∈ Icc 1 N, x n ^ 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  set B := Real.log 4 + 4
  set D := poleDefect N x
  set X := ∑ n ∈ Icc 1 N, x n ^ 2
  set Q := (N : ℝ) ^ 2 / Real.log N
  have hD := poleDefect_nonneg N x
  have hX : 0 ≤ X := sum_nonneg fun _ _ => sq_nonneg _
  have hQ1 : 1 ≤ Q := by
    rw [le_div_iff₀ hL, one_mul]
    have := Real.log_le_sub_one_of_pos hN0
    nlinarith
  have hx1 : x 1 ^ 2 ≤ X :=
    single_le_sum (f := fun n => x n ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  have hE := sq_edgePart_le N x
  have hE' := sum_div_log_le hN
  have hU := sq_upPart_le N x
  have hU' := sum_mul_upRow_sq_le hN
  rw [vRow_eq (by omega) x]
  set e := edgePart N x
  set u := ∑ m ∈ Icc 1 N, Real.sqrt m * x m * upRow N m
  have h3 : (x 1 + e + u) ^ 2 ≤ 3 * (x 1 ^ 2 + e ^ 2 + u ^ 2) := by
    nlinarith [sq_nonneg (x 1 - e), sq_nonneg (e - u), sq_nonneg (x 1 - u)]
  have he : e ^ 2 ≤ D * (5 * Q) := by
    refine hE.trans (mul_le_mul_of_nonneg_left ?_ hD)
    simp only [Q]; rw [mul_div_assoc] at hE'; exact hE'
  have hu : u ^ 2 ≤ X * ((16 * B ^ 2 + 16) * Q) := by
    refine hU.trans (mul_le_mul_of_nonneg_left ?_ hX)
    simp only [Q]; rw [mul_div_assoc] at hU'; exact hU'
  have hB : 0 ≤ B ^ 2 := sq_nonneg B
  have hQ0 : 0 ≤ Q := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hQ1 hX, mul_nonneg hD hQ0, mul_nonneg hX hQ0,
    mul_nonneg (mul_nonneg hB hX) (by linarith : (0 : ℝ) ≤ Q)]

end GaloisForLFunctions.ArithmeticLorentzianGeometry
