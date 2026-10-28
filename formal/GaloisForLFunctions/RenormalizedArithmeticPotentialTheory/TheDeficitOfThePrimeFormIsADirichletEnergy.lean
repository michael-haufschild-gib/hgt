import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePoleIsTheTopOfThePrimeForm

/-!
# The deficit of the prime form is a Dirichlet energy

The pole vector `b_n = n^{−1/2}` is the ground state of Weil's atomic prime form `P_N`
(`ThePoleIsTheTopOfThePrimeForm`). Transforming by it turns `P_N` into a diagonal minus the Dirichlet
form of the multiplicative random walk: every prime-power edge `m → mt` carries the defect of the
pole relation `x_{mt} = t^{−1/2} x_m`, weighted by `Λ(t)`.

* **The ground-state identity** (`atomicWeilForm_add_poleDefect`): for every `N` and `x`,
  `P_N(x) + D_N(x) = Σ_{n ≤ N} (A(⌊N/n⌋) + log n) x_n²`, with
  `D_N(x) = Σ_{mt ≤ N} Λ(t)(x_{mt} − x_m/√t)²` (`poleDefect`) and `A(y) = Σ_{t ≤ y} Λ(t)/t`.
* **The defect pays the top atoms** (`sum_top_le_poleDefect`): `log n = Σ_{t ∣ n} Λ(t)` and
  Chebyshev's bound give `Σ_n (n/N) log n · x_n² ≤ 2 D_N(x) + 2(log 4 + 4)|x|²`.
* **The sharp counterterm with its deficit** (`eventually_atomicWeilForm_add_poleDefect_le`): for
  every `ε > 0`, eventually `P_N(x) + (1 − ε) D_N(x) ≤ (log N − γ + ε)|x|²`. Mertens' theorem
  bounds the rows with `⌊N/n⌋` large; the rows near the top exceed `log N − γ` by a bounded amount,
  and their atoms are paid by the defect. No tilt of the pole is needed.

* **The Hodge index modulo a prime** (`eventually_atomicWeilForm_le_of_ladderOrthogonal`): the
  `p`-power edges of the defect form the ladder defect `E_p`, and on each `p`-ladder `{u p^j}`
  Lagrange's identity gives `E_p ≥ |b|²|x|² − ⟨b, x⟩²` with `b_j = p^{−j/2}`. So on vectors
  orthogonal to every ladder pole, `P_N ≤ (log N − γ − (1 + 1/p) log p + ε)|·|²` eventually.

So the defect of the sharp counterterm `log N − γ` is, up to `ε`, the Dirichlet energy of the pole
relations. It vanishes exactly on the pole line, and every prime contributes its own gap on the
whole space, not only on the class profiles of `TheValuationTowerIsExactlySolvable`.
-/

noncomputable section

open Filter Topology Finset
open scoped Chebyshev

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.ArithmeticIntersectionTheory GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.ArithmeticEffectivityTheory ArithmeticFunction

local notation "γ" => Real.eulerMascheroniConstant

/-! ### 1. The pole defect and the edges of the prime form -/

/-- The **pole defect** `D_N(x) = Σ_{m t ≤ N} Λ(t) (x_{mt} − x_m/√t)²`: the Dirichlet energy of the
pole relations `x_{mt} = t^{−1/2} x_m` along the prime-power edges of `[1, N]`. -/
def poleDefect (N : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m), Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2

theorem poleDefect_nonneg (N : ℕ) (x : ℕ → ℝ) : 0 ≤ poleDefect N x :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => mul_nonneg vonMangoldt_nonneg (sq_nonneg _)

/-- Up the tower: `Σ_{n ≤ N, m ∣ n, n ≠ m} g(n) = Σ_{t ≤ N/m} g(mt)` when `g(m) = 0`. -/
theorem sum_up_eq_of_self {m N : ℕ} (hm : 0 < m) (g : ℕ → ℝ) (hg : g m = 0) :
    ∑ n ∈ Icc 1 N, (if m ∣ n ∧ m ≠ n then g n else 0) = ∑ t ∈ Icc 1 (N / m), g (m * t) := by
  have hterm : ∀ n ∈ Icc 1 N, (if m ∣ n ∧ m ≠ n then g n else 0) =
      if m ∣ n then g n else 0 := by
    intro n _
    by_cases h : m ∣ n
    · by_cases h' : m = n
      · subst h'; simp [hg]
      · rw [if_pos ⟨h, h'⟩, if_pos h]
    · rw [if_neg (fun h'' => h h''.1), if_neg h]
  rw [sum_congr rfl hterm, ← sum_filter, filter_dvd_Icc_eq_image hm,
    sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hm h]

/-- The upward half of Weil's kernel. -/
def upKernel (m n : ℕ) : ℝ :=
  if m ∣ n ∧ m ≠ n then Λ (n / m) / Real.sqrt ((n / m : ℕ) : ℝ) else 0

theorem weilPrimeKernel_eq_up_add (m n : ℕ) :
    weilPrimeKernel m n = upKernel m n + upKernel n m := by
  unfold weilPrimeKernel upKernel
  by_cases h1 : m ∣ n ∧ m ≠ n
  · have h2 : ¬ (n ∣ m ∧ n ≠ m) := fun h => h1.2 (Nat.dvd_antisymm h1.1 h.1)
    rw [if_pos h1, if_pos h1, if_neg h2, add_zero]
  · rw [if_neg h1, if_neg h1, zero_add]

/-- **Weil's form along the edges**: `P_N(x) = 2 Σ_{mt ≤ N} (Λ(t)/√t) x_m x_{mt}`. -/
theorem atomicWeilForm_eq_edges (N : ℕ) (x : ℕ → ℝ) :
    atomicWeilForm N x =
      2 * ∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m), Λ t / Real.sqrt t * (x m * x (m * t)) := by
  set S := Icc 1 N
  have hrow : ∀ m ∈ S, ∑ n ∈ S, x m * x n * upKernel m n =
      ∑ t ∈ Icc 1 (N / m), Λ t / Real.sqrt t * (x m * x (m * t)) := by
    intro m hm
    have hm0 := (mem_Icc.mp hm).1
    have h := sum_up_eq_of_self (N := N) hm0
      (fun n => x m * x n * (Λ (n / m) / Real.sqrt ((n / m : ℕ) : ℝ)))
      (by simp [Nat.div_self hm0])
    rw [show ∑ n ∈ S, x m * x n * upKernel m n = ∑ n ∈ S, (if m ∣ n ∧ m ≠ n then
        x m * x n * (Λ (n / m) / Real.sqrt ((n / m : ℕ) : ℝ)) else 0) from
      sum_congr rfl fun n _ => by unfold upKernel; split_ifs <;> simp, h]
    exact sum_congr rfl fun t _ => by rw [Nat.mul_div_cancel_left t hm0]; ring
  have hsplit : atomicWeilForm N x = ∑ m ∈ S, ∑ n ∈ S, x m * x n * upKernel m n +
      ∑ m ∈ S, ∑ n ∈ S, x m * x n * upKernel n m := by
    rw [atomicWeilForm, ← sum_add_distrib]
    exact sum_congr rfl fun m _ => by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun n _ => by rw [weilPrimeKernel_eq_up_add]; ring
  have hswap : ∑ m ∈ S, ∑ n ∈ S, x m * x n * upKernel n m =
      ∑ m ∈ S, ∑ n ∈ S, x m * x n * upKernel m n := by
    rw [sum_comm]
    exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by ring
  rw [hsplit, hswap, ← two_mul, sum_congr rfl hrow]

/-- **Edges by their top**: `Σ_{m ≤ N} Σ_{t ≤ N/m} F(mt, t) = Σ_{n ≤ N} Σ_{t ∣ n} F(n, t)`. -/
theorem sum_edges_eq_sum_divisors (N : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m), F (m * t) t =
      ∑ n ∈ Icc 1 N, ∑ t ∈ n.divisors, F n t := by
  -- both sides run over the pairs `(m, t)` with `m, t ≥ 1` and `mt ≤ N`
  have h1 : ∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m), F (m * t) t =
      ∑ t ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / t), F (m * t) t := by
    refine sum_comm' fun m t => ?_
    simp only [mem_Icc]
    constructor
    · rintro ⟨⟨hm1, -⟩, ht1, htN⟩
      rw [Nat.le_div_iff_mul_le hm1] at htN
      refine ⟨⟨hm1, ?_⟩, ht1, ?_⟩
      · rw [Nat.le_div_iff_mul_le ht1]; linarith [Nat.mul_comm t m]
      · nlinarith
    · rintro ⟨⟨hm1, hmN⟩, ht1, -⟩
      rw [Nat.le_div_iff_mul_le ht1] at hmN
      refine ⟨⟨hm1, ?_⟩, ht1, ?_⟩
      · nlinarith
      · rw [Nat.le_div_iff_mul_le hm1]; linarith [Nat.mul_comm t m]
  have h2 : ∀ t ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / t), F (m * t) t =
      ∑ n ∈ Icc 1 N, if t ∣ n then F n t else 0 := by
    intro t ht
    have ht0 := (mem_Icc.mp ht).1
    rw [← sum_filter, filter_dvd_Icc_eq_image ht0,
      sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left ht0 h]
    exact sum_congr rfl fun m _ => by rw [Nat.mul_comm]
  rw [h1, sum_congr rfl h2, sum_comm]
  refine sum_congr rfl fun n hn => ?_
  rw [← sum_filter, filter_Icc_dvd_eq_divisors (mem_Icc.mp hn).1 (mem_Icc.mp hn).2]

/-! ### 2. The ground-state identity -/

/-- **The ground-state identity.** `P_N(x) + D_N(x) = Σ_{n ≤ N} (A(⌊N/n⌋) + log n) x_n²`: the pole
vector turns Weil's prime form into its rows minus the Dirichlet energy of the pole relations. -/
theorem atomicWeilForm_add_poleDefect (N : ℕ) (x : ℕ → ℝ) :
    atomicWeilForm N x + poleDefect N x =
      ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * x n ^ 2 := by
  have hm : ∀ m ∈ Icc 1 N,
      ∑ t ∈ Icc 1 (N / m), Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2 =
        ∑ t ∈ Icc 1 (N / m), Λ t * x (m * t) ^ 2 -
          2 * ∑ t ∈ Icc 1 (N / m), Λ t / Real.sqrt t * (x m * x (m * t)) +
          mertensSum (N / m) * x m ^ 2 := by
    intro m _
    rw [mertensSum, sum_mul, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun t ht => ?_
    have ht0 : (0 : ℝ) < t := by exact_mod_cast (mem_Icc.mp ht).1
    have hs0 : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht0).ne'
    have hsq : (x (m * t) - x m / Real.sqrt t) ^ 2 =
        x (m * t) ^ 2 - 2 * (x m * x (m * t)) / Real.sqrt t + x m ^ 2 / t := by
      rw [sub_sq, div_pow, Real.sq_sqrt ht0.le]; ring
    rw [hsq]
    field_simp
  have hlog : ∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m), Λ t * x (m * t) ^ 2 =
      ∑ n ∈ Icc 1 N, Real.log n * x n ^ 2 := by
    have h := sum_edges_eq_sum_divisors N (fun n t => Λ t * x n ^ 2)
    rw [h]
    exact sum_congr rfl fun n _ => by rw [← sum_mul, vonMangoldt_sum]
  rw [poleDefect, sum_congr rfl hm, sum_add_distrib, sum_sub_distrib, ← mul_sum, hlog,
    atomicWeilForm_eq_edges]
  rw [show ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * x n ^ 2 =
      ∑ n ∈ Icc 1 N, Real.log n * x n ^ 2 + ∑ n ∈ Icc 1 N, mertensSum (N / n) * x n ^ 2 by
    rw [← sum_add_distrib]; exact sum_congr rfl fun n _ => by ring]
  ring

/-! ### 3. The defect pays the top atoms -/

/-- `Σ_{t ≤ k} Λ(t) = ψ(k)`. -/
theorem sum_vonMangoldt_Icc_eq_psi (k : ℕ) : ∑ t ∈ Icc 1 k, Λ t = ψ (k : ℝ) := by
  rw [Chebyshev.psi, Nat.floor_natCast]; rfl

/-- **The defect pays the top atoms**: `Σ_n (n/N) log n · x_n² ≤ 2 D_N(x) + 2(log 4 + 4)|x|²`. Write
`log n = Σ_{t ∣ n} Λ(t)` and compare `x_{mt}` with `x_m/√t` on every edge; what is left is
`Σ_m (m/N) ψ(⌊N/m⌋) x_m²`, at most `(log 4 + 4)|x|²` by Chebyshev. -/
theorem sum_top_le_poleDefect (N : ℕ) (x : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, (n : ℝ) / N * Real.log n * x n ^ 2 ≤
      2 * poleDefect N x + 2 * (Real.log 4 + 4) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  have hedge : ∑ n ∈ Icc 1 N, (n : ℝ) / N * Real.log n * x n ^ 2 =
      ∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m), ((m * t : ℕ) : ℝ) / N * Λ t * x (m * t) ^ 2 := by
    have h := sum_edges_eq_sum_divisors N (fun n t => (n : ℝ) / N * Λ t * x n ^ 2)
    rw [h]
    exact sum_congr rfl fun n _ => by rw [← sum_mul, ← mul_sum, vonMangoldt_sum]
  -- on each edge: `(mt/N) Λ(t) x_{mt}² ≤ 2Λ(t)(x_{mt} − x_m/√t)² + 2(m/N) Λ(t) x_m²`
  have hpt : ∀ m ∈ Icc 1 N, ∀ t ∈ Icc 1 (N / m),
      ((m * t : ℕ) : ℝ) / N * Λ t * x (m * t) ^ 2 ≤
        2 * (Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2) + 2 * ((m : ℝ) / N * Λ t * x m ^ 2) := by
    intro m hm t ht
    have hm1 := (mem_Icc.mp hm).1
    have ht1 := (mem_Icc.mp ht).1
    have htm := (mem_Icc.mp ht).2
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by have := (mem_Icc.mp hm).2; omega)
    have ht0 : (0 : ℝ) < t := by exact_mod_cast ht1
    have hmtN : ((m * t : ℕ) : ℝ) ≤ N := by
      have : m * t ≤ N := by rw [Nat.le_div_iff_mul_le hm1] at htm; linarith [Nat.mul_comm t m]
      exact_mod_cast this
    have hr0 : 0 ≤ ((m * t : ℕ) : ℝ) / N := by positivity
    have hr1 : ((m * t : ℕ) : ℝ) / N ≤ 1 := (div_le_one hN0).mpr hmtN
    have hΛ := vonMangoldt_nonneg (n := t)
    -- `a² ≤ 2(a − b)² + 2b²` with `b = x_m/√t`, `b² = x_m²/t`
    have hsq : x (m * t) ^ 2 ≤ 2 * (x (m * t) - x m / Real.sqrt t) ^ 2 + 2 * (x m ^ 2 / t) := by
      have hb : (x m / Real.sqrt t) ^ 2 = x m ^ 2 / t := by
        rw [div_pow, Real.sq_sqrt ht0.le]
      nlinarith [sq_nonneg (x (m * t) - 2 * (x m / Real.sqrt t))]
    have hcast : ((m * t : ℕ) : ℝ) / N * (x m ^ 2 / t) = (m : ℝ) / N * x m ^ 2 := by
      push_cast; field_simp
    have hD : 0 ≤ Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2 := mul_nonneg hΛ (sq_nonneg _)
    calc ((m * t : ℕ) : ℝ) / N * Λ t * x (m * t) ^ 2
        ≤ ((m * t : ℕ) : ℝ) / N * Λ t *
            (2 * (x (m * t) - x m / Real.sqrt t) ^ 2 + 2 * (x m ^ 2 / t)) :=
          mul_le_mul_of_nonneg_left hsq (mul_nonneg hr0 hΛ)
      _ = 2 * (((m * t : ℕ) : ℝ) / N * (Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2)) +
            2 * (Λ t * (((m * t : ℕ) : ℝ) / N * (x m ^ 2 / t))) := by ring
      _ ≤ 2 * (Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2) +
            2 * ((m : ℝ) / N * Λ t * x m ^ 2) := by
          rw [hcast]
          nlinarith [mul_le_mul_of_nonneg_right hr1 hD]
  -- the leftover rows are Chebyshev's function
  have hrow : ∀ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m), (m : ℝ) / N * Λ t * x m ^ 2 ≤
      (Real.log 4 + 4) * x m ^ 2 := by
    intro m hm
    have hm1 := (mem_Icc.mp hm).1
    have hmN := (mem_Icc.mp hm).2
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hq1 : (1 : ℝ) ≤ ((N / m : ℕ) : ℝ) := by
      exact_mod_cast Nat.div_pos hmN hm1
    have hqm : (m : ℝ) * ((N / m : ℕ) : ℝ) ≤ N := by
      exact_mod_cast Nat.mul_div_le N m
    rw [show ∑ t ∈ Icc 1 (N / m), (m : ℝ) / N * Λ t * x m ^ 2 =
        (m : ℝ) / N * (∑ t ∈ Icc 1 (N / m), Λ t) * x m ^ 2 by rw [mul_sum, sum_mul],
      sum_vonMangoldt_Icc_eq_psi]
    have hψ := psi_le_linear hq1
    have hψ0 : 0 ≤ ψ ((N / m : ℕ) : ℝ) := Chebyshev.psi_nonneg _
    have hfac : (m : ℝ) / N * ψ ((N / m : ℕ) : ℝ) ≤ Real.log 4 + 4 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hN0]
      have hc : 0 ≤ Real.log 4 + 4 := by
        have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
      nlinarith [mul_le_mul_of_nonneg_left hψ hm0.le]
    exact mul_le_mul_of_nonneg_right hfac (sq_nonneg _)
  rw [hedge, poleDefect, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun m hm => ?_
  calc ∑ t ∈ Icc 1 (N / m), ((m * t : ℕ) : ℝ) / N * Λ t * x (m * t) ^ 2
      ≤ ∑ t ∈ Icc 1 (N / m), (2 * (Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2) +
          2 * ((m : ℝ) / N * Λ t * x m ^ 2)) := sum_le_sum fun t ht => hpt m hm t ht
    _ = 2 * ∑ t ∈ Icc 1 (N / m), Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2 +
          2 * ∑ t ∈ Icc 1 (N / m), (m : ℝ) / N * Λ t * x m ^ 2 := by
        rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ 2 * ∑ t ∈ Icc 1 (N / m), Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2 +
          2 * (Real.log 4 + 4) * x m ^ 2 := by
        have := hrow m hm; nlinarith

/-! ### 4. The sharp counterterm with its deficit -/

/-- **The deficit of the sharp counterterm is the pole defect.** For every `ε > 0`, eventually in
`N`, `P_N(x) + (1 − ε) D_N(x) ≤ (log N − γ + ε)|x|²` for every `x`. The rows with `⌊N/n⌋ ≥ Q` obey
Mertens' bound `A(⌊N/n⌋) + log n ≤ log N − γ + ε/2`; the rows below exceed it by at most
`A(Q) + γ`, which is at most `θ (n/N) log n` there once `log(N/Q) ≥ Q(A(Q) + γ)/θ`, and those atoms
are paid by the defect (`sum_top_le_poleDefect`). -/
theorem eventually_atomicWeilForm_add_poleDefect_le {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ x : ℕ → ℝ,
      atomicWeilForm N x + (1 - ε) * poleDefect N x ≤
        (Real.log N - γ + ε) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  set B : ℝ := Real.log 4 + 4 with hB
  have hB0 : 0 < B := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
  set th : ℝ := ε / (4 * B + 2) with hth
  have hth0 : 0 < th := by positivity
  have hthε : 2 * th ≤ ε := by
    rw [hth, mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  have hthB : 2 * th * B ≤ ε / 2 := by
    rw [hth]; field_simp; nlinarith
  have hγ0 : 0 < γ :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans Real.one_half_lt_eulerMascheroniConstant
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.mp
    (tendsto_mertensSum_sub_log.eventually (gt_mem_nhds (by linarith : -γ < -γ + ε / 2)))
  set Q : ℕ := Q₀ + 1 with hQ
  have hQ0 : (0 : ℝ) < Q := by positivity
  set C : ℝ := mertensSum Q + γ with hC
  have hAQ : 0 ≤ mertensSum Q := sum_nonneg fun t _ => div_nonneg vonMangoldt_nonneg (by positivity)
  have hC0 : 0 < C := by linarith
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (Real.log Q + Q * C / th))
  refine ⟨N₀ + 1, fun N hN x => ?_⟩
  have hlogN : Real.log Q + Q * C / th ≤ Real.log N := hN₀ N (by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  -- every row is at most `log N − γ + ε/2 + th (n/N) log n`
  have hrowbd : ∀ n ∈ Icc 1 N, mertensSum (N / n) + Real.log n ≤
      Real.log N - γ + ε / 2 + th * ((n : ℝ) / N * Real.log n) := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hlogn : Real.log n ≤ Real.log N :=
      Real.log_le_log hn0 (by exact_mod_cast hnN)
    by_cases hbulk : Q₀ ≤ N / n
    · -- Mertens on the bulk rows
      have hM := hQ₀ (N / n) hbulk
      have hq0 : (0 : ℝ) < ((N / n : ℕ) : ℝ) := by
        exact_mod_cast Nat.div_pos hnN hn1
      have hprod : ((N / n : ℕ) : ℝ) * n ≤ N := by exact_mod_cast Nat.div_mul_le_self N n
      have hlogs : Real.log ((N / n : ℕ) : ℝ) + Real.log n ≤ Real.log N := by
        rw [← Real.log_mul hq0.ne' hn0.ne']
        exact Real.log_le_log (mul_pos hq0 hn0) hprod
      have htop : 0 ≤ th * ((n : ℝ) / N * Real.log n) :=
        mul_nonneg hth0.le (mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hn1)))
      linarith
    · -- the top rows: `N < Q n`
      have hlt : N / n < Q := by omega
      have hNQ : (N : ℝ) < Q * n := by
        exact_mod_cast (Nat.div_lt_iff_lt_mul hn1).mp hlt
      have hmono : mertensSum (N / n) ≤ mertensSum Q :=
        sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hlt.le)
          fun t _ _ => div_nonneg vonMangoldt_nonneg (by positivity)
      have hratio : 1 / (Q : ℝ) ≤ (n : ℝ) / N := by
        rw [div_le_div_iff₀ hQ0 hN0]; linarith
      have hNQ0 : (0 : ℝ) < N / Q := by positivity
      have hlogQ : Real.log (N / Q) ≤ Real.log n := by
        refine Real.log_le_log hNQ0 ?_
        rw [div_le_iff₀ hQ0]; linarith
      have hlogNQ : Q * C / th ≤ Real.log (N / Q) := by
        rw [Real.log_div hN0.ne' hQ0.ne']; linarith
      have hlogNQ0 : 0 ≤ Real.log (N / Q) := le_trans (by positivity) hlogNQ
      -- `C ≤ th (1/Q) log(N/Q) ≤ th (n/N) log n`
      have hCle : C ≤ th * ((n : ℝ) / N * Real.log n) := by
        have h1 : C ≤ th * (1 / (Q : ℝ) * Real.log (N / Q)) := by
          have h2 : (Q : ℝ) * C ≤ th * Real.log (N / Q) := by
            have := (div_le_iff₀ hth0).mp hlogNQ; linarith
          rw [show th * (1 / (Q : ℝ) * Real.log (N / Q)) = th * Real.log (N / Q) / Q by
            field_simp, le_div_iff₀ hQ0]
          linarith
        refine h1.trans (mul_le_mul_of_nonneg_left ?_ hth0.le)
        exact mul_le_mul hratio hlogQ hlogNQ0 (by positivity)
      linarith
  have htopsum := sum_top_le_poleDefect N x
  have hD := poleDefect_nonneg N x
  have hid := atomicWeilForm_add_poleDefect N x
  have hrows : ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * x n ^ 2 ≤
      (Real.log N - γ + ε / 2) * ∑ n ∈ Icc 1 N, x n ^ 2 +
        th * ∑ n ∈ Icc 1 N, (n : ℝ) / N * Real.log n * x n ^ 2 := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_le_sum fun n hn => by
      nlinarith [mul_le_mul_of_nonneg_right (hrowbd n hn) (sq_nonneg (x n))]
  have hX := sum_nonneg fun n (_ : n ∈ Icc 1 N) => sq_nonneg (x n)
  nlinarith [mul_le_mul_of_nonneg_left htopsum hth0.le, mul_le_mul_of_nonneg_right hthε hD,
    mul_le_mul_of_nonneg_right hthB hX]

/-! ### 5. The Hodge index modulo a prime -/

/-- **The `p`-ladders partition `[1, N]`**: every `n ≤ N` is `u p^j` with `p ∤ u`, uniquely. -/
theorem sum_Icc_eq_sum_ladders {p : ℕ} (hp : p.Prime) (N : ℕ) (F : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, F n = ∑ u ∈ (Icc 1 N).filter (fun u => ¬ p ∣ u),
      ∑ j ∈ range (N + 1), if u * p ^ j ≤ N then F (u * p ^ j) else 0 := by
  have hp1 := hp.one_lt
  rw [show (∑ u ∈ (Icc 1 N).filter (fun u => ¬ p ∣ u),
      ∑ j ∈ range (N + 1), if u * p ^ j ≤ N then F (u * p ^ j) else 0) =
      ∑ q ∈ ((Icc 1 N).filter (fun u => ¬ p ∣ u) ×ˢ range (N + 1)).filter
        (fun q => q.1 * p ^ q.2 ≤ N), F (q.1 * p ^ q.2) by
    rw [Finset.sum_filter (p := fun q : ℕ × ℕ => q.1 * p ^ q.2 ≤ N), sum_product]]
  refine sum_nbij' (fun n => (n / p ^ n.factorization p, n.factorization p))
    (fun q => q.1 * p ^ q.2) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
    have hn0 : n ≠ 0 := by omega
    have hpow : p ^ n.factorization p ≤ n := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n p)
    have hlt := Nat.lt_pow_self (n := n.factorization p) hp1
    simp only [mem_filter, mem_product, mem_Icc, mem_range]
    refine ⟨⟨⟨⟨Nat.ordCompl_pos p hn0, (Nat.div_le_self _ _).trans hnN⟩,
      Nat.not_dvd_ordCompl hp hn0⟩, by omega⟩, ?_⟩
    rw [mul_comm, Nat.ordProj_mul_ordCompl_eq_self]; exact hnN
  · intro q hq
    simp only [mem_filter, mem_product, mem_Icc, mem_range] at hq
    obtain ⟨⟨⟨⟨hu1, -⟩, -⟩, -⟩, hle⟩ := hq
    exact mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (by omega) (pow_ne_zero _ hp.ne_zero)), hle⟩
  · intro n _
    simp only
    rw [mul_comm, Nat.ordProj_mul_ordCompl_eq_self]
  · intro q hq
    simp only [mem_filter, mem_product, mem_Icc, mem_range] at hq
    obtain ⟨⟨⟨⟨hu1, -⟩, hpu⟩, -⟩, -⟩ := hq
    have hv : (q.1 * p ^ q.2).factorization p = q.2 := by
      rw [Nat.factorization_mul (by omega) (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hpu, hp.factorization_pow, Finsupp.single_eq_same,
        zero_add]
    simp only [hv, Nat.mul_div_cancel _ (pow_pos hp.pos _), Prod.mk.eta]
  · intro n _
    simp only
    rw [mul_comm, Nat.ordProj_mul_ordCompl_eq_self]

/-- The **`p`-ladder defect** `E_p(x) = Σ_{m p^k ≤ N, k ≥ 1} (x_{m p^k} − p^{−k/2} x_m)²`: the pole
defect along the `p`-power edges, all pairs of one `p`-ladder. -/
def ladderDefect (p N : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Icc 1 N, ∑ k ∈ Icc 1 N,
    if m * p ^ k ≤ N then (x (m * p ^ k) - x m / Real.sqrt ((p ^ k : ℕ) : ℝ)) ^ 2 else 0

/-- The `p`-power edges carry `log p · E_p(x)` of the pole defect. -/
theorem log_mul_ladderDefect_le {p : ℕ} (hp : p.Prime) (N : ℕ) (x : ℕ → ℝ) :
    Real.log p * ladderDefect p N x ≤ poleDefect N x := by
  rw [ladderDefect, poleDefect, mul_sum]
  refine sum_le_sum fun m hm => ?_
  have hm1 := (mem_Icc.mp hm).1
  have hfil : Real.log p * ∑ k ∈ Icc 1 N, (if m * p ^ k ≤ N then
      (x (m * p ^ k) - x m / Real.sqrt ((p ^ k : ℕ) : ℝ)) ^ 2 else 0) =
      ∑ k ∈ (Icc 1 N).filter (fun k => m * p ^ k ≤ N),
        Λ (p ^ k) * (x (m * p ^ k) - x m / Real.sqrt ((p ^ k : ℕ) : ℝ)) ^ 2 := by
    rw [sum_filter, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk0 : k ≠ 0 := by have := (mem_Icc.mp hk).1; omega
    rw [vonMangoldt_apply_pow hk0, vonMangoldt_apply_prime hp]
    split_ifs <;> simp
  have himg : ∑ t ∈ ((Icc 1 N).filter (fun k => m * p ^ k ≤ N)).image (fun k => p ^ k),
      Λ t * (x (m * t) - x m / Real.sqrt (t : ℝ)) ^ 2 =
      ∑ k ∈ (Icc 1 N).filter (fun k => m * p ^ k ≤ N),
        Λ (p ^ k) * (x (m * p ^ k) - x m / Real.sqrt ((p ^ k : ℕ) : ℝ)) ^ 2 :=
    sum_image fun a _ b _ h => Nat.pow_right_injective hp.two_le h
  rw [hfil, ← himg]
  refine sum_le_sum_of_subset_of_nonneg ?_ fun t _ _ =>
    mul_nonneg vonMangoldt_nonneg (sq_nonneg _)
  intro t ht
  simp only [mem_image, mem_filter, mem_Icc] at ht
  obtain ⟨k, ⟨⟨-, -⟩, hkN⟩, rfl⟩ := ht
  exact mem_Icc.mpr ⟨Nat.one_le_pow _ _ hp.pos,
    (Nat.le_div_iff_mul_le hm1).mpr (by linarith [Nat.mul_comm m (p ^ k)])⟩

/-- **Lagrange's identity**: `Σ_{j,l} (B_j Y_l − B_l Y_j)² = 2(ΣB²)(ΣY²) − 2(ΣBY)²`. -/
theorem sum_sum_minor_sq (s : Finset ℕ) (B Y : ℕ → ℝ) :
    ∑ j ∈ s, ∑ l ∈ s, (B j * Y l - B l * Y j) ^ 2 =
      2 * ((∑ j ∈ s, B j ^ 2) * ∑ j ∈ s, Y j ^ 2) - 2 * (∑ j ∈ s, B j * Y j) ^ 2 := by
  have h1 : ∀ j ∈ s, ∑ l ∈ s, (B j * Y l - B l * Y j) ^ 2 =
      B j ^ 2 * ∑ l ∈ s, Y l ^ 2 + Y j ^ 2 * ∑ l ∈ s, B l ^ 2 -
        B j * Y j * (2 * ∑ l ∈ s, B l * Y l) := by
    intro j _
    rw [mul_sum, mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun l _ => by ring
  rw [sum_congr rfl h1, sum_sub_distrib, sum_add_distrib, ← sum_mul, ← sum_mul, ← sum_mul]
  ring

/-- Shifting a sum up a ladder: `Σ_{1 ≤ k ≤ N} h(j + k) = Σ_{l ≤ N, l > j} h(l)` when `h` vanishes
beyond `N`. -/
theorem sum_Icc_shift (j N : ℕ) (h : ℕ → ℝ) (hvan : ∀ l, N < l → h l = 0) :
    ∑ k ∈ Icc 1 N, h (j + k) = ∑ l ∈ range (N + 1), if j < l then h l else 0 := by
  rw [← sum_filter, show (range (N + 1)).filter (fun l => j < l) = Icc (j + 1) N by
    ext l; simp only [mem_filter, mem_range, mem_Icc]; omega]
  rw [show ∑ k ∈ Icc 1 N, h (j + k) = ∑ l ∈ Icc (j + 1) (j + N), h l by
    rw [← map_add_left_Icc, sum_map]; rfl]
  symm
  refine sum_subset (Icc_subset_Icc le_rfl (by omega)) fun l hl hnot => hvan l ?_
  simp only [mem_Icc] at hl hnot; omega

/-- **One ladder.** If `x` restricted to the `p`-ladder of `u` is orthogonal to the pole profile
`p^{−j/2}`, its ladder defect is at least `(1 + 1/p)` times its mass. The defect dominates the
Lagrange minors `(p^{−j/2} x_l − p^{−l/2} x_j)²`, whose sum is `|b|²|x|² − ⟨b, x⟩²`, and
`|b|² ≥ 1 + 1/p` as soon as the ladder has two rungs. -/
theorem sum_ladder_sq_le_of_orthogonal {p : ℕ} (hp : p.Prime) {N u : ℕ} (hu : 1 ≤ u)
    (huN : u ≤ N) (x : ℕ → ℝ)
    (horth : ∑ j ∈ range (N + 1),
      (if u * p ^ j ≤ N then x (u * p ^ j) / Real.sqrt ((p ^ j : ℕ) : ℝ) else 0) = 0) :
    (1 + 1 / (p : ℝ)) * ∑ j ∈ range (N + 1), (if u * p ^ j ≤ N then x (u * p ^ j) ^ 2 else 0) ≤
      ∑ j ∈ range (N + 1), if u * p ^ j ≤ N then
        ∑ k ∈ Icc 1 N, (if u * p ^ j * p ^ k ≤ N then
          (x (u * p ^ j * p ^ k) - x (u * p ^ j) / Real.sqrt ((p ^ k : ℕ) : ℝ)) ^ 2 else 0)
      else 0 := by
  set R := range (N + 1)
  set B : ℕ → ℝ := fun j => if u * p ^ j ≤ N then 1 / Real.sqrt ((p ^ j : ℕ) : ℝ) else 0 with hBdef
  set Y : ℕ → ℝ := fun j => if u * p ^ j ≤ N then x (u * p ^ j) else 0 with hYdef
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hdown : ∀ j l, j ≤ l → u * p ^ l ≤ N → u * p ^ j ≤ N := fun j l hjl h =>
    le_trans (Nat.mul_le_mul_left u (Nat.pow_le_pow_right hp.pos hjl)) h
  have hbig : ∀ l, N < l → ¬ u * p ^ l ≤ N := by
    intro l hl h
    have h1 : l < p ^ l := Nat.lt_pow_self hp.one_lt
    have h2 : p ^ l ≤ u * p ^ l := Nat.le_mul_of_pos_left _ hu
    omega
  have hsqrt_pos : ∀ j : ℕ, 0 < Real.sqrt ((p ^ j : ℕ) : ℝ) := fun j =>
    Real.sqrt_pos.mpr (by have := Nat.one_le_pow j p hp.pos; positivity)
  have hBY : ∑ j ∈ R, B j * Y j = 0 := by
    rw [← horth]; refine sum_congr rfl fun j _ => ?_
    simp only [hBdef, hYdef]; split_ifs <;> ring
  have hYY : ∑ j ∈ R, Y j ^ 2 = ∑ j ∈ R, (if u * p ^ j ≤ N then x (u * p ^ j) ^ 2 else 0) :=
    sum_congr rfl fun j _ => by simp only [hYdef]; split_ifs <;> ring
  -- each edge dominates its Lagrange minor
  have hminor : ∀ j k, u * p ^ j ≤ N → (B j * Y (j + k) - B (j + k) * Y j) ^ 2 ≤
      if u * p ^ j * p ^ k ≤ N then
        (x (u * p ^ j * p ^ k) - x (u * p ^ j) / Real.sqrt ((p ^ k : ℕ) : ℝ)) ^ 2 else 0 := by
    intro j k hj
    have hjk : u * p ^ j * p ^ k = u * p ^ (j + k) := by rw [pow_add, mul_assoc]
    rw [hjk]
    by_cases hl : u * p ^ (j + k) ≤ N
    · simp only [hBdef, hYdef, if_pos hj, if_pos hl]
      set s := Real.sqrt ((p ^ j : ℕ) : ℝ)
      set r := Real.sqrt ((p ^ k : ℕ) : ℝ)
      have hs := hsqrt_pos j
      have hr := hsqrt_pos k
      have hsl : Real.sqrt ((p ^ (j + k) : ℕ) : ℝ) = s * r := by
        rw [pow_add, Nat.cast_mul, Real.sqrt_mul (by positivity)]
      have hs1 : 1 ≤ s := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.one_le_pow _ _ hp.pos)
      rw [hsl]
      have key : 1 / s * x (u * p ^ (j + k)) - 1 / (s * r) * x (u * p ^ j) =
          (x (u * p ^ (j + k)) - x (u * p ^ j) / r) / s := by field_simp
      rw [key, div_pow]
      exact div_le_self (sq_nonneg _) (by nlinarith)
    · have hz : (B j * Y (j + k) - B (j + k) * Y j) ^ 2 = 0 := by
        simp only [hBdef, hYdef, if_neg hl]; ring
      rw [hz, if_neg hl]
  -- the ladder defect dominates half the Lagrange double sum
  have hvan : ∀ j l, N < l → (B j * Y l - B l * Y j) ^ 2 = 0 := by
    intro j l hl
    simp only [hBdef, hYdef, if_neg (hbig l hl)]; ring
  have hrow : ∀ j ∈ R, ∑ l ∈ R, (if j < l then (B j * Y l - B l * Y j) ^ 2 else 0) ≤
      if u * p ^ j ≤ N then
        ∑ k ∈ Icc 1 N, (if u * p ^ j * p ^ k ≤ N then
          (x (u * p ^ j * p ^ k) - x (u * p ^ j) / Real.sqrt ((p ^ k : ℕ) : ℝ)) ^ 2 else 0)
      else 0 := by
    intro j _
    rw [← sum_Icc_shift j N (fun l => (B j * Y l - B l * Y j) ^ 2) (hvan j)]
    by_cases hj : u * p ^ j ≤ N
    · rw [if_pos hj]
      exact sum_le_sum fun k _ => hminor j k hj
    · rw [if_neg hj]
      refine le_of_eq (sum_eq_zero fun k _ => ?_)
      simp only [hBdef, hYdef, if_neg hj]; ring
  have hhalf : ∑ j ∈ R, ∑ l ∈ R, (if j < l then (B j * Y l - B l * Y j) ^ 2 else 0) =
      (∑ j ∈ R, ∑ l ∈ R, (B j * Y l - B l * Y j) ^ 2) / 2 := by
    have hsplit : ∀ j l, (B j * Y l - B l * Y j) ^ 2 =
        (if j < l then (B j * Y l - B l * Y j) ^ 2 else 0) +
          (if l < j then (B l * Y j - B j * Y l) ^ 2 else 0) := by
      intro j l
      rcases lt_trichotomy j l with h | rfl | h
      · rw [if_pos h, if_neg (by omega), add_zero]
      · simp
      · rw [if_neg (by omega), if_pos h, zero_add]; ring
    have hS : ∑ j ∈ R, ∑ l ∈ R, (B j * Y l - B l * Y j) ^ 2 =
        ∑ j ∈ R, ∑ l ∈ R, (if j < l then (B j * Y l - B l * Y j) ^ 2 else 0) +
          ∑ j ∈ R, ∑ l ∈ R, (if l < j then (B l * Y j - B j * Y l) ^ 2 else 0) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun j _ => by
        rw [← sum_add_distrib]; exact sum_congr rfl fun l _ => hsplit j l
    have hswap : ∑ j ∈ R, ∑ l ∈ R, (if l < j then (B l * Y j - B j * Y l) ^ 2 else 0) =
        ∑ j ∈ R, ∑ l ∈ R, (if j < l then (B j * Y l - B l * Y j) ^ 2 else 0) := sum_comm
    rw [hS, hswap]; ring
  have hlag := sum_sum_minor_sq R B Y
  rw [hBY] at hlag
  have hYnn : 0 ≤ ∑ j ∈ R, Y j ^ 2 := sum_nonneg fun j _ => sq_nonneg _
  have hmain : (∑ j ∈ R, B j ^ 2) * ∑ j ∈ R, Y j ^ 2 ≤
      ∑ j ∈ R, if u * p ^ j ≤ N then
        ∑ k ∈ Icc 1 N, (if u * p ^ j * p ^ k ≤ N then
          (x (u * p ^ j * p ^ k) - x (u * p ^ j) / Real.sqrt ((p ^ k : ℕ) : ℝ)) ^ 2 else 0)
      else 0 := by
    have := sum_le_sum hrow
    rw [hhalf, hlag] at this
    linarith
  have hB0 : B 0 = 1 := by simp only [hBdef, pow_zero, mul_one, if_pos huN]; simp
  rw [← hYY]
  by_cases h1 : u * p ^ 1 ≤ N
  · -- two rungs: `ΣB² ≥ B₀² + B₁² = 1 + 1/p`
    have hB1 : B 1 ^ 2 = 1 / p := by
      simp only [hBdef, if_pos h1, pow_one, div_pow, one_pow]
      rw [Real.sq_sqrt (by positivity)]
    have hN1 : 1 ∈ R := mem_range.mpr (by
      have : u * p ≤ N := by simpa using h1
      have : p ≤ u * p := Nat.le_mul_of_pos_left _ hu
      have := hp.two_le
      omega)
    have hsub : ({0, 1} : Finset ℕ) ⊆ R := by
      intro j hj
      simp only [mem_insert, mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact mem_range.mpr (by omega)
      · exact hN1
    have hBsum : 1 + 1 / (p : ℝ) ≤ ∑ j ∈ R, B j ^ 2 := by
      have := sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => sq_nonneg (B j)
      rw [sum_pair (by norm_num), hB0, hB1] at this
      linarith
    exact (mul_le_mul_of_nonneg_right hBsum hYnn).trans hmain
  · -- one rung: orthogonality kills it
    have hzero : ∀ j ∈ R, j ≠ 0 → ¬ u * p ^ j ≤ N := fun j _ hj h =>
      h1 (hdown 1 j (by omega) h)
    have hY0 : Y 0 = 0 := by
      have h := hBY
      rw [sum_eq_single 0 (fun j hj hj0 => by simp only [hBdef, if_neg (hzero j hj hj0)]; ring)
        (fun h0 => absurd (mem_range.mpr (by omega)) h0), hB0, one_mul] at h
      exact h
    have hYsum : ∑ j ∈ R, Y j ^ 2 = 0 := by
      rw [sum_eq_single 0 (fun j hj hj0 => by simp only [hYdef, if_neg (hzero j hj hj0)]; ring)
        (fun h0 => absurd (mem_range.mpr (by omega)) h0), hY0]
      ring
    rw [hYsum, mul_zero]
    have hBnn : 0 ≤ ∑ j ∈ R, B j ^ 2 := sum_nonneg fun j _ => sq_nonneg _
    nlinarith [hmain]

/-- **The ladder defect controls the mass off the ladder poles**: if `x` is orthogonal to the pole
profile on every `p`-ladder, `E_p(x) ≥ (1 + 1/p)|x|²`. -/
theorem ladderDefect_ge {p : ℕ} (hp : p.Prime) (N : ℕ) (x : ℕ → ℝ)
    (horth : ∀ u ∈ Icc 1 N, ¬ p ∣ u → ∑ j ∈ range (N + 1),
      (if u * p ^ j ≤ N then x (u * p ^ j) / Real.sqrt ((p ^ j : ℕ) : ℝ) else 0) = 0) :
    (1 + 1 / (p : ℝ)) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ ladderDefect p N x := by
  rw [sum_Icc_eq_sum_ladders hp N (fun n => x n ^ 2), ladderDefect,
    sum_Icc_eq_sum_ladders hp N (fun m => ∑ k ∈ Icc 1 N, if m * p ^ k ≤ N then
      (x (m * p ^ k) - x m / Real.sqrt ((p ^ k : ℕ) : ℝ)) ^ 2 else 0), mul_sum]
  refine sum_le_sum fun u hu => ?_
  obtain ⟨hu', hpu⟩ := mem_filter.mp hu
  exact sum_ladder_sq_le_of_orthogonal hp (mem_Icc.mp hu').1 (mem_Icc.mp hu').2 x
    (horth u hu' hpu)

/-- **The Hodge index of the prime form modulo a prime.** Let `V_p` be spanned by the pole profiles
`p^{−j/2}` of the `p`-ladders `{u p^j}`. For every prime `p` and `ε > 0`, eventually in `N`, every
`x ⊥ V_p` has `P_N(x) ≤ (log N − γ − (1 + 1/p) log p + ε)|x|²`: on the whole space, not only on
class profiles, the top of the prime form drops by at least `(1 + 1/p) log p` off the ladder poles.
The deficit is the pole defect, whose `p`-power edges carry `log p · E_p(x) ≥ (1 + 1/p) log p |x|²`. -/
theorem eventually_atomicWeilForm_le_of_ladderOrthogonal {p : ℕ} (hp : p.Prime) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ x : ℕ → ℝ,
      (∀ u ∈ Icc 1 N, ¬ p ∣ u → ∑ j ∈ range (N + 1),
        (if u * p ^ j ≤ N then x (u * p ^ j) / Real.sqrt ((p ^ j : ℕ) : ℝ) else 0) = 0) →
      atomicWeilForm N x ≤
        (Real.log N - γ - (1 + 1 / (p : ℝ)) * Real.log p + ε) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  set L := Real.log p
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
  set e : ℝ := min (ε / (1 + 2 * L)) (1 / 2) with he
  have he0 : 0 < e := lt_min (by positivity) (by norm_num)
  have he1 : e ≤ 1 / 2 := min_le_right _ _
  have heε : e * (1 + 2 * L) ≤ ε := (le_div_iff₀ (by positivity)).mp (min_le_left _ _)
  obtain ⟨N₀, hN₀⟩ := eventually_atomicWeilForm_add_poleDefect_le he0
  refine ⟨N₀, fun N hN x horth => ?_⟩
  have h := hN₀ N hN x
  have hE := ladderDefect_ge hp N x horth
  have hD := log_mul_ladderDefect_le hp N x
  set X := ∑ n ∈ Icc 1 N, x n ^ 2
  have hX : 0 ≤ X := sum_nonneg fun n _ => sq_nonneg (x n)
  have hp2 : (1 : ℝ) + 1 / p ≤ 2 := by
    have : (1 : ℝ) / p ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hp.pos)]; exact_mod_cast hp.one_lt.le
    linarith
  have hDlow : (1 + 1 / (p : ℝ)) * L * X ≤ poleDefect N x := by
    have := mul_le_mul_of_nonneg_left hE hL.le
    nlinarith
  have k1 := mul_le_mul_of_nonneg_left hDlow (by linarith : (0 : ℝ) ≤ 1 - e)
  have k2 : (e + e * ((1 + 1 / (p : ℝ)) * L)) * X ≤ ε * X := by
    refine mul_le_mul_of_nonneg_right ?_ hX
    have : e * ((1 + 1 / (p : ℝ)) * L) ≤ e * (2 * L) :=
      mul_le_mul_of_nonneg_left (by nlinarith) he0.le
    linarith
  nlinarith

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
