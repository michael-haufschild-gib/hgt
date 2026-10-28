import GaloisForLFunctions.ArithmeticIntersectionTheory.TheHeckeCocycleOfRenormalization
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheTorsionCountertermIsTheGoldenRatio
import GaloisForLFunctions.RHTower.CreaseBudgetPrimeMass

/-!
# The positive squares of the torsion form live below `N^{4/5}`

The renormalized torsion form `R_N(x) = −P_N(x) − Σ_{n ≤ N} c(n) x_n²`, `c(n) = I(n, n)/φ(n) =
log n − d(n)` with `d` the tame different, has at least `N^{1/5 − o(1)}` positive squares
(`TheTorsionFormHasPolynomiallyManyPositiveSquares`). This file bounds their number from above.

* **Diagonal domination** (`renormalizedTorsionForm_le_diag`): for every `x`,
  `R_N(x) ≤ Σ_n (2A(⌊N/n⌋) + d(n) − ½ log n) x_n²`, with `A(y) = Σ_{t ≤ y} Λ(t)/t`.
* **The index bound** (`finrank_le_of_renormalizedTorsionForm_pos`): every subspace on which `R_N` is
  positive definite has dimension at most `#{n ≤ N : 2A(⌊N/n⌋) + d(n) > ½ log n}`.
* **The exponent** (`eventually_finrank_le_rpow`): for every `ε > 0`, eventually in `N`, that number
  is at most `N^{4/5 + ε}`: the rows `2A(N/n) ≈ 2 log(N/n)` beat `½ log n` only below `n ≈ N^{4/5}`,
  and `d(n) ≤ 2 log K + 2 log 4 + 2 log n/K` for every `K` makes the tame different negligible.

**Proof of the domination.** The ground-state identity `P_N + D_N = Σ (A(⌊N/n⌋) + log n) x_n²` and
the edge bound `(a − b)² ≤ (3/2)a² + 3b²` (`0 ≤ ½(a + 2b)²`) on each pole relation
`x_{mt} − x_m/√t` give `D_N ≤ (3/2) Σ log n · x² + 3 Σ A x²`, i.e. `P_N ≥ −½ Σ log n · x² − 2 Σ A x²`.
The split `θ = ½` is optimal: `(1 − θ + 1/θ) u ≥ 1/θ` first holds at `u = 4/5`.
-/

noncomputable section

open Finset Filter

namespace GaloisForLFunctions.ArithmeticIntersectionTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-! ### 1. Diagonal domination -/

/-- The edge bound: `D_N ≤ (3/2) Σ log n · x² + 3 Σ A(⌊N/m⌋) x_m²`. -/
theorem poleDefect_le_diag (N : ℕ) (x : ℕ → ℝ) :
    poleDefect N x ≤ 3 / 2 * ∑ n ∈ Icc 1 N, Real.log n * x n ^ 2 +
      3 * ∑ m ∈ Icc 1 N, mertensSum (N / m) * x m ^ 2 := by
  rw [sum_log_mul_sq_eq_edges, mul_sum, mul_sum, ← sum_add_distrib, poleDefect]
  refine sum_le_sum fun m _ => ?_
  rw [mertensSum, sum_mul, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun t ht => ?_
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (mem_Icc.mp ht).1
  have hΛ : 0 ≤ Λ t := vonMangoldt_nonneg
  have hsq : (x m / Real.sqrt t) ^ 2 = x m ^ 2 / t := by
    rw [div_pow, Real.sq_sqrt ht0.le]
  have hedge : (x (m * t) - x m / Real.sqrt t) ^ 2 ≤
      3 / 2 * x (m * t) ^ 2 + 3 * (x m / Real.sqrt t) ^ 2 := by
    nlinarith [sq_nonneg (x (m * t) + 2 * (x m / Real.sqrt t))]
  rw [hsq] at hedge
  have := mul_le_mul_of_nonneg_left hedge hΛ
  have e : Λ t * (3 / 2 * x (m * t) ^ 2 + 3 * (x m ^ 2 / t)) =
      3 / 2 * (Λ t * x (m * t) ^ 2) + 3 * (Λ t / t * x m ^ 2) := by ring
  linarith

/-- **Diagonal domination of the torsion form**:
`R_N(x) ≤ Σ_n (2A(⌊N/n⌋) + d(n) − ½ log n) x_n²`. -/
theorem renormalizedTorsionForm_le_diag (N : ℕ) (x : ℕ → ℝ) :
    renormalizedTorsionForm (Icc 1 N) x ≤
      ∑ n ∈ Icc 1 N, (2 * mertensSum (N / n) + tameDifferent n - Real.log n / 2) * x n ^ 2 := by
  have hgs := atomicWeilForm_add_poleDefect N x
  have hD := poleDefect_le_diag N x
  have hself : ∑ n ∈ Icc 1 N, x n ^ 2 * selfIntersection n =
      ∑ n ∈ Icc 1 N, Real.log n * x n ^ 2 - ∑ n ∈ Icc 1 N, tameDifferent n * x n ^ 2 := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun n hn => ?_
    rw [selfIntersection_eq (mem_Icc.mp hn).1]
    ring
  have hR : renormalizedTorsionForm (Icc 1 N) x =
      -atomicWeilForm N x - ∑ n ∈ Icc 1 N, x n ^ 2 * selfIntersection n := rfl
  have hrows : ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * x n ^ 2 =
      ∑ n ∈ Icc 1 N, mertensSum (N / n) * x n ^ 2 + ∑ n ∈ Icc 1 N, Real.log n * x n ^ 2 := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun n _ => by ring
  have hgoal : ∑ n ∈ Icc 1 N, (2 * mertensSum (N / n) + tameDifferent n - Real.log n / 2) *
      x n ^ 2 = 2 * ∑ n ∈ Icc 1 N, mertensSum (N / n) * x n ^ 2 +
        ∑ n ∈ Icc 1 N, tameDifferent n * x n ^ 2 - (∑ n ∈ Icc 1 N, Real.log n * x n ^ 2) / 2 := by
    rw [mul_sum, sum_div, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [hR, hself, hgoal]
  linarith

/-! ### 2. The index bound -/

/-- The set of atoms where the dominating diagonal is positive. -/
def torsionPositiveAtoms (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter fun n => 0 < 2 * mertensSum (N / n) + tameDifferent n - Real.log n / 2

/-- **The positive index is at most the number of positive diagonal atoms.** -/
theorem finrank_le_of_renormalizedTorsionForm_pos (N : ℕ) (V : Submodule ℝ (ℕ → ℝ))
    (hV : ∀ v ∈ V, v ≠ 0 → 0 < renormalizedTorsionForm (Icc 1 N) v) :
    Module.finrank ℝ V ≤ (torsionPositiveAtoms N).card := by
  -- restriction to the positive atoms is injective on `V`
  let ρ : V →ₗ[ℝ] (torsionPositiveAtoms N → ℝ) :=
    { toFun := fun v s => (v : ℕ → ℝ) s
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ρ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hne
    have hv0 : (v : ℕ → ℝ) ≠ 0 := fun h => hne (Subtype.ext h)
    have hpos := hV v v.2 hv0
    have hzero : ∀ n ∈ torsionPositiveAtoms N, (v : ℕ → ℝ) n = 0 := fun n hn =>
      congrFun hv ⟨n, hn⟩
    have hle := renormalizedTorsionForm_le_diag N v
    have hnp : ∑ n ∈ Icc 1 N, (2 * mertensSum (N / n) + tameDifferent n - Real.log n / 2) *
        (v : ℕ → ℝ) n ^ 2 ≤ 0 := by
      refine sum_nonpos fun n hn => ?_
      by_cases h : n ∈ torsionPositiveAtoms N
      · rw [hzero n h]; simp
      · have : 2 * mertensSum (N / n) + tameDifferent n - Real.log n / 2 ≤ 0 := by
          by_contra hc
          exact h (mem_filter.mpr ⟨hn, lt_of_not_ge hc⟩)
        exact mul_nonpos_of_nonpos_of_nonneg this (sq_nonneg _)
    linarith
  calc Module.finrank ℝ V ≤ Module.finrank ℝ (torsionPositiveAtoms N → ℝ) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = (torsionPositiveAtoms N).card := by simp

/-! ### 3. The exponent `4/5` -/

/-- The tame different is small: `d(n) ≤ 2 log K + 2 log 4 + 2 log n/K` for every `K ≥ 1`. -/
theorem tameDifferent_le_split {n K : ℕ} (hn : 0 < n) (hK : 1 ≤ K) :
    tameDifferent n ≤ 2 * Real.log K + 2 * Real.log 4 + 2 * Real.log n / K := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hterm : ∀ p ∈ n.primeFactors, Real.log p / ((p : ℝ) - 1) ≤ 2 * (Real.log p / p) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    rw [div_le_iff₀ (by linarith), mul_comm 2, mul_assoc, div_mul_eq_mul_div,
      le_div_iff₀ (by linarith)]
    nlinarith
  rw [tameDifferent, ← sum_filter_add_sum_filter_not n.primeFactors (fun p => p ≤ K)]
  have hsmall : ∑ p ∈ n.primeFactors.filter (fun p => p ≤ K), Real.log p / ((p : ℝ) - 1) ≤
      2 * Real.log K + 2 * Real.log 4 := by
    calc ∑ p ∈ n.primeFactors.filter (fun p => p ≤ K), Real.log p / ((p : ℝ) - 1)
        ≤ ∑ p ∈ n.primeFactors.filter (fun p => p ≤ K), 2 * (Real.log p / p) :=
          sum_le_sum fun p hp => hterm p (mem_filter.mp hp).1
      _ ≤ ∑ p ∈ Nat.primesBelow (K + 1), 2 * (Real.log p / p) := by
          refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ => ?_
          · obtain ⟨hp1, hpK⟩ := mem_filter.mp hp
            exact Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_of_mem_primeFactors hp1⟩
          · exact mul_nonneg (by norm_num) (div_nonneg (Real.log_natCast_nonneg p)
              (Nat.cast_nonneg p))
      _ = 2 * ∑ p ∈ Nat.primesBelow (K + 1), Real.log p / p := by rw [mul_sum]
      _ ≤ 2 * Real.log K + 2 * Real.log 4 := by
          have := RHTower.mertens_first_upper hK
          linarith
  have hlarge : ∑ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K), Real.log p / ((p : ℝ) - 1) ≤
      2 * Real.log n / K := by
    have hprod : ∑ p ∈ n.primeFactors, Real.log p ≤ Real.log n := by
      rw [← Real.log_prod (fun p hp => by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
      have hd := Nat.prod_primeFactors_dvd n
      have hle : ∏ p ∈ n.primeFactors, p ≤ n := Nat.le_of_dvd hn hd
      rw [← Nat.cast_prod]
      exact Real.log_le_log (by
        have : 0 < ∏ p ∈ n.primeFactors, p :=
          prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
        exact_mod_cast this) (by exact_mod_cast hle)
    calc ∑ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K), Real.log p / ((p : ℝ) - 1)
        ≤ ∑ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K), 2 / K * Real.log p := by
          refine sum_le_sum fun p hp => ?_
          obtain ⟨hp1, hpK⟩ := mem_filter.mp hp
          have hpK' : (K : ℝ) ≤ p := by exact_mod_cast (not_le.mp hpK).le
          have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
          refine (hterm p hp1).trans ?_
          rw [mul_div_assoc', div_mul_eq_mul_div, mul_comm (2 : ℝ) (Real.log p)]
          exact div_le_div_of_nonneg_left (by positivity) hK0 hpK'
      _ ≤ ∑ p ∈ n.primeFactors, 2 / K * Real.log p :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            fun p _ _ => mul_nonneg (by positivity) (Real.log_natCast_nonneg p)
      _ = 2 / K * ∑ p ∈ n.primeFactors, Real.log p := by rw [mul_sum]
      _ ≤ 2 / K * Real.log n := mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = 2 * Real.log n / K := by ring
  linarith

/-- **The positive squares of the torsion form live below `N^{4/5}`.** For every `ε > 0`,
eventually in `N`, every subspace on which the renormalized torsion form of `[1, N]` is positive
definite has dimension at most `N^{4/5 + ε}`. -/
theorem eventually_finrank_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ V : Submodule ℝ (ℕ → ℝ),
      (∀ v ∈ V, v ≠ 0 → 0 < renormalizedTorsionForm (Icc 1 N) v) →
        (Module.finrank ℝ V : ℝ) ≤ (N : ℝ) ^ ((4 : ℝ) / 5 + ε) := by
  set C₀ := Real.log 4 + 4
  set K : ℕ := ⌈8 / ε⌉₊ + 1
  have hK1 : 1 ≤ K := by omega
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hKε : 2 / (K : ℝ) ≤ ε / 4 := by
    have : 8 / ε < K := by
      have := Nat.le_ceil (8 / ε)
      have : ((⌈8 / ε⌉₊ : ℕ) : ℝ) + 1 = K := by simp [K]
      linarith
    rw [div_le_iff₀ hK0]
    rw [div_lt_iff₀ hε] at this
    linarith
  -- eventually `log N` absorbs the constants
  set B := 2 * C₀ + 2 * Real.log K + 2 * Real.log 4
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (max 1 (4 * B / ε)))
  refine ⟨max N₀ 2, fun N hN V hV => ?_⟩
  have hL := hN₀ N (le_of_max_le_left hN)
  simp only [Function.comp] at hL
  have hL1 : 1 ≤ Real.log N := (le_max_left _ _).trans hL
  have hLB : 4 * B / ε ≤ Real.log N := (le_max_right _ _).trans hL
  have hN2 : 2 ≤ N := le_of_max_le_right hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hB : B ≤ ε / 4 * Real.log N := by
    rw [div_le_iff₀ hε] at hLB
    linarith
  -- the positive atoms lie below `exp((4/5)(log N + …))`
  set T : ℝ := Real.exp ((2 / 5) * ((2 + ε) * Real.log N))
  have hsub : torsionPositiveAtoms N ⊆ Icc 1 ⌊T⌋₊ := by
    intro n hn
    obtain ⟨hnI, hpos⟩ := mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hnI
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hrow := row_le (show 0 < n by omega) hnN
    have hd := tameDifferent_le_split (show 0 < n by omega) hK1
    have hlogn : Real.log n ≤ Real.log N := Real.log_le_log hn0 (by exact_mod_cast hnN)
    have hdl : 2 * Real.log n / K ≤ ε / 4 * Real.log N := by
      have : 2 * Real.log n / K = 2 / K * Real.log n := by ring
      rw [this]
      exact (mul_le_mul_of_nonneg_left hlogn (by positivity)).trans
        (mul_le_mul_of_nonneg_right hKε (by linarith))
    -- `½ log n < 2 A + d ≤ 2(log N − log n + C₀) + d`
    have key : 5 / 2 * Real.log n < (2 + ε) * Real.log N := by
      simp only [C₀, B] at hB
      have := mul_nonneg hε.le (show (0 : ℝ) ≤ Real.log N by linarith)
      linarith
    refine mem_Icc.mpr ⟨hn1, Nat.le_floor ?_⟩
    calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hn0).symm
      _ ≤ T := Real.exp_le_exp.mpr (by linarith)
  have hcard : ((torsionPositiveAtoms N).card : ℝ) ≤ T := by
    have h1 := card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
    exact (by exact_mod_cast h1 : ((torsionPositiveAtoms N).card : ℝ) ≤ ⌊T⌋₊).trans
      (Nat.floor_le (Real.exp_pos _).le)
  have hT : T ≤ (N : ℝ) ^ ((4 : ℝ) / 5 + ε) := by
    rw [Real.rpow_def_of_pos hN0]
    refine Real.exp_le_exp.mpr ?_
    have := mul_nonneg hε.le (show (0 : ℝ) ≤ Real.log N by linarith)
    linarith
  calc (Module.finrank ℝ V : ℝ) ≤ (torsionPositiveAtoms N).card := by
        exact_mod_cast finrank_le_of_renormalizedTorsionForm_pos N V hV
    _ ≤ T := hcard
    _ ≤ (N : ℝ) ^ ((4 : ℝ) / 5 + ε) := hT

end GaloisForLFunctions.ArithmeticIntersectionTheory
