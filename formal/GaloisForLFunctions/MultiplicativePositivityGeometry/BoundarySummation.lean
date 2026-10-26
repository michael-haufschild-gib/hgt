import GaloisForLFunctions.MultiplicativePositivityGeometry.BoundaryDivisorRange
import GaloisForLFunctions.MultiplicativePositivityGeometry.BoundaryCalculus

/-!
# Countable sums of boundary divisors and boundary divisors with dense support

* **σ-additivity** (`isBoundaryDivisor_tsum`). If `D_k` are boundary divisors with
  `Σ_k D_k(0) < ∞`, then `Σ_k D_k` is a boundary divisor. Each `D_k` is a pointwise limit of positive
  cosine polynomials `P_{k,n}`; dropping the first terms of each sequence makes
  `|P_{k,n}| ≤ P_{k,n}(0) ≤ D_k(0) + 2^{−k}`, and Tannery's theorem passes the limit through the
  positive cosine polynomials `Σ_{k ≤ n} P_{k,n}`.
* **Dense support** (`ratLattice_isBoundaryDivisor`, `ratLattice_ne_zero_iff`). The lattice
  indicators of `(2π/(n+1)!)ℤ` are boundary divisors, so `Σ_n 2^{−n} 1_{(2π/(n+1)!)ℤ}` is a boundary
  divisor; it is positive exactly on the dense subgroup `2πℚ`.

So local finiteness is not a property of boundary divisors: dense supports occur. They cannot carry
integer values with a simple pole (`boundary_tetrachotomy`), and they cannot be the indicator of
`2πℚ` itself, which is not a pointwise limit of continuous functions.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-! ### Positive cosine polynomials -/

theorem isPosCosPoly_zero : IsPosCosPoly fun _ => 0 :=
  ⟨0, fun _ => 0, fun _ => 0, fun _ => le_rfl, fun u => by simp⟩

theorem IsPosCosPoly.add {P Q : ℝ → ℝ} (hP : IsPosCosPoly P) (hQ : IsPosCosPoly Q) :
    IsPosCosPoly fun u => P u + Q u := by
  obtain ⟨N, c, lam, hc, hP⟩ := hP
  obtain ⟨M, d, mu, hd, hQ⟩ := hQ
  have h := isPosCosPoly_finset_sum ((range N).disjSum (range M)) (Sum.elim c d) (Sum.elim lam mu)
    fun i _ => by cases i <;> simp [hc, hd]
  convert h using 2 with u
  rw [Finset.sum_disjSum, hP, hQ]
  rfl

theorem isPosCosPoly_sum {P : ℕ → ℝ → ℝ} (hP : ∀ k, IsPosCosPoly (P k)) (s : Finset ℕ) :
    IsPosCosPoly fun u => ∑ k ∈ s, P k u := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPosCosPoly_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hP a).add ih

/-- A positive cosine polynomial is bounded by its value at `0`. -/
theorem IsPosCosPoly.abs_le {P : ℝ → ℝ} (hP : IsPosCosPoly P) (u : ℝ) : |P u| ≤ P 0 := by
  obtain ⟨N, c, lam, hc, hP⟩ := hP
  rw [hP, hP]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_of_nonneg (hc i), mul_zero, Real.cos_zero, mul_one]
  exact mul_le_of_le_one_right (hc i) (Real.abs_cos_le_one _)

/-! ### Countable sums -/

/-- **Countable sums of boundary divisors are boundary divisors** when the pole orders at the
origin are summable. -/
theorem isBoundaryDivisor_tsum {D : ℕ → ℝ → ℝ}
    (hD : ∀ k, ∃ (ι : Type) (lam : ι → ℝ) (w : ℝ → ι → ℝ), IsBoundaryDivisor lam w (D k))
    (hs : Summable fun k => D k 0) :
    ∃ (ι : Type) (lam : ι → ℝ) (w : ℝ → ι → ℝ), IsBoundaryDivisor lam w fun u => ∑' k, D k u := by
  classical
  choose P hP hlim using fun k => (isBoundaryDivisor_iff_tendsto_posCosPoly (D k)).mp (hD k)
  have hD0 : ∀ k, 0 ≤ D k 0 := fun k => by
    obtain ⟨_, _, _, h⟩ := hD k
    exact h.isEvenPosDef.apply_zero_nonneg
  -- From some index on, `P_{k,n}(0) ≤ D_k(0) + 2^{−k}`.
  have hstart : ∀ k, ∃ n₀, ∀ n ≥ n₀, P k n 0 ≤ D k 0 + (1 / 2) ^ k := fun k => by
    obtain ⟨n₀, hn₀⟩ := Metric.tendsto_atTop.mp (hlim k 0) ((1 / 2) ^ k) (by positivity)
    exact ⟨n₀, fun n hn => by
      have := hn₀ n hn
      rw [Real.dist_eq] at this
      linarith [(abs_lt.mp this).2]⟩
  choose n₀ hn₀ using hstart
  set P' : ℕ → ℕ → ℝ → ℝ := fun k n => if n₀ k ≤ n then P k n else fun _ => 0
  have hP' : ∀ k n, IsPosCosPoly (P' k n) := fun k n => by
    simp only [P']
    split_ifs
    · exact hP k n
    · exact isPosCosPoly_zero
  have hb : ∀ k n u, |P' k n u| ≤ D k 0 + (1 / 2) ^ k := fun k n u => by
    simp only [P']
    split_ifs with h
    · exact ((hP k n).abs_le u).trans (hn₀ k n h)
    · simpa using add_nonneg (hD0 k) (by positivity : (0 : ℝ) ≤ (1 / 2) ^ k)
  set Q : ℕ → ℝ → ℝ := fun n u => ∑ k ∈ range (n + 1), P' k n u
  have hlimQ : ∀ u, Tendsto (fun n => Q n u) atTop (𝓝 (∑' k, D k u)) := by
    intro u
    -- Tannery's theorem for `Σ_k [k ≤ n] P'_{k,n}(u)`.
    have hT := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun n k => if k ≤ n then P' k n u else 0) (g := fun k => D k u)
      (bound := fun k => D k 0 + (1 / 2) ^ k) (hs.add summable_geometric_two)
      (fun k => by
        refine (hlim k u).congr' ?_
        filter_upwards [eventually_ge_atTop (max k (n₀ k))] with n hn
        simp only [P', if_pos (le_of_max_le_left hn), if_pos (le_of_max_le_right hn)])
      (Eventually.of_forall fun n k => by
        rw [Real.norm_eq_abs]
        split_ifs
        · exact hb k n u
        · simpa using add_nonneg (hD0 k) (by positivity : (0 : ℝ) ≤ (1 / 2) ^ k))
    refine hT.congr fun n => ?_
    rw [tsum_eq_sum (s := range (n + 1)) fun k hk => by
      rw [Finset.mem_range, not_lt] at hk
      rw [if_neg (by omega)]]
    exact Finset.sum_congr rfl fun k hk => by rw [if_pos (by simpa [Nat.lt_succ_iff] using hk)]
  obtain ⟨lam, w, h⟩ := isBoundaryDivisor_of_tendsto_posCosPoly (P := Q)
    (fun n => isPosCosPoly_sum (hP' · n) _) hlimQ
  exact ⟨_, lam, w, h⟩

/-! ### A boundary divisor supported on `2πℚ` -/

open Classical in
/-- `Σ_n 2^{−n} 1_{(2π/(n+1)!)ℤ}`. -/
noncomputable def ratLattice (u : ℝ) : ℝ :=
  ∑' n : ℕ, (1 / 2) ^ n * (if ∃ m : ℤ, u = m * (2 * Real.pi / (n + 1).factorial) then 1 else 0)

theorem ratLattice_isBoundaryDivisor :
    ∃ (ι : Type) (lam : ι → ℝ) (w : ℝ → ι → ℝ), IsBoundaryDivisor lam w ratLattice := by
  classical
  refine isBoundaryDivisor_tsum (fun n => ?_) ?_
  · have hh : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos _
    exact ⟨_, _, _, (lattice_isBoundaryDivisor hh).smul (by positivity : (0 : ℝ) ≤ (1 / 2) ^ n)⟩
  · simpa using summable_geometric_two

/-- **Dense support.** `ratLattice` is positive exactly on `2πℚ`. -/
theorem ratLattice_ne_zero_iff (u : ℝ) : ratLattice u ≠ 0 ↔ ∃ q : ℚ, u = 2 * Real.pi * q := by
  classical
  have hterm : ∀ n : ℕ, 0 ≤ (1 / 2 : ℝ) ^ n *
      (if ∃ m : ℤ, u = m * (2 * Real.pi / (n + 1).factorial) then 1 else 0) := fun n => by
    split_ifs <;> positivity
  have hsum : Summable fun n : ℕ => (1 / 2 : ℝ) ^ n *
      (if ∃ m : ℤ, u = m * (2 * Real.pi / (n + 1).factorial) then 1 else 0) :=
    Summable.of_nonneg_of_le hterm (fun n => by
      split_ifs <;> simp) summable_geometric_two
  constructor
  · intro hne
    by_contra hq
    apply hne
    have h0 : ∀ n : ℕ, (1 / 2 : ℝ) ^ n *
        (if ∃ m : ℤ, u = m * (2 * Real.pi / (n + 1).factorial) then 1 else 0) = 0 := by
      intro n
      rw [if_neg, mul_zero]
      rintro ⟨m, hm⟩
      exact hq ⟨(m : ℚ) / (n + 1).factorial, by rw [hm]; push_cast; ring⟩
    simp only [ratLattice, h0, tsum_zero]
  · rintro ⟨q, rfl⟩
    set n := q.den - 1
    have hn : n + 1 = q.den := Nat.sub_add_cancel q.pos
    obtain ⟨c, hc⟩ := Nat.dvd_factorial q.pos hn.symm.le
    have hc0 : (c : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by
      rintro rfl
      rw [mul_zero] at hc
      exact (Nat.factorial_pos _).ne' hc)
    have hmem : ∃ m : ℤ, 2 * Real.pi * q = m * (2 * Real.pi / (n + 1).factorial) := by
      refine ⟨q.num * c, ?_⟩
      rw [hc, Rat.cast_def]
      push_cast
      have hden : (q.den : ℝ) ≠ 0 := by positivity
      field_simp
    have hpos : 0 < (1 / 2 : ℝ) ^ n *
        (if ∃ m : ℤ, 2 * Real.pi * q = m * (2 * Real.pi / (n + 1).factorial) then 1 else 0) := by
      rw [if_pos hmem]
      positivity
    exact (lt_of_lt_of_le hpos (hsum.le_tsum n fun j _ => hterm j)).ne'

end GaloisForLFunctions.MultiplicativePositivityGeometry
