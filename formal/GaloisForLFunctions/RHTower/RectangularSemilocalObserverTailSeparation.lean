import GaloisForLFunctions.RHTower.TraceClassOperatorTrace
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.PSeries

/-!
# Rectangular semilocal observer continuity does not supply cofinal tail control

Three unconditional facts, and one unconditional separation.

* **Exact coordinate stabilization `(2)`.**  A von Mangoldt weight is supported on prime powers, so
  the least prime factor of every visible index is at most that index.  Restricting a rectangular
  observer at cutoff `X` to prime powers whose prime is at most `X` therefore changes **nothing**
  for indices `n ≤ X`: prime-cutoff convergence is eventually exact, not merely pointwise.

* **Uniform trace-duality bound `(6)`.**  The trace pairing of a Schatten-1 operator with a
  uniformly bounded observer is bounded by the product of the operator bound and the trace norm; the
  observer contributes no aperture growth.

* **`(8)`–`(9)`.**  Hence the negative part of a compensated defect is controlled by the trace norm
  plus the negative part of the anomaly, and an all-`ε` subpower bound makes its square summable
  against `n^{-1-ε}`.

* **The separation `(10)`–`(12)`.**  Finite-level positivity, refinement compatibility, exact
  coordinate stabilization and finite-level summability at every exponent do **not** imply the
  cofinal tail estimate: the explicit triangular array `A_m = B_m + R_m` has all four properties and
  a cofinal remainder whose weighted mass diverges at every exponent `ε ≤ δ`.
-/

namespace RHTower

open scoped BigOperators
open Filter ContinuousLinearMap

noncomputable section

/-! ## `(2)` Exact coordinate stabilization -/

/-- The von Mangoldt weight is supported on indices whose least prime factor is at most the index
itself; in particular no visible prime exceeds the index. -/
theorem minFac_le_of_vonMangoldt_ne_zero {k : ℕ} (hk : ArithmeticFunction.vonMangoldt k ≠ 0) :
    k.minFac ≤ k := by
  have hpp : IsPrimePow k := by
    rwa [ArithmeticFunction.vonMangoldt_ne_zero_iff] at hk
  exact Nat.minFac_le hpp.pos

/-- **`(2)`: prime-cutoff convergence is eventually exact.**  For every index `n ≤ X`, discarding
the prime powers whose prime exceeds `X` changes no term of a rectangular von Mangoldt observer. -/
theorem vonMangoldt_primeCutoff_stabilizes (X n : ℕ) (hn : n ≤ X) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 n,
        (if k.minFac ≤ X then ArithmeticFunction.vonMangoldt k else 0) * f k
      = ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k * f k := by
  refine Finset.sum_congr rfl fun k hk => ?_
  by_cases hcut : k.minFac ≤ X
  · rw [if_pos hcut]
  · rw [if_neg hcut, zero_mul]
    have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
    have hzero : ArithmeticFunction.vonMangoldt k = 0 := by
      by_contra hne
      exact hcut ((minFac_le_of_vonMangoldt_ne_zero hne).trans (hkn.trans hn))
    rw [hzero, zero_mul]

/-! ## `(6)` The uniform trace-duality bound -/

section TraceDuality

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Schatten-1 is a right ideal. -/
theorem MemSchattenClass.one_comp_right {K : H →L[ℂ] H} (hK : MemSchattenClass 1 K)
    (A : H →L[ℂ] H) : MemSchattenClass 1 (K ∘L A) :=
  (summable_approxNumber_comp_right hK.one_summable_approxNumber A).congr fun _ =>
    (Real.rpow_one _).symm

/-- **`(6)`: trace duality against a uniformly bounded observer.**  No aperture growth. -/
theorem norm_opTrace_comp_le_norm_mul_traceNorm {K : H →L[ℂ] H} (hK : MemSchattenClass 1 K)
    (A : H →L[ℂ] H) :
    ‖opTrace (K ∘L A)‖ ≤ traceNorm H K * ‖A‖ := by
  refine (norm_opTrace_le_traceNorm (hK.one_comp_right A)).trans ?_
  exact traceNorm_comp_right_le hK.one_summable_approxNumber A

/-- `(6)` with an explicit observer bound `‖A‖ ≤ C`. -/
theorem norm_opTrace_comp_le_of_norm_le {K : H →L[ℂ] H} (hK : MemSchattenClass 1 K)
    {A : H →L[ℂ] H} {C : ℝ} (hA : ‖A‖ ≤ C) :
    ‖opTrace (K ∘L A)‖ ≤ traceNorm H K * C := by
  refine (norm_opTrace_comp_le_norm_mul_traceNorm hK A).trans ?_
  exact mul_le_mul_of_nonneg_left hA (traceNorm_nonneg K)

/-- **`(8)`: the negative part of a compensated defect.**  If `κ = Re Tr(K A) + c`, the negative
part of `κ` is at most `‖K‖₁ ‖A‖` plus the negative part of `c`. -/
theorem negPart_le_traceNorm_add {K : H →L[ℂ] H} (hK : MemSchattenClass 1 K)
    (A : H →L[ℂ] H) (c : ℝ) :
    max 0 (-((opTrace (K ∘L A)).re + c)) ≤ traceNorm H K * ‖A‖ + max 0 (-c) := by
  have hre : |(opTrace (K ∘L A)).re| ≤ traceNorm H K * ‖A‖ :=
    (Complex.abs_re_le_norm _).trans (norm_opTrace_comp_le_norm_mul_traceNorm hK A)
  have hlow : -(traceNorm H K * ‖A‖) ≤ (opTrace (K ∘L A)).re := by
    have := abs_le.mp hre
    linarith [this.1]
  have hcpos : 0 ≤ max 0 (-c) := le_max_left _ _
  have hcge : -c ≤ max 0 (-c) := le_max_right _ _
  refine max_le ?_ ?_
  · have : 0 ≤ traceNorm H K * ‖A‖ := mul_nonneg (traceNorm_nonneg K) (norm_nonneg A)
    linarith
  · linarith

end TraceDuality

/-! ## `(9)` A subpower bound makes the squared response summable -/

theorem summable_rpow_neg_succ {q : ℝ} (hq : 1 < q) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-q) := by
  have hbase : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ q :=
    Real.summable_one_div_nat_rpow.mpr hq
  have hshift := (summable_nat_add_iff 1).mpr hbase
  refine hshift.congr fun n => ?_
  push_cast
  rw [Real.rpow_neg (by positivity), one_div]

/-- **`(9)`: an all-`ε` subpower response makes the squared response summable against
`n^{-1-ε}`.** -/
theorem summable_sq_div_rpow_of_subpower {eps C : ℝ} (heps : 0 < eps)
    (a : ℕ → ℝ) (ha0 : ∀ n, 0 ≤ a n)
    (ha : ∀ n : ℕ, a n ≤ C * ((n : ℝ) + 1) ^ (eps / 4)) :
    Summable fun n : ℕ => (a n) ^ 2 * ((n : ℝ) + 1) ^ (-(1 + eps)) := by
  have hmaj : Summable fun n : ℕ => C ^ 2 * ((n : ℝ) + 1) ^ (-(1 + eps / 2)) :=
    (summable_rpow_neg_succ (q := 1 + eps / 2) (by linarith)).mul_left (C ^ 2)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmaj
  have hbase : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hsq : (a n) ^ 2 ≤ C ^ 2 * ((n : ℝ) + 1) ^ (eps / 2) := by
    have h1 : (a n) ^ 2 ≤ (C * ((n : ℝ) + 1) ^ (eps / 4)) ^ 2 :=
      pow_le_pow_left₀ (ha0 n) (ha n) 2
    have h2 : (C * ((n : ℝ) + 1) ^ (eps / 4)) ^ 2 = C ^ 2 * ((n : ℝ) + 1) ^ (eps / 2) := by
      rw [mul_pow, ← Real.rpow_natCast (((n : ℝ) + 1) ^ (eps / 4)) 2, ← Real.rpow_mul hbase.le]
      congr 2
      push_cast
      ring
    rw [← h2]
    exact h1
  calc (a n) ^ 2 * ((n : ℝ) + 1) ^ (-(1 + eps))
      ≤ (C ^ 2 * ((n : ℝ) + 1) ^ (eps / 2)) * ((n : ℝ) + 1) ^ (-(1 + eps)) :=
        mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hbase.le _)
    _ = C ^ 2 * ((n : ℝ) + 1) ^ (-(1 + eps / 2)) := by
        rw [mul_assoc, ← Real.rpow_add hbase]
        congr 2
        ring

/-! ## `(10)`–`(12)` Finite positivity does not imply the cofinal tail estimate -/

/-- The cutoff-`m` bulk coordinate `B_m(n) = n^δ · 1_{n ≤ m}`. -/
def separationBulk (delta : ℝ) (m n : ℕ) : ℝ :=
  if n ≤ m then ((n : ℝ) + 1) ^ delta else 0

/-- The cutoff-`m` defect coordinate `R_m(n) = -2 n^δ · 1_{n ≤ m}`. -/
def separationDefect (delta : ℝ) (m n : ℕ) : ℝ :=
  if n ≤ m then -2 * ((n : ℝ) + 1) ^ delta else 0

/-- The cutoff-`m` total `A_m(n) = -n^δ · 1_{n ≤ m}`. -/
def separationTotal (delta : ℝ) (m n : ℕ) : ℝ :=
  if n ≤ m then -((n : ℝ) + 1) ^ delta else 0

/-- `(11)`: the array splits as bulk plus defect. -/
theorem separationTotal_eq (delta : ℝ) (m n : ℕ) :
    separationTotal delta m n = separationBulk delta m n + separationDefect delta m n := by
  unfold separationTotal separationBulk separationDefect
  by_cases h : n ≤ m
  · rw [if_pos h, if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h, if_neg h]; ring

/-- `(11)`: the bulk is nonnegative. -/
theorem separationBulk_nonneg {delta : ℝ} (m n : ℕ) : 0 ≤ separationBulk delta m n := by
  unfold separationBulk
  by_cases h : n ≤ m
  · rw [if_pos h]; positivity
  · rw [if_neg h]

/-- Every coordinate stabilizes exactly once the cutoff passes it. -/
theorem separationTotal_stabilizes {delta : ℝ} {m n : ℕ} (h : n ≤ m) :
    separationTotal delta m n = -((n : ℝ) + 1) ^ delta := by
  unfold separationTotal
  rw [if_pos h]

/-- Enlarging the cutoff adds only bulk coordinates: the bulk is monotone in the cutoff. -/
theorem separationBulk_mono {delta : ℝ} {m m' : ℕ} (h : m ≤ m') (n : ℕ) :
    separationBulk delta m n ≤ separationBulk delta m' n := by
  unfold separationBulk
  by_cases hn : n ≤ m
  · rw [if_pos hn, if_pos (hn.trans h)]
  · rw [if_neg hn]
    by_cases hn' : n ≤ m'
    · rw [if_pos hn']; positivity
    · rw [if_neg hn']

/-- Every finite level has finite weighted Dirichlet energy at **every** exponent: the coordinate
family is finitely supported. -/
theorem summable_separationDefect (delta eps : ℝ) (m : ℕ) :
    Summable fun n : ℕ => |separationDefect delta m n| * ((n : ℝ) + 1) ^ (-(1 + eps)) := by
  refine summable_of_ne_finset_zero (s := Finset.range (m + 1)) fun n hn => ?_
  have hnm : ¬ n ≤ m := by
    simp only [Finset.mem_range, not_lt] at hn
    omega
  unfold separationDefect
  rw [if_neg hnm]
  simp

/-- Every coordinate of the defect converges to the cofinal value `-2 n^δ`. -/
theorem tendsto_separationDefect (delta : ℝ) (n : ℕ) :
    Tendsto (fun m => separationDefect delta m n) atTop
      (nhds (-2 * ((n : ℝ) + 1) ^ delta)) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  unfold separationDefect
  rw [if_pos hm]

/-- **`(12)`: the cofinal defect has infinite weighted mass at every exponent `ε ≤ δ`.** -/
theorem not_summable_separation_cofinal {delta eps : ℝ} (heps : eps ≤ delta) :
    ¬ Summable fun n : ℕ => 2 * ((n : ℝ) + 1) ^ delta * ((n : ℝ) + 1) ^ (-(1 + eps)) := by
  intro hsum
  have hharm : ¬ Summable fun n : ℕ => ((n : ℝ) + 1)⁻¹ := by
    intro hc
    have h1 : Summable fun n : ℕ => ((n : ℝ))⁻¹ := by
      refine (summable_nat_add_iff 1).mp ?_
      refine hc.congr fun n => ?_
      push_cast
      ring
    have h2 : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (1 : ℝ) := by
      refine h1.congr fun n => ?_
      rw [Real.rpow_one, one_div]
    exact absurd (Real.summable_one_div_nat_rpow.mp h2) (lt_irrefl 1)
  refine hharm ?_
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsum
  have hbase : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hcomb : 2 * ((n : ℝ) + 1) ^ delta * ((n : ℝ) + 1) ^ (-(1 + eps))
      = 2 * ((n : ℝ) + 1) ^ (delta - eps - 1) := by
    rw [mul_assoc, ← Real.rpow_add hpos]
    congr 2
    ring
  rw [hcomb]
  have hexp : ((n : ℝ) + 1) ^ (-(1 : ℝ)) ≤ ((n : ℝ) + 1) ^ (delta - eps - 1) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  have hinv : ((n : ℝ) + 1) ^ (-(1 : ℝ)) = ((n : ℝ) + 1)⁻¹ := by
    rw [Real.rpow_neg hpos.le, Real.rpow_one]
  rw [hinv] at hexp
  have h2 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (delta - eps - 1) := Real.rpow_nonneg hpos.le _
  linarith

/-- **The separation theorem `(10)`–`(12)`.**  All four finite-level properties hold, and the
cofinal weighted mass still diverges at every exponent `ε ≤ δ`. -/
theorem rectangular_finite_positivity_not_imply_tail {delta eps : ℝ} (heps : eps ≤ delta) :
    (∀ m n, separationTotal delta m n
        = separationBulk delta m n + separationDefect delta m n) ∧
      (∀ m n, 0 ≤ separationBulk delta m n) ∧
      (∀ m n, n ≤ m → separationTotal delta m n = -((n : ℝ) + 1) ^ delta) ∧
      (∀ e : ℝ, ∀ m, Summable fun n : ℕ =>
        |separationDefect delta m n| * ((n : ℝ) + 1) ^ (-(1 + e))) ∧
      (∀ n, Tendsto (fun m => separationDefect delta m n) atTop
        (nhds (-2 * ((n : ℝ) + 1) ^ delta))) ∧
      ¬ Summable fun n : ℕ =>
        2 * ((n : ℝ) + 1) ^ delta * ((n : ℝ) + 1) ^ (-(1 + eps)) :=
  ⟨separationTotal_eq delta, fun m n => separationBulk_nonneg m n,
    fun _ _ h => separationTotal_stabilizes h,
    fun e m => summable_separationDefect delta e m,
    tendsto_separationDefect delta,
    not_summable_separation_cofinal heps⟩

end

end RHTower
