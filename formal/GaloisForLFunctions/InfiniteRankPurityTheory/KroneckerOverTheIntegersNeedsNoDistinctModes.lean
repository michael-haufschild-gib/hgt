import GaloisForLFunctions.InfiniteRankPurityTheory.TheArchimedeanFibreIsATraceAndTheFiniteContactsAreNot
import GaloisForLFunctions.InfiniteRankPurityTheory.NoTraceClassFamilyOfZerosIsIntegral

/-!
# Kronecker over the integers needs no distinct modes

Kronecker's theorem for Frobenius modules over `ℤ` and the growth form of the weight filtration, in
their final generality: trace class at any Frobenius, modes repeated at will. The statements are
about the merged weight `Σ_{ρ_i = w} b_i` carried at a mode `w`.

* `mergedWeight_eq_zero_of_integral_trace`, `exists_nat_of_mergedWeight_ne_zero`: a module of trace
  class of order `m` at a Frobenius `q`, with weights below `m` without ascending chain and integer
  traces at all large integers, carries weight only at the modes `0, 1, …, m − 1`. The trace is
  eventually a polynomial `P`; the Tate module with weights the coefficients of `P` has the same
  trace; traces determine the merged weights.
* `mergedWeight_dual_of_integral_trace`: if moreover the visible modes are closed under
  `w ↦ 1 − w`, only `0` and `1` are visible.
* `frobTrace_bound_iff_mergedWeight_at`: for a module of trace class at `q` with weights without
  ascending chain, `t(n) = O(n^s)` at the integers exactly when no weight is carried at a mode of
  weight `> s`.
-/

open Filter Topology Finset

namespace GaloisForLFunctions.InfiniteRankPurityTheory

variable {ι : Type*}

/-- Trace class of order `m` at `q` is trace class of order zero at `q`. -/
theorem TraceClassAt.zero {q m : ℕ} {b ρ : ι → ℂ} (hb : TraceClassAt q m b ρ) :
    TraceClassAt q 0 b ρ := by
  have h : Summable fun i => ‖b i‖ * (q : ℝ) ^ (ρ i).re * (1 + ‖ρ i‖) ^ m := hb
  have h0 : ∀ i, 0 ≤ ‖b i‖ * (q : ℝ) ^ (ρ i).re := fun i =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) h
  · exact mul_nonneg (h0 i) (pow_nonneg (by linarith [norm_nonneg (ρ i)]) _)
  · rw [pow_zero, mul_one]
    exact le_mul_of_one_le_right (h0 i) (one_le_one_add_norm_pow _ _)

/-! ### Kronecker -/

theorem sum_range_coeff_eq_eval (P : Polynomial ℂ) {m : ℕ} (hP : ∀ i, m ≤ i → P.coeff i = 0)
    (x : ℂ) : ∑ k ∈ range m, P.coeff k * x ^ k = P.eval x := by
  have hA : ∑ k ∈ range m, P.coeff k * x ^ k =
      ∑ k ∈ range (max m (P.natDegree + 1)), P.coeff k * x ^ k := by
    refine Finset.sum_subset (Finset.range_subset_range.mpr (le_max_left _ _)) fun k _ hk => ?_
    rw [hP k (not_lt.mp (Finset.mem_range.not.mp hk)), zero_mul]
  have hB : ∑ k ∈ range (P.natDegree + 1), P.coeff k * x ^ k =
      ∑ k ∈ range (max m (P.natDegree + 1)), P.coeff k * x ^ k := by
    refine Finset.sum_subset (Finset.range_subset_range.mpr (le_max_right _ _)) fun k _ hk => ?_
    have hlt : P.natDegree < k := by
      have := Finset.mem_range.not.mp hk
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, zero_mul]
  rw [Polynomial.eval_eq_sum_range, hA, hB]

/-- The Tate module with weights the coefficients of `P` has the trace `P`. -/
theorem frobTrace_tate (P : Polynomial ℂ) {m : ℕ} (hP : ∀ i, m ≤ i → P.coeff i = 0) (n : ℕ) :
    frobTrace (fun k : Fin m => P.coeff k) (fun k : Fin m => ((k : ℕ) : ℂ)) n =
      P.eval (n : ℂ) := by
  rw [frobTrace, tsum_fintype, ← sum_range_coeff_eq_eval P hP,
    ← Fin.sum_univ_eq_sum_range (fun k => P.coeff k * (n : ℂ) ^ k) m]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.cpow_natCast, Complex.ofReal_natCast]

/-- **Kronecker over `ℤ` without distinct modes.** A module of trace class of order `m` at `q`,
with weights below `m` without ascending chain and integer traces at all large integers, carries no
weight at a mode other than `0, 1, …, m − 1`. -/
theorem mergedWeight_eq_zero_of_integral_trace {b ρ : ι → ℂ} {A : ℝ} {m q : ℕ} (hq : 1 ≤ q)
    (hwf : WeightsWellFounded ρ) (hA : ∀ i, (ρ i).re ≤ A) (hAm : A < m)
    (hb : TraceClassAt q m b ρ) {n₁ : ℕ}
    (hint : ∀ n : ℕ, n₁ ≤ n → ∃ k : ℤ, frobTrace b ρ n = k) {w : ℂ}
    (hw : ∀ k : ℕ, k < m → w ≠ k) : mergedWeight b ρ w = 0 := by
  obtain ⟨n₀, P, hP, hval⟩ := exists_polynomial_of_integral_trace_at hq hA hAm hb hint
  have hc : TraceClassAt q 0 (fun k : Fin m => P.coeff k) (fun k : Fin m => ((k : ℕ) : ℂ)) :=
    (hasSum_fintype _).summable
  have heq := mergedWeight_eq_of_frobTrace_eventually_eq hq hb.zero hc hwf
    (weightsWellFounded_of_finite _) (n₀ := n₀)
    (fun n hn => by rw [hval n hn, frobTrace_tate P hP]) w
  rw [heq, mergedWeight]
  refine (tsum_congr fun k => ?_).trans tsum_zero
  rw [if_neg fun h => hw k k.2 h.symm]

/-- The visible modes of an integral module are natural numbers below its order. -/
theorem exists_nat_of_mergedWeight_ne_zero {b ρ : ι → ℂ} {A : ℝ} {m q : ℕ} (hq : 1 ≤ q)
    (hwf : WeightsWellFounded ρ) (hA : ∀ i, (ρ i).re ≤ A) (hAm : A < m)
    (hb : TraceClassAt q m b ρ) {n₁ : ℕ}
    (hint : ∀ n : ℕ, n₁ ≤ n → ∃ k : ℤ, frobTrace b ρ n = k) {w : ℂ}
    (hw : mergedWeight b ρ w ≠ 0) : ∃ k : ℕ, k < m ∧ w = k := by
  by_contra hcon
  exact hw (mergedWeight_eq_zero_of_integral_trace hq hwf hA hAm hb hint
    fun k hk hwk => hcon ⟨k, hk, hwk⟩)

/-- **Kronecker with the duality, without distinct modes.** If the visible modes are closed under
`w ↦ 1 − w`, only `0` and `1` are visible. -/
theorem mergedWeight_dual_of_integral_trace {b ρ : ι → ℂ} {A : ℝ} {m q : ℕ} (hq : 1 ≤ q)
    (hwf : WeightsWellFounded ρ) (hA : ∀ i, (ρ i).re ≤ A) (hAm : A < m)
    (hb : TraceClassAt q m b ρ) {n₁ : ℕ}
    (hint : ∀ n : ℕ, n₁ ≤ n → ∃ k : ℤ, frobTrace b ρ n = k)
    (hdual : ∀ w : ℂ, mergedWeight b ρ w ≠ 0 → mergedWeight b ρ (1 - w) ≠ 0) {w : ℂ}
    (hw : mergedWeight b ρ w ≠ 0) : w = 0 ∨ w = 1 := by
  obtain ⟨k, -, hk⟩ := exists_nat_of_mergedWeight_ne_zero hq hwf hA hAm hb hint hw
  obtain ⟨l, -, hl⟩ := exists_nat_of_mergedWeight_ne_zero hq hwf hA hAm hb hint (hdual w hw)
  have hkl : l + k = 1 := by
    have : ((l + k : ℕ) : ℂ) = 1 := by
      push_cast
      rw [← hl, hk]
      ring
    exact_mod_cast this
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · left
    rw [hk, h0]
    simp
  · right
    have : k = 1 := by omega
    rw [hk, this]
    simp

/-! ### Growth -/

/-- With summable weights and visible weights `≤ s`, the trace is at most `(Σ‖c_i‖) x^s` for
`x ≥ 1`. -/
theorem norm_frobTrace_le_of_re_le {c ρ : ι → ℂ} (hc : Summable fun i => ‖c i‖) {s : ℝ}
    (hle : ∀ i, c i ≠ 0 → (ρ i).re ≤ s) {x : ℝ} (hx : 1 ≤ x) :
    ‖frobTrace c ρ x‖ ≤ (∑' i, ‖c i‖) * x ^ s := by
  rw [frobTrace, ← tsum_mul_right]
  refine tsum_of_norm_bounded (hc.mul_right _).hasSum fun i => ?_
  by_cases hci : c i = 0
  · simp [hci]
  · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (hle i hci))
      (norm_nonneg _)

/-- **The weight filtration is the growth filtration at any Frobenius.** For a module of trace
class at `q` with weights without ascending chain: the trace is `O(n^s)` at the integers exactly
when no weight is carried at a mode `w` with `Re w > s`. -/
theorem frobTrace_bound_iff_mergedWeight_at {c ρ : ι → ℂ} {q : ℕ} (hq : 1 ≤ q)
    (hc : TraceClassAt q 0 c ρ) (hwf : WeightsWellFounded ρ) (s : ℝ) :
    (∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ‖frobTrace c ρ n‖ ≤ C * (n : ℝ) ^ s) ↔
      ∀ w : ℂ, s < w.re → mergedWeight c ρ w = 0 := by
  constructor
  · rintro ⟨C, n₀, h⟩ w hw
    exact mergedWeight_eq_zero_of_frobTrace_bound_at hq hc hwf h hw
  · intro hzero
    obtain ⟨A, hA⟩ := hwf.exists_le
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    have hc' : Summable fun i => ‖c i * (q : ℂ) ^ ρ i‖ := by simpa using hc.dilated hq
    -- the merged weights of the dilated module vanish above `s`
    have hvis : ∀ k : Set.range ρ,
        mergedWeight (fun i => c i * (q : ℂ) ^ ρ i) ρ k ≠ 0 → ((k : ℂ)).re ≤ s := by
      intro k hk
      by_contra hlt
      apply hk
      rw [mergedWeight_dilate, hzero k (not_le.mp hlt), zero_mul]
    refine ⟨(∑' k : Set.range ρ, ‖mergedWeight (fun i => c i * (q : ℂ) ^ ρ i) ρ k‖) *
      ((q : ℝ) ^ s)⁻¹, q, fun n hn => ?_⟩
    have hx : (1 : ℝ) ≤ (n : ℝ) / q := (one_le_div hq0).mpr (by exact_mod_cast hn)
    have hn0 : (0 : ℝ) ≤ (n : ℝ) / q := le_trans zero_le_one hx
    have htr : frobTrace c ρ n =
        frobTrace (fun k : Set.range ρ => mergedWeight (fun i => c i * (q : ℂ) ^ ρ i) ρ k)
          (fun k : Set.range ρ => (k : ℂ)) ((n : ℝ) / q) := by
      rw [frobTrace_merged hc' hA hx, ← frobTrace_dilate c ρ q hn0, mul_div_cancel₀ _ hq0.ne']
    rw [htr]
    refine (norm_frobTrace_le_of_re_le (summable_norm_mergedWeight hc') hvis hx).trans
      (le_of_eq ?_)
    rw [Real.div_rpow (Nat.cast_nonneg n) hq0.le, div_eq_mul_inv]
    ring

end GaloisForLFunctions.InfiniteRankPurityTheory
