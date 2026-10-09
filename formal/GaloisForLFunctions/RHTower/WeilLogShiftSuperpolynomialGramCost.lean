import GaloisForLFunctions.RHTower.WeilLogShiftAllOrderClusterCost

/-!
# Full-cutoff Gram certificate cost exceeds every fixed polynomial

The cost normalization is fixed before the polynomial degree. Constants from
different cancellation orders are reconciled by exact linear scaling of cost.
-/

open scoped BigOperators

namespace RHTower

theorem finiteWeilGramTailCost_scale (a B : ℝ) (w : FiniteWeilGramTest) :
    finiteWeilGramTailCost (a * B) w = a * finiteWeilGramTailCost B w := by
  rcases w with ⟨N, x, u, b⟩
  dsimp [finiteWeilGramTailCost]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Under every fixed positive cost normalization, every normalized certificate
on the full cutoff eventually costs more than every fixed polynomial in that
cutoff. Existence of finite certificates is already unconditional in the corpus. -/
theorem finiteWeilGram_cutoff_cost_superpolynomial (B₀ : ℝ) (hB₀ : 0 < B₀)
    (p : ℕ) (A : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ tests : Finset FiniteWeilGramTest,
      FiniteWeilGramNormCertificate (Finset.range n) tests →
      A * (n : ℝ) ^ p < ∑ w ∈ tests, finiteWeilGramTailCost B₀ w := by
  obtain ⟨B, hB, hbound⟩ := exists_finiteWeilGram_allOrder_cluster_cost_bound p
  let C : ℝ := B₀ / B
  have hC : 0 < C := div_pos hB₀ hB
  have hscale (w : FiniteWeilGramTest) :
      finiteWeilGramTailCost B₀ w = C * finiteWeilGramTailCost B w := by
    have heq : B₀ = C * B := by dsimp [C]; field_simp
    calc
      finiteWeilGramTailCost B₀ w = finiteWeilGramTailCost (C * B) w := by rw [← heq]
      _ = C * finiteWeilGramTailCost B w := finiteWeilGramTailCost_scale C B w
  obtain ⟨M, hM⟩ := exists_nat_gt (|A| * (2 : ℝ) ^ p / C)
  refine ⟨max M (p + 2) + (p + 2), ?_⟩
  intro n hn tests hcert
  let k : ℕ := n - (p + 2)
  have hkM : M ≤ k := by dsimp [k]; omega
  have hkp : p + 2 ≤ k := by dsimp [k]; omega
  have hnk : n = k + p + 2 := by dsimp [k]; omega
  have hlower : 2 * (((k + 2 : ℕ) : ℝ) ^ (p + 3)) <
      ∑ w ∈ tests, finiteWeilGramTailCost B w := by
    apply hbound _ tests hcert k (by omega)
    intro i
    apply Finset.mem_range.mpr
    have := i.isLt
    omega
  let x : ℝ := (k + 2 : ℕ)
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ k + 2 by omega)
  have hx : 0 < x := by linarith
  have hMx : (M : ℝ) ≤ x := by dsimp [x]; exact_mod_cast (show M ≤ k + 2 by omega)
  have hnx : (n : ℝ) ≤ 2 * x := by
    dsimp [x]
    exact_mod_cast (show n ≤ 2 * (k + 2) by omega)
  have hcoeff : |A| * (2 : ℝ) ^ p ≤ C * x := by
    have hmc := (div_lt_iff₀ hC).mp hM
    nlinarith
  have hcube : x ≤ x ^ 3 := by
    nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hx1),
      mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx1)]
  calc
    A * (n : ℝ) ^ p ≤ |A| * (n : ℝ) ^ p :=
      mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
    _ ≤ |A| * (2 * x) ^ p := by gcongr
    _ = (|A| * (2 : ℝ) ^ p) * x ^ p := by rw [mul_pow]; ring
    _ ≤ (C * x) * x ^ p := mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ ≤ (2 * C * x ^ 3) * x ^ p := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
    _ = C * (2 * x ^ (p + 3)) := by rw [pow_add]; ring
    _ < C * ∑ w ∈ tests, finiteWeilGramTailCost B w := mul_lt_mul_of_pos_left hlower hC
    _ = ∑ w ∈ tests, finiteWeilGramTailCost B₀ w := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      exact (hscale w).symm

end RHTower
