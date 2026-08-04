import GaloisForLFunctions.HTGeometry.PolynomialGrowthBound

/-!
# A transcendental entire function satisfies no order-zero equation

An order-zero algebraic differential equation is a polynomial relation `P(z, g z) = 0`.  Reading it
as a polynomial in the second variable and applying the algebraic root estimate bounds `g` by the
normalised lower coefficients; beyond the leading coefficient's growth radius those quotients are
polynomially bounded, and on the remaining compact disc `g` is bounded by continuity.  Liouville at
polynomial growth then makes `g` a polynomial.

This is the order-zero case of the cascade order theorem: the differential order of a transcendental
entire function is at least one.
-/

open Metric

namespace GaloisForLFunctions.HTGeometry

/-! ## Reduction to a nonvanishing top coefficient

The coefficient form produced by the two-variable decomposition only knows that *some* coefficient is
nonzero.  Truncating at the largest such index makes the top coefficient nonzero, which is what the
root estimate needs. -/

/-- **Truncation at the top nonzero coefficient.** -/
theorem exists_top_relation {g : ℂ → ℂ} {d : ℕ} {a : ℕ → Polynomial ℂ}
    (hne : ∃ k, k ≤ d ∧ a k ≠ 0)
    (hrel : ∀ z : ℂ, ∑ k ∈ Finset.range (d + 1), (a k).eval z * (g z) ^ k = 0) :
    ∃ D : ℕ, a D ≠ 0 ∧
      ∀ z : ℂ, ∑ k ∈ Finset.range (D + 1), (a k).eval z * (g z) ^ k = 0 := by
  classical
  set S : Finset ℕ := (Finset.range (d + 1)).filter (fun k => a k ≠ 0) with hS
  have hSne : S.Nonempty := by
    obtain ⟨k, hk, hak⟩ := hne
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hak⟩⟩
  set D : ℕ := S.max' hSne with hD
  have hDmem : D ∈ S := S.max'_mem hSne
  have hDne : a D ≠ 0 := (Finset.mem_filter.mp hDmem).2
  have hDle : D ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hDmem).1)
  refine ⟨D, hDne, ?_⟩
  intro z
  have hsub : Finset.range (D + 1) ⊆ Finset.range (d + 1) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hzero : ∀ k ∈ Finset.range (d + 1), k ∉ Finset.range (D + 1) →
      (a k).eval z * (g z) ^ k = 0 := by
    intro k hk hknot
    have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hkD : D < k := by
      have h := hknot
      rw [Finset.mem_range] at h
      omega
    have hak : a k = 0 := by
      by_contra hcon
      have hmem : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hcon⟩
      have hle : k ≤ D := by
        rw [hD]
        exact Finset.le_max' S k hmem
      omega
    rw [hak, Polynomial.eval_zero, zero_mul]
  rw [Finset.sum_subset hsub hzero]
  exact hrel z

/-! ## Polynomial growth from an order-zero relation -/

/-- **Polynomial growth beyond the growth radius.**  A solution of a polynomial relation whose top
coefficient is a nonzero polynomial is polynomially bounded outside an explicit disc. -/
theorem norm_le_of_top_relation {g : ℂ → ℂ} {D : ℕ} {a : ℕ → Polynomial ℂ}
    (hD1 : 1 ≤ D) (hDne : a D ≠ 0)
    (hrelD : ∀ z : ℂ, ∑ k ∈ Finset.range (D + 1), (a k).eval z * (g z) ^ k = 0)
    {z : ℂ} (hz : growthRadius (a D) ≤ ‖z‖) :
    ‖g z‖
      ≤ (1 + ∑ k ∈ Finset.range D, 2 * coeffNormSum (a k) / ‖(a D).leadingCoeff‖)
          * (1 + ‖z‖) ^ ((Finset.range D).sup fun k => (a k).natDegree) := by
  classical
  set N : ℕ := (Finset.range D).sup (fun k => (a k).natDegree) with hN
  set C : ℝ := ∑ k ∈ Finset.range D, 2 * coeffNormSum (a k) / ‖(a D).leadingCoeff‖ with hC
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hz1 : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith
  have hpow1 : (1 : ℝ) ≤ (1 + ‖z‖) ^ N := one_le_pow₀ hz1
  have hC0 : 0 ≤ C := by
    rw [hC]
    refine Finset.sum_nonneg ?_
    intro k _
    exact div_nonneg (by linarith [coeffNormSum_nonneg (a k)]) (norm_nonneg _)
  have hane : (a D).eval z ≠ 0 := eval_ne_zero_of_growthRadius_le hDne hz
  have hbase := norm_le_max_sum_of_root hD1 hane (hrelD z)
  have hsum : ∑ i ∈ Finset.range D, ‖(a i).eval z / (a D).eval z‖ ≤ C * (1 + ‖z‖) ^ N := by
    rw [hC, Finset.sum_mul]
    refine Finset.sum_le_sum ?_
    intro k hk
    refine le_trans (norm_div_le_of_growthRadius_le hDne hz) ?_
    refine mul_le_mul_of_nonneg_left ?_
      (div_nonneg (by linarith [coeffNormSum_nonneg (a k)]) (norm_nonneg _))
    exact pow_le_pow_right₀ hz1 (Finset.le_sup (f := fun k => (a k).natDegree) hk)
  refine le_trans hbase (max_le ?_ ?_)
  · have hstep : (1 : ℝ) * 1 ≤ (1 + C) * (1 + ‖z‖) ^ N :=
      mul_le_mul (by linarith) hpow1 (by norm_num) (by linarith)
    linarith
  · have hstep : C * (1 + ‖z‖) ^ N ≤ (1 + C) * (1 + ‖z‖) ^ N :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith

/-! ## The order-zero case of the cascade theorem -/

/-- **A transcendental entire function is not algebraic.**  No order-zero algebraic differential
equation is satisfied by an entire function that is not a polynomial. -/
theorem not_differentiallyAlgebraicOfOrder_zero_of_transcendental
    {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z) :
    ¬ GaloisForLFunctions.DifferentiallyAlgebraicOfOrder g 0 := by
  classical
  intro hDA
  obtain ⟨d, a, hne, hrel⟩ := exists_nonzero_coeff_relation_of_order_zero hDA
  obtain ⟨D, hDne, hrelD⟩ := exists_top_relation hne hrel
  rcases Nat.eq_zero_or_pos D with hD0 | hD1
  · -- a constant relation forces its only coefficient to vanish identically
    refine hDne (Polynomial.funext (fun z => ?_))
    have h := hrelD z
    rw [hD0] at h ⊢
    simp only [zero_add, Finset.sum_range_one, pow_zero, mul_one] at h
    rw [Polynomial.eval_zero]
    exact h
  · set N : ℕ := (Finset.range D).sup (fun k => (a k).natDegree) with hN
    set C : ℝ := ∑ k ∈ Finset.range D, 2 * coeffNormSum (a k) / ‖(a D).leadingCoeff‖ with hC
    have hC0 : 0 ≤ C := by
      rw [hC]
      refine Finset.sum_nonneg ?_
      intro k _
      exact div_nonneg (by linarith [coeffNormSum_nonneg (a k)]) (norm_nonneg _)
    set R : ℝ := growthRadius (a D) with hR
    have hR0 : 0 ≤ R := growthRadius_nonneg _
    obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
      hg.continuous.continuousOn
    have hM0 : 0 ≤ M₀ := by
      have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) R := by
        simpa using hR0
      exact le_trans (norm_nonneg _) (hM₀ 0 h0)
    have hglobal : ∀ z : ℂ, ‖g z‖ ≤ (M₀ + 1 + C) * (1 + ‖z‖) ^ N := by
      intro z
      have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
      have hpow1 : (1 : ℝ) ≤ (1 + ‖z‖) ^ N := one_le_pow₀ (by linarith)
      rcases le_or_gt ‖z‖ R with hz | hz
      · have h1 := hM₀ z (mem_closedBall_zero_iff.mpr hz)
        have hK : (0 : ℝ) ≤ M₀ + 1 + C := by linarith
        have hstep : (M₀ + 1 + C) * 1 ≤ (M₀ + 1 + C) * (1 + ‖z‖) ^ N :=
          mul_le_mul_of_nonneg_left hpow1 hK
        linarith
      · have h1 := norm_le_of_top_relation hD1 hDne hrelD (le_of_lt hz)
        rw [← hN, ← hC] at h1
        have hstep : (1 + C) * (1 + ‖z‖) ^ N ≤ (M₀ + 1 + C) * (1 + ‖z‖) ^ N :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        linarith
    exact hnp (exists_polynomial_of_polynomial_growth hg hglobal)

end GaloisForLFunctions.HTGeometry
