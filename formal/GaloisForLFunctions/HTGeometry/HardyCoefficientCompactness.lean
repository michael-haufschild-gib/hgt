import GaloisForLFunctions.HTGeometry.HardyTaylorCoefficient

/-!
# Compactness for uniformly bounded Hardy coefficient factors

This module packages the countable diagonal compactness argument needed to pass from finite
Hardy factorizations to square-summable limiting coefficient sequences.  A single subsequence
works simultaneously for both factors, and finite-partial-sum bounds preserve the exact `ℓ²`
budget in the limit.
-/

open MeasureTheory Complex Filter Topology Set Polynomial PowerSeries Finset
open scoped Real ENNReal NNReal Nat ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem norm_le_add_one_of_sq_le {C : ℝ} (hC : 0 ≤ C) {z : ℂ}
    (hz : ‖z‖ ^ 2 ≤ C) : ‖z‖ ≤ C + 1 := by
  by_cases h : ‖z‖ ≤ 1
  · linarith
  · have h1 : 1 ≤ ‖z‖ := le_of_not_ge h
    have hs : ‖z‖ ≤ ‖z‖ ^ 2 := by nlinarith
    linarith

/-- Two arrays with a common uniform square-sum bound admit a common pointwise-convergent
subsequence.  Both limiting arrays are square-summable with the original bound. -/
theorem exists_common_subseq_tendsto_of_memℓp_two_of_tsum_le
    {C : ℝ} (hC : 0 ≤ C) (a b : ℕ → ℕ → ℂ)
    (ha : ∀ N, Memℓp (a N) 2) (hb : ∀ N, Memℓp (b N) 2)
    (haBound : ∀ N, (∑' k, ‖a N k‖ ^ 2) ≤ C)
    (hbBound : ∀ N, (∑' k, ‖b N k‖ ^ 2) ≤ C) :
    ∃ A B : ℕ → ℂ, ∃ subseq : ℕ → ℕ,
      StrictMono subseq ∧
      (∀ k, Tendsto (fun j => a (subseq j) k) atTop (nhds (A k))) ∧
      (∀ k, Tendsto (fun j => b (subseq j) k) atTop (nhds (B k))) ∧
      Memℓp A 2 ∧ Memℓp B 2 ∧
      (∑' k, ‖A k‖ ^ 2) ≤ C ∧ (∑' k, ‖B k‖ ^ 2) ≤ C := by
  let R : ℝ := C + 1
  have hpointA : ∀ N k, ‖a N k‖ ≤ R := by
    intro N k
    have hterm : ‖a N k‖ ^ 2 ≤ ∑' j, ‖a N j‖ ^ 2 := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (ha N).summable (by norm_num) |>.le_tsum k (fun _ _ => by positivity)
    exact norm_le_add_one_of_sq_le hC (hterm.trans (haBound N))
  have hpointB : ∀ N k, ‖b N k‖ ≤ R := by
    intro N k
    have hterm : ‖b N k‖ ^ 2 ≤ ∑' j, ‖b N j‖ ^ 2 := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (hb N).summable (by norm_num) |>.le_tsum k (fun _ _ => by positivity)
    exact norm_le_add_one_of_sq_le hC (hterm.trans (hbBound N))
  let x : ℕ → ((ℕ → Metric.closedBall (0 : ℂ) R) ×
      (ℕ → Metric.closedBall (0 : ℂ) R)) := fun N =>
    ⟨fun k => ⟨a N k, by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact hpointA N k⟩,
      fun k => ⟨b N k, by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact hpointB N k⟩⟩
  obtain ⟨L, subseq, hsubseq, hL⟩ := CompactSpace.tendsto_subseq x
  let A : ℕ → ℂ := fun k => (L.1 k : ℂ)
  let B : ℕ → ℂ := fun k => (L.2 k : ℂ)
  have hLA : Tendsto (fun j => (x (subseq j)).1) atTop (nhds L.1) := by
    exact (continuous_fst.tendsto L).comp hL
  have hLB : Tendsto (fun j => (x (subseq j)).2) atTop (nhds L.2) := by
    exact (continuous_snd.tendsto L).comp hL
  have hAlim : ∀ k, Tendsto (fun j => a (subseq j) k) atTop (nhds (A k)) := by
    intro k
    have hk := tendsto_pi_nhds.mp hLA k
    have hcoe := (continuous_subtype_val.tendsto (L.1 k)).comp hk
    simpa only [x, A] using! hcoe
  have hBlim : ∀ k, Tendsto (fun j => b (subseq j) k) atTop (nhds (B k)) := by
    intro k
    have hk := tendsto_pi_nhds.mp hLB k
    have hcoe := (continuous_subtype_val.tendsto (L.2 k)).comp hk
    simpa only [x, B] using! hcoe
  have hApartial : ∀ M, ∑ k ∈ Finset.range M, ‖A k‖ ^ 2 ≤ C := by
    intro M
    have hlimSum : Tendsto (fun j => ∑ k ∈ Finset.range M, ‖a (subseq j) k‖ ^ 2)
        atTop (nhds (∑ k ∈ Finset.range M, ‖A k‖ ^ 2)) := by
      apply tendsto_finsetSum
      intro k hk
      exact (hAlim k).norm.pow 2
    apply le_of_tendsto hlimSum
    filter_upwards with j
    have hsum : ∑ k ∈ Finset.range M, ‖a (subseq j) k‖ ^ 2 ≤
        ∑' k, ‖a (subseq j) k‖ ^ 2 := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        ((ha (subseq j)).summable (by norm_num)).sum_le_tsum (Finset.range M)
          (fun _ _ => by positivity)
    exact hsum.trans (haBound (subseq j))
  have hBpartial : ∀ M, ∑ k ∈ Finset.range M, ‖B k‖ ^ 2 ≤ C := by
    intro M
    have hlimSum : Tendsto (fun j => ∑ k ∈ Finset.range M, ‖b (subseq j) k‖ ^ 2)
        atTop (nhds (∑ k ∈ Finset.range M, ‖B k‖ ^ 2)) := by
      apply tendsto_finsetSum
      intro k hk
      exact (hBlim k).norm.pow 2
    apply le_of_tendsto hlimSum
    filter_upwards with j
    have hsum : ∑ k ∈ Finset.range M, ‖b (subseq j) k‖ ^ 2 ≤
        ∑' k, ‖b (subseq j) k‖ ^ 2 := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        ((hb (subseq j)).summable (by norm_num)).sum_le_tsum (Finset.range M)
          (fun _ _ => by positivity)
    exact hsum.trans (hbBound (subseq j))
  have hAsum : Summable (fun k => ‖A k‖ ^ 2) :=
    summable_of_sum_range_le (fun k => by positivity) hApartial
  have hBsum : Summable (fun k => ‖B k‖ ^ 2) :=
    summable_of_sum_range_le (fun k => by positivity) hBpartial
  have hAmem : Memℓp A 2 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hAsum
  have hBmem : Memℓp B 2 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hBsum
  exact ⟨A, B, subseq, hsubseq, hAlim, hBlim, hAmem, hBmem,
    Real.tsum_le_of_sum_range_le (fun k => by positivity) hApartial,
    Real.tsum_le_of_sum_range_le (fun k => by positivity) hBpartial⟩

/-- A sequence of analytic polynomials with a uniform boundary `L¹` bound has, after a common
subsequence, an exact coefficientwise convolution factorization by two bounded `ℓ²` sequences. -/
theorem exists_polynomial_hardy_coefficient_limit_factorization
    (p : ℕ → ℂ[X]) {C : ℝ} (hC : 0 ≤ C)
    (hpBound : ∀ N, polynomialBoundaryL1 (p N) ≤ C) :
    ∃ A B : ℕ → ℂ, ∃ subseq : ℕ → ℕ,
      StrictMono subseq ∧ Memℓp A 2 ∧ Memℓp B 2 ∧
      (∑' k, ‖A k‖ ^ 2) ≤ C ∧ (∑' k, ‖B k‖ ^ 2) ≤ C ∧
      ∀ n, Tendsto (fun j => (p (subseq j)).coeff n) atTop
        (nhds (∑ i ∈ Finset.range (n + 1), A i * B (n - i))) := by
  have hex : ∀ N, ∃ a b : ℕ → ℂ,
      Memℓp a 2 ∧ Memℓp b 2 ∧
      (∑' k, ‖a k‖ ^ 2) ≤ C ∧ (∑' k, ‖b k‖ ^ 2) ≤ C ∧
      ∀ n, (p N).coeff n = ∑ i ∈ Finset.range (n + 1), a i * b (n - i) := by
    intro N
    obtain ⟨g, h, hg, hh, hprod, hga, hha, hgbound, hhbound, hconv⟩ :=
      exists_polynomial_hardy_coefficients_with_convolution_all (p N)
    exact ⟨fun k => (cauchyPowerSeries g 0 (1 / 2 : NNReal)).coeff k,
      fun k => (cauchyPowerSeries h 0 (1 / 2 : NNReal)).coeff k,
      hga, hha, hgbound.trans (hpBound N), hhbound.trans (hpBound N), hconv⟩
  choose a b hab using hex
  obtain ⟨A, B, subseq, hsubseq, hAlim, hBlim, hAmem, hBmem, hAbound, hBbound⟩ :=
    exists_common_subseq_tendsto_of_memℓp_two_of_tsum_le hC a b
      (fun N => (hab N).1) (fun N => (hab N).2.1)
      (fun N => (hab N).2.2.1) (fun N => (hab N).2.2.2.1)
  refine ⟨A, B, subseq, hsubseq, hAmem, hBmem, hAbound, hBbound, ?_⟩
  intro n
  have hsum : Tendsto
      (fun j => ∑ i ∈ Finset.range (n + 1), a (subseq j) i * b (subseq j) (n - i))
      atTop (nhds (∑ i ∈ Finset.range (n + 1), A i * B (n - i))) := by
    apply tendsto_finsetSum
    intro i hi
    exact (hAlim i).mul (hBlim (n - i))
  refine Tendsto.congr' ?_ hsum
  filter_upwards with j
  exact (hab (subseq j)).2.2.2.2 n |>.symm

end

end GaloisForLFunctions.HTGeometry
