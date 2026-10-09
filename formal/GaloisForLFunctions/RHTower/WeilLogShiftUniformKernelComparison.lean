import GaloisForLFunctions.RHTower.WeilLogShiftFactorialMajorant

/-!
# Uniform exponential comparison across the entire real shift line

A global autocorrelation upper bound and one positive exponential lower
envelope at a source shift give a comparison uniform in every target shift.
The finite head is included. Consequently changing shift preserves each
fixed factorial-order class, even for arbitrary signed coefficient sequences.
-/

open Filter Topology Real Zeta23

noncomputable section

namespace RHTower

open WeilExcess

/-- The paired kernel is bounded uniformly in both shift and index. -/
theorem pairedLogKernel_le_two_mul_riemannAutocorr_zero (y : ℝ) (n : ℕ) :
    pairedLogKernel y n ≤ 2 * riemannAutocorr 0 := by
  unfold pairedLogKernel
  linarith only [riemannAutocorr_le_zero (y + log n),
    riemannAutocorr_le_zero (y - log n)]

/-- A single exponential loss at any source shift controls every target
shift, with constants uniform over the whole real line and all indices. -/
theorem exists_pairedLogKernel_uniform_exponential_comparison (c : ℝ) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∀ (y : ℝ) (n : ℕ),
      pairedLogKernel y n ≤ C * exp (B * n) * pairedLogKernel c n := by
  let B := logKernelCriticalRate c + 1
  have hB : 0 < B := by dsimp only [B]; linarith only [logKernelCriticalRate_pos c]
  obtain ⟨D, hD, htail⟩ := exists_paired_logKernel_lower_of_rate_lt
    (y := c) (b := B) (by dsimp only [B]; linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  let q : ℕ → ℝ := fun n => exp (-(B * n)) / pairedLogKernel c n
  let V := 1 / D + ∑ j ∈ Finset.range N, q j
  have hq (n : ℕ) : 0 ≤ q n :=
    div_nonneg (exp_pos _).le (pairedLogKernel_pos c n).le
  have hsum : 0 ≤ ∑ j ∈ Finset.range N, q j := Finset.sum_nonneg (fun j _ => hq j)
  have hV : 0 < V := by dsimp only [V]; positivity
  have hqV (n : ℕ) : q n ≤ V := by
    by_cases hn : n < N
    · have ht : q n ≤ ∑ j ∈ Finset.range N, q j :=
        Finset.single_le_sum (f := q) (fun j _ => hq j) (Finset.mem_range.mpr hn)
      dsimp only [V]
      have hD' : 0 < 1 / D := by positivity
      linarith only [ht, hD']
    · have ht : q n ≤ 1 / D := by
        apply (div_le_div_iff₀ (pairedLogKernel_pos c n) hD).mpr
        simpa only [one_mul, mul_comm, pairedLogKernel] using hN n (by omega)
      dsimp only [V]
      linarith only [ht, hsum]
  let U := 2 * riemannAutocorr 0
  have hU : 0 < U := mul_pos (by norm_num) (riemannAutocorr_pos 0)
  refine ⟨B, U * V, hB, mul_pos hU hV, fun y n => ?_⟩
  have he : exp (-(B * n)) ≤ V * pairedLogKernel c n :=
    (div_le_iff₀ (pairedLogKernel_pos c n)).mp (hqV n)
  have hscale := mul_le_mul_of_nonneg_left he (exp_pos (B * n)).le
  rw [← exp_add, add_neg_cancel, exp_zero] at hscale
  calc
    pairedLogKernel y n ≤ U := pairedLogKernel_le_two_mul_riemannAutocorr_zero y n
    _ ≤ U * (exp (B * n) * (V * pairedLogKernel c n)) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hscale hU.le
    _ = _ := by ring

/-- The same comparison constants apply to every signed coefficient sequence. -/
theorem exists_kernelPotential_uniform_exponential_comparison (c : ℝ) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∀ (v : ℕ → ℝ) (y : ℝ) (n : ℕ),
      |v n * pairedLogKernel y n| ≤
        C * exp (B * n) * |v n * pairedLogKernel c n| := by
  obtain ⟨B, C, hB, hC, hbound⟩ := exists_pairedLogKernel_uniform_exponential_comparison c
  refine ⟨B, C, hB, hC, fun v y n => ?_⟩
  simp only [abs_mul, abs_of_pos (pairedLogKernel_pos y n),
    abs_of_pos (pairedLogKernel_pos c n)]
  calc
    _ ≤ |v n| * (C * exp (B * n) * pairedLogKernel c n) :=
      mul_le_mul_of_nonneg_left (hbound y n) (abs_nonneg (v n))
    _ = _ := by ring

/-- A bound of fixed factorial order at one shift transfers to every real
shift simultaneously, without changing its factorial order or cutoff. -/
theorem exists_kernelPotential_uniform_factorial_envelope
    (v : ℕ → ℝ) (c : ℝ) (m : ℕ) (A D : ℝ) (N : ℕ)
    (hc : ∀ n : ℕ, N ≤ n →
      |v n * pairedLogKernel c n| ≤ D * exp (A * n) * (n.factorial : ℝ) ^ m) :
    ∃ B C : ℝ, 0 ≤ C ∧ ∀ (y : ℝ) (n : ℕ), N ≤ n →
      |v n * pairedLogKernel y n| ≤ C * exp (B * n) * (n.factorial : ℝ) ^ m := by
  obtain ⟨b, K, _, hK, hcompare⟩ := exists_kernelPotential_uniform_exponential_comparison c
  refine ⟨A + b, K * |D|, mul_nonneg hK.le (abs_nonneg D), fun y n hn => ?_⟩
  have hsource : |v n * pairedLogKernel c n| ≤
      |D| * exp (A * n) * (n.factorial : ℝ) ^ m := by
    refine (hc n hn).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self D) (exp_pos _).le) (by positivity)
  calc
    _ ≤ K * exp (b * n) * |v n * pairedLogKernel c n| := hcompare v y n
    _ ≤ K * exp (b * n) * (|D| * exp (A * n) * (n.factorial : ℝ) ^ m) :=
      mul_le_mul_of_nonneg_left hsource (by positivity)
    _ = _ := by rw [add_mul, exp_add]; ring

/-- Each fixed factorial-order class is independent of the real shift. -/
theorem kernelPotential_factorial_order_shift_iff
    (v : ℕ → ℝ) (m : ℕ) (y c : ℝ) :
    (∃ (A D : ℝ) (N : ℕ), ∀ n : ℕ, N ≤ n →
      |v n * pairedLogKernel y n| ≤ D * exp (A * n) * (n.factorial : ℝ) ^ m) ↔
    (∃ (A D : ℝ) (N : ℕ), ∀ n : ℕ, N ≤ n →
      |v n * pairedLogKernel c n| ≤ D * exp (A * n) * (n.factorial : ℝ) ^ m) := by
  have transfer (s t : ℝ) :
      (∃ (A D : ℝ) (N : ℕ), ∀ n : ℕ, N ≤ n →
        |v n * pairedLogKernel s n| ≤ D * exp (A * n) * (n.factorial : ℝ) ^ m) →
      (∃ (A D : ℝ) (N : ℕ), ∀ n : ℕ, N ≤ n →
        |v n * pairedLogKernel t n| ≤ D * exp (A * n) * (n.factorial : ℝ) ^ m) := by
    rintro ⟨A, D, N, hs⟩
    obtain ⟨B, C, _, hbound⟩ := exists_kernelPotential_uniform_factorial_envelope v s m A D N hs
    exact ⟨B, C, N, hbound t⟩
  exact ⟨transfer y c, transfer c y⟩

/-- Finite factorial regularity of any signed kernel potential is shift invariant. -/
theorem weilLogShiftHasFactorialMajorant_kernelPotential_shift_iff
    (v : ℕ → ℝ) (y c : ℝ) :
    WeilLogShiftHasFactorialMajorant (fun n => v n * pairedLogKernel y n) ↔
      WeilLogShiftHasFactorialMajorant (fun n => v n * pairedLogKernel c n) := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, (kernelPotential_factorial_order_shift_iff v m y c).mp hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, (kernelPotential_factorial_order_shift_iff v m y c).mpr hm⟩

/-- Recovery moment regularity is shift invariant even for unbounded histories. -/
theorem weilLogShiftHasFactorialMajorant_recoveryMoment_shift_iff
    (h : ℕ → ℝ) (y c : ℝ) :
    WeilLogShiftHasFactorialMajorant (weilLogShiftRecoveryMoment y h) ↔
      WeilLogShiftHasFactorialMajorant (weilLogShiftRecoveryMoment c h) :=
  weilLogShiftHasFactorialMajorant_kernelPotential_shift_iff
    (weilDeviation (weilLogShiftRecoveryInverse h)) y c

end RHTower
