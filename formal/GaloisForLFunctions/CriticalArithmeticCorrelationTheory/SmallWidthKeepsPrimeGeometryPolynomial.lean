import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheUpwardPrimeRowsHaveUniformKernelBounds

/-!
# Small physical width keeps prime geometry polynomial

At width `c/N≤1`, exponential log-distance estimates give linear integer
radii in `c`. Integer separation confines near pairs to a top fraction of
the horizon. Cauchy–Schwarz then bounds squared near rows by their radius
cubed. The same width estimate bounds exterior product strips linearly.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics BezoutValuationIncidence

/-- A linear integer-distance radius when physical width is at most one. -/
def linearNearRowRadius (c : ℝ) : ℝ := 2 * c * Real.exp 2

/-- A linear exterior product strip when physical width is at most one. -/
def linearPrimeStrip (c : ℝ) : ℕ := ⌈c * Real.exp 1⌉₊

/-- Integer separation confines every near pair to a fixed top fraction of the horizon. -/
theorem nearRow_geometry_small_width {c : ℝ} (hc : 0 < c) {N n j : ℕ}
    (hn : n ∈ Icc 1 N) (hj : j ∈ nearRowIndices c N n) (hw : c / N ≤ 1) :
    |(j : ℝ) - n| ≤ linearNearRowRadius c ∧
      (N : ℝ) ≤ linearNearRowRadius c * n ∧ (N : ℝ) ≤ linearNearRowRadius c * j := by
  obtain ⟨hjN, hjn, hlog⟩ := mem_filter.mp hj
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjN).1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (mem_Icc.mp hn).1 (mem_Icc.mp hn).2
  have hN0 : (0 : ℝ) < N := by linarith only [hN1]
  have he : Real.exp (2 * c / N) - 1 ≤ linearNearRowRadius c / N := by
    calc
      _ ≤ 2 * c / N * Real.exp (2 * c / N) := exp_sub_one_le_mul_exp
      _ ≤ 2 * c / N * Real.exp 2 :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by
            have h := mul_le_mul_of_nonneg_left hw zero_le_two
            simpa only [mul_div_assoc, mul_one] using h)) (by positivity)
      _ = _ := by unfold linearNearRowRadius; ring
  have hdist := (abs_sub_le_of_abs_log_le hj0 hn0 hlog).trans
    (mul_le_mul_of_nonneg_left he hn0.le)
  have hdist' := (abs_sub_le_of_abs_log_le hn0 hj0
    (by simpa only [abs_sub_comm] using hlog)).trans
    (mul_le_mul_of_nonneg_left he hj0.le)
  have hone : (1 : ℝ) ≤ |(j : ℝ) - n| := by
    rcases lt_or_gt_of_ne hjn with h | h
    · have hstep : (j : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_iff.mpr h
      rw [abs_of_neg (by linarith only [hstep])]
      linarith only [hstep]
    · have hstep : (n : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_iff.mpr h
      rw [abs_of_pos (by linarith only [hstep])]
      linarith only [hstep]
  have hrad : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
  refine ⟨hdist.trans ?_, ?_, ?_⟩
  · calc (n : ℝ) * (linearNearRowRadius c / N)
        ≤ N * (linearNearRowRadius c / N) := mul_le_mul_of_nonneg_right
          (by exact_mod_cast (mem_Icc.mp hn).2) (div_nonneg hrad hN0.le)
      _ = linearNearRowRadius c := by field_simp
  · have h := hone.trans hdist
    rw [← mul_div_assoc, le_div_iff₀ hN0] at h
    simpa only [one_mul, mul_one, mul_comm] using h
  · have h := (show (1 : ℝ) ≤ |(n : ℝ) - j| by simpa only [abs_sub_comm] using hone).trans hdist'
    rw [← mul_div_assoc, le_div_iff₀ hN0] at h
    simpa only [one_mul, mul_one, mul_comm] using h

theorem card_nearRowIndices_le_small_width {c : ℝ} (hc : 0 < c) {N n : ℕ} (hn : n ∈ Icc 1 N) (hw : c / N ≤ 1) :
    ((nearRowIndices c N n).card : ℝ) ≤ 2 * linearNearRowRadius c := by
  have hsub : nearRowIndices c N n ⊆
      (Icc 1 N).filter (fun j => j ≠ n ∧ |(j : ℝ) - n| ≤ linearNearRowRadius c) := by
    intro j hj
    exact mem_filter.mpr ⟨(mem_filter.mp hj).1, (mem_filter.mp hj).2.1,
      (nearRow_geometry_small_width hc hn hj hw).1⟩
  exact (show ((nearRowIndices c N n).card : ℝ) ≤
      (((Icc 1 N).filter (fun j => j ≠ n ∧ |(j : ℝ) - n| ≤ linearNearRowRadius c)).card : ℝ)
      by exact_mod_cast card_le_card hsub).trans
    (card_near_le (Icc 1 N) n (by unfold linearNearRowRadius; positivity))

/-- Bounded near-pair numerators give a horizon-independent squared row bound. -/
theorem sum_near_div_sqrt_sq_le_small_width {c K : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 1 ≤ N) (hw : c / N ≤ 1) (F : ℕ → ℕ → ℝ)
    (hF : ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n, |F n j| ≤ K) :
    (∑ n ∈ Icc 1 N, (∑ j ∈ nearRowIndices c N n, F n j / Real.sqrt j) ^ 2) ≤
      4 * linearNearRowRadius c ^ 3 * K ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hB : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
  have hrow : ∀ n ∈ Icc 1 N,
      (∑ j ∈ nearRowIndices c N n, F n j / Real.sqrt j) ^ 2 ≤
        4 * linearNearRowRadius c ^ 3 * K ^ 2 / N := by
    intro n hn
    have hpoint : ∀ j ∈ nearRowIndices c N n,
        (F n j / Real.sqrt j) ^ 2 ≤ K ^ 2 * linearNearRowRadius c / N := by
      intro j hj
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp (mem_filter.mp hj).1).1
      have hsq : F n j ^ 2 ≤ K ^ 2 := by
        have h := mul_self_le_mul_self (abs_nonneg (F n j)) (hF n hn j hj)
        simpa only [← sq, sq_abs] using h
      rw [div_pow, Real.sq_sqrt hj0.le]
      calc F n j ^ 2 / j ≤ K ^ 2 / j := div_le_div_of_nonneg_right hsq hj0.le
        _ ≤ K ^ 2 * linearNearRowRadius c / N := by
          rw [div_le_div_iff₀ hj0 hN0]
          have h := mul_le_mul_of_nonneg_left (nearRow_geometry_small_width hc hn hj hw).2.2 (sq_nonneg K)
          nlinarith only [h]
    have hsum := sum_le_sum hpoint
    rw [sum_const, nsmul_eq_mul] at hsum
    have hcard := card_nearRowIndices_le_small_width hc hn hw
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (nearRowIndices c N n)
      (fun j => F n j / Real.sqrt j) (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, sum_const, nsmul_eq_mul, mul_one] at hcs
    calc
      _ ≤ ((nearRowIndices c N n).card : ℝ) *
          ∑ j ∈ nearRowIndices c N n, (F n j / Real.sqrt j) ^ 2 := by
        simpa only [mul_comm] using hcs
      _ ≤ (2 * linearNearRowRadius c) * ((2 * linearNearRowRadius c) *
          (K ^ 2 * linearNearRowRadius c / N)) :=
        mul_le_mul hcard (hsum.trans (mul_le_mul_of_nonneg_right hcard (by positivity)))
          (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ n ∈ Icc 1 N, 4 * linearNearRowRadius c ^ 3 * K ^ 2 / N := sum_le_sum hrow
    _ = _ := by
      rw [sum_const, nsmul_eq_mul, Nat.card_Icc]
      simp only [Nat.add_sub_cancel]
      field_simp

/-- The product cutoff exceeds the horizon by at most a fixed number of integers. -/
theorem exteriorPrimeCutoff_bounds_small_width {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (hwidth : c / N ≤ 1) :
    N ≤ exteriorPrimeCutoff c N ∧ exteriorPrimeCutoff c N ≤ N + linearPrimeStrip c := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 ≤ c / N := (div_pos hc hN0).le
  have hNc : (N : ℝ) * Real.exp (c / N) ≤ N + c * Real.exp 1 := by
    calc
      _ = N + N * (Real.exp (c / N) - 1) := by ring
      _ ≤ N + N * (c / N * Real.exp (c / N)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (show Real.exp (c / N) - 1 ≤ c / N * Real.exp (c / N) from exp_sub_one_le_mul_exp) hN0.le)
      _ = N + c * Real.exp (c / N) := by field_simp
      _ ≤ N + c * Real.exp 1 := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr hwidth) hc.le)
  constructor
  · have h : (N : ℝ) ≤ (exteriorPrimeCutoff c N : ℝ) :=
      (le_mul_of_one_le_right hN0.le (Real.one_le_exp_iff.mpr hw)).trans (Nat.le_ceil _)
    exact_mod_cast h
  · apply Nat.ceil_le.mpr
    have hB : c * Real.exp 1 ≤ (linearPrimeStrip c : ℝ) := Nat.le_ceil _
    refine hNc.trans ?_
    rw [Nat.cast_add]
    exact add_le_add le_rfl hB

/-- A near product beyond the horizon can reach only the fixed boundary strip. -/
theorem exterior_prime_near_boundary_small_width {c : ℝ} (hc : 0 < c) {N n ℓ : ℕ}
    (hn : n ∈ Icc 1 N) (hℓ : N < ℓ)
    (hlog : |Real.log ℓ - Real.log n| ≤ c / N) (hwidth : c / N ≤ 1) :
    N - linearPrimeStrip c ≤ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le N) hℓ
  have hN0 : (0 : ℝ) < N := hn0.trans_le hnN
  have hgap := abs_sub_le_of_abs_log_le hℓ0 hn0 hlog
  have hB : |(ℓ : ℝ) - n| ≤ c * Real.exp 1 := by
    calc
      _ ≤ n * (Real.exp (c / N) - 1) := hgap
      _ ≤ n * (c / N * Real.exp (c / N)) :=
        mul_le_mul_of_nonneg_left exp_sub_one_le_mul_exp hn0.le
      _ ≤ N * (c / N * Real.exp (c / N)) :=
        mul_le_mul_of_nonneg_right hnN (by positivity)
      _ = c * Real.exp (c / N) := by field_simp
      _ ≤ c * Real.exp 1 := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hwidth) hc.le
  have hB' := (le_abs_self ((ℓ : ℝ) - n)).trans (hB.trans (Nat.le_ceil _))
  change (ℓ : ℝ) - n ≤ (linearPrimeStrip c : ℝ) at hB'
  have hnat : ℓ ≤ n + linearPrimeStrip c := by
    have h : (ℓ : ℝ) ≤ n + (linearPrimeStrip c : ℝ) := by linarith only [hB']
    exact_mod_cast h
  omega

private theorem one_le_abs_gap_small_width {T j : ℕ} (hne : T ≠ j) :
    (1 : ℝ) ≤ |(j : ℝ) - T| := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hstep : (T : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_iff.mpr h
    rw [abs_of_nonneg (by linarith only [hstep])]
    linarith only [hstep]
  · have hstep : (j : ℝ) + 1 ≤ T := by exact_mod_cast Nat.succ_le_iff.mpr h
    rw [abs_of_nonpos (by linarith only [hstep])]
    linarith only [hstep]

/-- A nonzero integer log gap at scale `c/N` forces both indices to be macroscopic. -/
theorem logWindow_integer_separation_small_width {c : ℝ} (hc : 0 < c) {N T j : ℕ}
    (hN : 1 ≤ N) (hT : 1 ≤ T) (hj : 1 ≤ j) (hne : T ≠ j)
    (hlog : |Real.log j - Real.log T| ≤ c / N) (hwidth : c / N ≤ 1) :
    (N : ℝ) ≤ c * Real.exp 1 * T ∧ (N : ℝ) ≤ c * Real.exp 1 * j := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have he : Real.exp (c / N) - 1 ≤ (c * Real.exp 1) / N := by
    calc
      _ ≤ c / N * Real.exp (c / N) := exp_sub_one_le_mul_exp
      _ ≤ c / N * Real.exp 1 := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hwidth) (div_pos hc hN0).le
      _ = _ := by ring
  have hdist := (abs_sub_le_of_abs_log_le hj0 hT0 hlog).trans
    (mul_le_mul_of_nonneg_left he hT0.le)
  have hdist' := (abs_sub_le_of_abs_log_le hT0 hj0
    (by simpa only [abs_sub_comm] using hlog)).trans
    (mul_le_mul_of_nonneg_left he hj0.le)
  have hgap := one_le_abs_gap_small_width hne
  have hgap' : (1 : ℝ) ≤ |(T : ℝ) - j| := by simpa only [abs_sub_comm] using hgap
  constructor
  · have h := hgap.trans hdist
    rw [← mul_div_assoc, le_div_iff₀ hN0] at h
    simpa only [one_mul, mul_one, mul_comm] using h
  · have h := hgap'.trans hdist'
    rw [← mul_div_assoc, le_div_iff₀ hN0] at h
    simpa only [one_mul, mul_one, mul_comm] using h

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.nearRow_geometry_small_width
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.sum_near_div_sqrt_sq_le_small_width
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exteriorPrimeCutoff_bounds_small_width

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.logWindow_integer_separation_small_width
