import GaloisForLFunctions.CompletedArithmeticForms.WeightedConductorCrossBounds
import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandQuadraticCancellation

/-!
# Terminal support sharpens the weighted near pairing

The merged near-Gamma/downward-prime output vanishes below its integer-separation
threshold. Testing the weighted norm bound against the packet only on that terminal
interval contributes a second logarithmic tail factor.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  ArithmeticElectrostatics

private theorem log_two_mul_near_radius_le {c : ℝ} (hc1 : 1 ≤ c) :
    Real.log (2 * (linearNearRowRadius c + 1)) + 3 ≤ 10 * (1 + Real.log c) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have he2 : Real.exp 2 ≤ 8 := by
    have h1 : Real.exp 1 ≤ 14 / 5 := by linarith [Real.exp_one_lt_d9]
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith only [h1, h2, Real.exp_pos 1]
  have hlin : 2 * (linearNearRowRadius c + 1) ≤ 34 * c := by
    unfold linearNearRowRadius
    nlinarith only [hc1, he2]
  have hlog34 : Real.log 34 ≤ 6 := by
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have he6 : (34 : ℝ) ≤ Real.exp 6 := by
      have hpow : (2 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 := pow_le_pow_left₀ (by norm_num) he1 6
      rw [← Real.exp_nat_mul] at hpow
      norm_num at hpow
      linarith only [hpow]
    exact (Real.log_le_log (by norm_num) he6).trans_eq (Real.log_exp 6)
  have hlog_le : Real.log (2 * (linearNearRowRadius c + 1)) ≤ 6 + Real.log c := by
    calc
      Real.log (2 * (linearNearRowRadius c + 1)) ≤ Real.log (34 * c) :=
        Real.log_le_log (by unfold linearNearRowRadius; positivity) hlin
      _ = Real.log 34 + Real.log c := Real.log_mul (by norm_num) hc0.ne'
      _ ≤ 6 + Real.log c := by linarith only [hlog34]
  have hlc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  linarith only [hlog_le, hlc0]

/-- Terminal support retains an extra logarithmic denominator in the weighted
quadratic near pairing, without a new arithmetic cancellation assumption. -/
theorem exists_overlap_sub_downward_inner_sq_le_logarithmic_terminal_weight_of_four_log {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0)
    (hM : 0 < ∫ t, φ t ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {R N : ℕ} {c : ℝ},
      2 ≤ R → R * R ≤ N → 4 * Real.log R + 18 ≤ Real.log N →
      1 ≤ c → c / N ≤ 1 / 3 →
      ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
      ∀ a : ℕ → ℝ,
      let u := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
      |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u - downwardPrimeVector φ c N u, u⟫| ^ 2 ≤
        C * c ^ 4 * (1 + Real.log R) *
          ((1 + Real.log c) ^ 2 / (Real.log N) ^ 2 +
            (R : ℝ) ^ 2 * (1 + Real.log c) / N) *
          (∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2) * ‖u‖ ^ 2 := by
  obtain ⟨C₀, hC₀, hnorm⟩ := exists_overlap_sub_downward_sq_le_logarithmic_weight_of_four_log hφ hsupp hM
  refine ⟨20 * C₀, by positivity, ?_⟩
  intro R N c hR hRN hlog hc1 hw hsize a
  let u := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
  let d := Matrix.toEuclideanLin (overlapMatrix φ c N) u - downwardPrimeVector φ c N u
  let T := linearNearRowRadius c + 1
  let S := (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / n < T)
  have hu : u ∈ conductorSubspace R N :=
    sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R N a
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hN : (0 : ℝ) < N := by
    exact_mod_cast (Nat.mul_pos (by omega : 0 < R) (by omega : 0 < R)).trans_le hRN
  have hL : 0 < Real.log N := by linarith only [hlog, Real.log_natCast_nonneg R]
  have hlogc : 0 ≤ 1 + Real.log c := by linarith only [Real.log_nonneg hc1]
  have hd_zero : ∀ n ∈ Icc 1 N, n ∉ S → primeHorizonExtension d n = 0 := by
    intro n hn hnS
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnlarge : T ≤ (N : ℝ) / n := by
      apply le_of_not_gt
      intro hh
      exact hnS (mem_filter.mpr ⟨hn, hh⟩)
    have hh := (le_div_iff₀ hn0).mp hnlarge
    have hsmall : linearNearRowRadius c * n < N := by
      dsimp only [T] at hh
      nlinarith only [hh, hn0]
    exact overlap_sub_downward_row_eq_zero_of_small_row hφ hsupp hc hn
      (hw.trans (by norm_num)) hsmall u
  have hinner : ⟪d, u⟫ = ∑ n ∈ S, primeHorizonExtension d n * primeHorizonExtension u n := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ j : PrimeHorizonIndex N, u.ofLp j * d.ofLp j) = _
    trans ∑ n ∈ Icc 1 N, primeHorizonExtension d n * primeHorizonExtension u n
    · rw [← sum_coe_sort (Icc 1 N)]
      exact sum_congr rfl fun j _ => by
        rw [primeHorizonExtension_coe d j, primeHorizonExtension_coe u j]
        exact mul_comm _ _
    · symm
      apply sum_subset (filter_subset _ _)
      intro n hn hnS
      rw [hd_zero n hn hnS, zero_mul]
  have huTop : (∑ n ∈ S, primeHorizonExtension u n ^ 2) ≤
      20 * (1 + Real.log c) / Real.log N * ‖u‖ ^ 2 := by
    have hT1 : 1 ≤ T := by
      dsimp only [T, linearNearRowRadius]
      have hh : 0 ≤ 2 * c * Real.exp 2 := by positivity
      linarith only [hh]
    have ht := sum_quotient_tail_sq_le_of_mem_conductorSubspace_of_four_log hR hT1 hsize hlog hu
    have hlogT := log_two_mul_near_radius_le hc1
    calc
      _ ≤ (2 * (Real.log (2 * T) + 3) * ‖u‖ ^ 2) / Real.log N :=
        (le_div_iff₀' hL).mpr ht
      _ ≤ (20 * (1 + Real.log c) * ‖u‖ ^ 2) / Real.log N :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith only [hlogT]) (sq_nonneg _)) hL.le
      _ = _ := by ring
  have hdTop : (∑ n ∈ S, primeHorizonExtension d n ^ 2) ≤ ‖d‖ ^ 2 := by
    rw [← sum_primeHorizonExtension_sq d]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _
  have hpair : |⟪d, u⟫| ^ 2 ≤
      ‖d‖ ^ 2 * (20 * (1 + Real.log c) / Real.log N * ‖u‖ ^ 2) := by
    rw [sq_abs, hinner]
    exact (sum_mul_sq_le_sq_mul_sq S (primeHorizonExtension d) (primeHorizonExtension u)).trans
      (mul_le_mul hdTop huTop (sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _))
  have hnormBound := hnorm hR hRN hlog hc1 hw hsize a
  have hcoef0 : 0 ≤ 20 * (1 + Real.log c) / Real.log N * ‖u‖ ^ 2 := by positivity
  have hh := hpair.trans (mul_le_mul_of_nonneg_right hnormBound hcoef0)
  refine hh.trans_eq ?_
  change _ = (20 * C₀) * c ^ 4 * (1 + Real.log R) *
    ((1 + Real.log c) ^ 2 / (Real.log N) ^ 2 + (R : ℝ) ^ 2 * (1 + Real.log c) / N) *
    (∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2) * ‖u‖ ^ 2
  field_simp [hL.ne', hN.ne']

/-- The terminal near pairing in the range `18 (1 + log R) ≤ log N`. -/
theorem exists_overlap_sub_downward_inner_sq_le_logarithmic_terminal_weight {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0)
    (hM : 0 < ∫ t, φ t ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {R N : ℕ} {c : ℝ},
      2 ≤ R → R * R ≤ N → 18 * (1 + Real.log R) ≤ Real.log N →
      1 ≤ c → c / N ≤ 1 / 3 →
      ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
      ∀ a : ℕ → ℝ,
      let u := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
      |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u - downwardPrimeVector φ c N u, u⟫| ^ 2 ≤
        C * c ^ 4 * (1 + Real.log R) *
          ((1 + Real.log c) ^ 2 / (Real.log N) ^ 2 +
            (R : ℝ) ^ 2 * (1 + Real.log c) / N) *
          (∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2) * ‖u‖ ^ 2 := by
  obtain ⟨C, hC, h⟩ := exists_overlap_sub_downward_inner_sq_le_logarithmic_terminal_weight_of_four_log
    hφ hsupp hM
  exact ⟨C, hC, fun hR hRN hlog hc1 hw hsize a =>
    h hR hRN (four_log_add_eighteen_le_of_log_le hlog) hc1 hw hsize a⟩

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
