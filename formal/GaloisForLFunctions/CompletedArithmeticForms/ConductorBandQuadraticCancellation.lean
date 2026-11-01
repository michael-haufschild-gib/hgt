import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandOverlapAndNonRatioBounds

/-!
# Quadratic near-kernel cancellation

Integer separation confines both the near archimedean row and the non-ratio
prime row to the same terminal interval. Testing against a conductor packet
uses its mass on that interval a second time.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset
open scoped RealInnerProductSpace Classical
namespace GaloisForLFunctions.CompletedArithmeticForms
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  CriticalArithmeticCorrelationTheory ArithmeticElectrostatics ArithmeticIntersectionTheory
  SpacingScaleHarmonicAnalysis

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

private theorem bumpCorr_eq_zero_of_small_row {g : ℝ → ℝ} {c : ℝ} {N n j : ℕ}
    (hc : 0 < c) (hn : 0 < n) (hj : 0 < j) (hjn : j ≠ n)
    (hw : c / N ≤ 1) (hsmall : linearNearRowRadius c * n < N)
    (hsupp : ∀ t, t ∉ Set.Icc 0 (c / N) → g t = 0) :
    bumpCorr g (Real.log j - Real.log n) = 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < N :=
    (mul_pos (by unfold linearNearRowRadius; positivity) hn0).trans hsmall
  have hN1 : 1 ≤ N := by exact_mod_cast hN0
  apply bumpCorr_eq_zero hsupp
  by_contra hgap
  have hsep := (logWindow_integer_separation_small_width hc hN1 hn hj
    (Ne.symm hjn) (le_of_not_gt hgap) hw).1
  have he12 : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
  have hrad : c * Real.exp 1 ≤ linearNearRowRadius c := by
    unfold linearNearRowRadius
    nlinarith only [hc, he12, Real.exp_pos 1]
  exact (not_le_of_gt hsmall)
    (hsep.trans (mul_le_mul_of_nonneg_right hrad hn0.le))

/-- Both terms of the near cancellation vanish below their integer-separation threshold. -/
theorem overlap_sub_downward_row_eq_zero_of_small_row {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0)
    {c : ℝ} (hc : 0 < c) {N n : ℕ} (hn : n ∈ Icc 1 N) (hw : c / N ≤ 1)
    (hsmall : linearNearRowRadius c * n < N)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    primeHorizonExtension
      (Matrix.toEuclideanLin (overlapMatrix φ c N) u - downwardPrimeVector φ c N u) n = 0 := by
  have hn1 := (mem_Icc.mp hn).1
  have hN1 := hn1.trans (mem_Icc.mp hn).2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨_, hgsupp, _⟩ := atomDilate_facts hφ hsupp (div_pos hc hN0)
  have hov : (Matrix.toEuclideanLin (overlapMatrix φ c N) u) ⟨n, hn⟩ = 0 := by
    change (∑ j : PrimeHorizonIndex N, overlapMatrix φ c N ⟨n, hn⟩ j * u j) = 0
    apply sum_eq_zero
    intro j _
    dsimp only [overlapMatrix]
    split_ifs with hnear
    · have hj : (j : ℕ) ∈ nearRowIndices c N n := mem_filter.mpr ⟨j.property,
        Ne.symm hnear.1, by simpa only [mul_div_assoc] using hnear.2⟩
      exact False.elim ((not_le_of_gt hsmall) (nearRow_geometry_small_width hc hn hj hw).2.1)
    · exact zero_mul _
  have hdown : downwardPrimeVector φ c N u ⟨n, hn⟩ = 0 := by
    change downwardPrimeRow (atomDilate φ (c / N)) N (primeHorizonExtension u) n /
      (∫ t, atomDilate φ (c / N) t ^ 2) = 0
    suffices hh : downwardPrimeRow (atomDilate φ (c / N)) N (primeHorizonExtension u) n = 0 by
      rw [hh, zero_div]
    rw [downwardPrimeRow_eq_sum hgsupp (div_pos hc hN0).le hn (primeHorizonExtension u)]
    apply sum_eq_zero
    intro k _
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [_root_.RHTower.vonMangoldtAtom]
    · apply mul_eq_zero.mpr
      right
      apply sum_eq_zero
      intro j hj
      by_cases hnj : n = k * j
      · simp only [if_pos hnj, mul_zero]
      · have hj0 : 0 < j := (mem_Icc.mp hj).1
        have hlogid : Real.log k - (Real.log n - Real.log j) =
            Real.log (k * j : ℕ) - Real.log n := by
          rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hk.ne') (by exact_mod_cast hj0.ne')]
          ring
        rw [if_neg hnj, hlogid,
          bumpCorr_eq_zero_of_small_row hc hn1 (Nat.mul_pos hk hj0) (Ne.symm hnj) hw hsmall hgsupp,
          mul_zero]
  rw [primeHorizonExtension_coe _ ⟨n, hn⟩]
  change (Matrix.toEuclideanLin (overlapMatrix φ c N) u) ⟨n, hn⟩ -
    downwardPrimeVector φ c N u ⟨n, hn⟩ = 0
  rw [hov, hdown, sub_self]

/-- Quadratic cancellation gains the terminal mass of both conductor packets. -/
theorem exists_overlap_sub_downward_inner_le_of_mem_conductorSubspace {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0)
    (hM : 0 < ∫ t, φ t ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {R N : ℕ} {c : ℝ},
      2 ≤ R → R * R ≤ N → 18 * (1 + Real.log R) ≤ Real.log N →
      1 ≤ c → c / N ≤ 1 / 3 →
      ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
      ∀ {u : EuclideanSpace ℝ (PrimeHorizonIndex N)}, u ∈ conductorSubspace R N →
        |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u - downwardPrimeVector φ c N u, u⟫| ≤
          C * (c ^ 2 * (1 + Real.log R) * (1 + Real.log c) / Real.log N +
            c ^ 2 * (R : ℝ) * Real.sqrt (Real.log N / N)) * ‖u‖ ^ 2 := by
  obtain ⟨C, hC, hnorm⟩ := exists_overlap_sub_downward_norm_le_of_mem_conductorSubspace hφ hsupp hM
  refine ⟨10 * C, by positivity, ?_⟩
  intro R N c hR hRN hlog hc1 hw1 hsize u hu
  have hc0 := zero_lt_one.trans_le hc1
  have hN1 : 1 ≤ N := (Nat.mul_pos (by omega : 0 < R) (by omega : 0 < R)).trans_le hRN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL1 : 1 ≤ Real.log N := by
    have hh := Real.log_natCast_nonneg R
    linarith only [hlog, hh]
  have hL0 := zero_lt_one.trans_le hL1
  have hw : c / N ≤ 1 := hw1.trans (by norm_num)
  have hcN : c ≤ N := (div_le_one hN0).mp hw
  let T := linearNearRowRadius c + 1
  let S := (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / n < T)
  let d := Matrix.toEuclideanLin (overlapMatrix φ c N) u - downwardPrimeVector φ c N u
  let r := Real.sqrt ((1 + Real.log c) / Real.log N)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hratio0 : 0 ≤ (1 + Real.log c) / Real.log N := by
    have hh := Real.log_nonneg hc1
    positivity
  have hrsq : r ^ 2 = (1 + Real.log c) / Real.log N := Real.sq_sqrt hratio0
  have hr2 : r ≤ 2 := by
    have hlogc := Real.log_le_log hc0 hcN
    have hh : (1 + Real.log c) / Real.log N ≤ 4 := by
      rw [div_le_iff₀ hL0]
      linarith only [hlogc, hL1]
    nlinarith only [hh, hrsq, hr0]
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
    exact overlap_sub_downward_row_eq_zero_of_small_row hφ hsupp hc0 hn hw hsmall u
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
  have huTop : (∑ n ∈ S, primeHorizonExtension u n ^ 2) ≤ 20 * r ^ 2 * ‖u‖ ^ 2 := by
    have hT1 : 1 ≤ T := by
      dsimp only [T, linearNearRowRadius]
      have hh : 0 ≤ 2 * c * Real.exp 2 := by positivity
      linarith only [hh]
    have ht := sum_quotient_tail_sq_le_of_mem_conductorSubspace hR hT1 hsize hlog hu
    have hlogT := log_two_mul_near_radius_le hc1
    calc
      _ ≤ (2 * (Real.log (2 * T) + 3) * ‖u‖ ^ 2) / Real.log N :=
        (le_div_iff₀' hL0).mpr ht
      _ ≤ (20 * (1 + Real.log c) * ‖u‖ ^ 2) / Real.log N :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith only [hlogT]) (sq_nonneg _)) hL0.le
      _ = _ := by rw [hrsq]; ring
  have hdTop : (∑ n ∈ S, primeHorizonExtension d n ^ 2) ≤ ‖d‖ ^ 2 := by
    rw [← sum_primeHorizonExtension_sq d]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _
  have hcross : |⟪d, u⟫| ≤ 5 * ‖d‖ * r * ‖u‖ := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (primeHorizonExtension d) (primeHorizonExtension u)
    have hs : ⟪d, u⟫ ^ 2 ≤ (5 * ‖d‖ * r * ‖u‖) ^ 2 := by
      rw [hinner]
      calc
        _ ≤ (∑ n ∈ S, primeHorizonExtension d n ^ 2) *
            (∑ n ∈ S, primeHorizonExtension u n ^ 2) := hcs
        _ ≤ ‖d‖ ^ 2 * (20 * r ^ 2 * ‖u‖ ^ 2) :=
          mul_le_mul hdTop huTop (sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
        _ ≤ (5 * ‖d‖ * r * ‖u‖) ^ 2 := by
          nlinarith only [mul_nonneg (sq_nonneg ‖d‖) (mul_nonneg (sq_nonneg r) (sq_nonneg ‖u‖))]
    have hrhs : 0 ≤ 5 * ‖d‖ * r * ‖u‖ := by positivity
    nlinarith only [hs, hrhs, sq_abs ⟪d, u⟫, abs_nonneg ⟪d, u⟫]
  have hnr := hnorm hR hRN hlog hc1 hw1 hsize hu
  let X := c ^ 2 * (1 + Real.log R)
  let Y := c ^ 2 * (R : ℝ) * Real.sqrt (Real.log N / N)
  have hX0 : 0 ≤ X := by dsimp only [X]; have hh := Real.log_natCast_nonneg R; positivity
  have hY0 : 0 ≤ Y := by dsimp only [Y]; positivity
  have hcoef : 5 * C * (X * r + Y) * r ≤ 10 * C * (X * r ^ 2 + Y) := by
    have hh := mul_le_mul_of_nonneg_left hr2 hY0
    have hhC := mul_le_mul_of_nonneg_left hh (show 0 ≤ 5 * C by positivity)
    have hxC := mul_nonneg hC.le (mul_nonneg hX0 (sq_nonneg r))
    nlinarith only [hhC, hxC]
  calc
    _ ≤ 5 * ‖d‖ * r * ‖u‖ := hcross
    _ ≤ 5 * (C * (X * r + Y) * ‖u‖) * r * ‖u‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnr (by norm_num)) hr0) (norm_nonneg u)
    _ = (5 * C * (X * r + Y) * r) * ‖u‖ ^ 2 := by ring
    _ ≤ (10 * C * (X * r ^ 2 + Y)) * ‖u‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    _ = _ := by dsimp only [X, Y]; rw [hrsq]; ring

end GaloisForLFunctions.CompletedArithmeticForms

#print axioms GaloisForLFunctions.CompletedArithmeticForms.overlap_sub_downward_row_eq_zero_of_small_row
#print axioms GaloisForLFunctions.CompletedArithmeticForms.exists_overlap_sub_downward_inner_le_of_mem_conductorSubspace
