import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandOverlapAndNonRatioBounds
import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandQuadraticCenterBounds

/-!
# The packet linear moment removes the overlap logarithm

Near-row cardinality retains its factor `n/N`. A symmetric quadratic Schur
estimate then uses the packet's linear moment instead of its full terminal mass,
leaving a loss linear in the overlap.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  ArithmeticElectrostatics BezoutValuationIncidence SignedArithmeticHodgeTheory
  SuccessorShellArithmetic ArithmeticIntersectionTheory ArithmeticEffectivityTheory
  HTGeometry RenormalizedBiarithmeticGeometry

private theorem nearRow_distance_le_relative_radius {c : ℝ} (hc : 0 < c) {N n j : ℕ}
    (hn : n ∈ Icc 1 N) (hj : j ∈ nearRowIndices c N n) (hw : c / N ≤ 1) :
    |(j : ℝ) - n| ≤ (n : ℝ) * (linearNearRowRadius c / N) := by
  obtain ⟨hjN, -, hlog⟩ := mem_filter.mp hj
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjN).1
  have hN0 : (0 : ℝ) < N := by
    exact_mod_cast (mem_Icc.mp hn).1.trans (mem_Icc.mp hn).2
  have he : Real.exp (2 * c / N) - 1 ≤ linearNearRowRadius c / N := by
    calc
      _ ≤ 2 * c / N * Real.exp (2 * c / N) := exp_sub_one_le_mul_exp
      _ ≤ 2 * c / N * Real.exp 2 := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by
          have hh := mul_le_mul_of_nonneg_left hw zero_le_two
          simpa only [mul_div_assoc, mul_one] using hh)) (by positivity)
      _ = _ := by unfold linearNearRowRadius; ring
  exact (abs_sub_le_of_abs_log_le hj0 hn0 hlog).trans
    (mul_le_mul_of_nonneg_left he hn0.le)

/-- Near-row cardinality retains its relative horizon position. -/
theorem card_nearRowIndices_le_relative_radius {c : ℝ} (hc : 0 < c)
    {N n : ℕ} (hn : n ∈ Icc 1 N) (hw : c / N ≤ 1) :
    ((nearRowIndices c N n).card : ℝ) ≤ 2 * linearNearRowRadius c * ((n : ℝ) / N) := by
  let r := (n : ℝ) * (linearNearRowRadius c / N)
  have hr : 0 ≤ r := by dsimp only [r, linearNearRowRadius]; positivity
  have hsub : nearRowIndices c N n ⊆
      (Icc 1 N).filter (fun j => j ≠ n ∧ |(j : ℝ) - n| ≤ r) := by
    intro j hj
    exact mem_filter.mpr ⟨(mem_filter.mp hj).1, (mem_filter.mp hj).2.1,
      nearRow_distance_le_relative_radius hc hn hj hw⟩
  have hh := (show ((nearRowIndices c N n).card : ℝ) ≤
      (((Icc 1 N).filter (fun j => j ≠ n ∧ |(j : ℝ) - n| ≤ r)).card : ℝ)
      by exact_mod_cast card_le_card hsub).trans (card_near_le (Icc 1 N) n hr)
  exact hh.trans_eq (by dsimp only [r]; ring)

private theorem near_pair_abs_product_le_row_square (c : ℝ) (N : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, ∑ j ∈ nearRowIndices c N n, |f n| * |f j|) ≤
      ∑ n ∈ Icc 1 N, ((nearRowIndices c N n).card : ℝ) * f n ^ 2 := by
  have hswap : (∑ n ∈ Icc 1 N, ∑ j ∈ nearRowIndices c N n, f j ^ 2) =
      ∑ n ∈ Icc 1 N, ∑ _j ∈ nearRowIndices c N n, f n ^ 2 := by
    simp only [nearRowIndices, sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun n _ => sum_congr rfl fun j _ => ?_
    simp only [ne_comm, abs_sub_comm]
  have htwice : 2 * (∑ n ∈ Icc 1 N, ∑ j ∈ nearRowIndices c N n, |f n| * |f j|) ≤
      (∑ n ∈ Icc 1 N, ∑ j ∈ nearRowIndices c N n, f n ^ 2) +
        ∑ n ∈ Icc 1 N, ∑ j ∈ nearRowIndices c N n, f j ^ 2 := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun n _ => ?_
    rw [mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun j _ => ?_
    nlinarith only [sq_nonneg (|f n| - |f j|), sq_abs (f n), sq_abs (f j)]
  rw [hswap] at htwice
  simp only [sum_const, nsmul_eq_mul] at htwice
  linarith only [htwice]

private theorem overlapMatrix_inner_eq (φ : ℝ → ℝ) (c : ℝ) (N : ℕ)
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) x, y⟫ =
      ∑ n ∈ Icc 1 N, primeHorizonExtension y n *
        ∑ j ∈ nearRowIndices c N n,
          (atomArchPair (atomDilate φ (c / N)) n j / (∫ t, atomDilate φ (c / N) t ^ 2) +
            (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j) *
            primeHorizonExtension x j := by
  let K_ov : ℕ → ℕ → ℝ := fun n j =>
    atomArchPair (atomDilate φ (c / N)) n j / (∫ t, atomDilate φ (c / N) t ^ 2) +
      (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ n : PrimeHorizonIndex N, y.ofLp n *
    ∑ j : PrimeHorizonIndex N, overlapMatrix φ c N n j * x.ofLp j) = _
  rw [← sum_coe_sort (Icc 1 N) (fun n => primeHorizonExtension y n *
    ∑ j ∈ nearRowIndices c N n, K_ov n j * primeHorizonExtension x j)]
  refine sum_congr rfl fun n _ => ?_
  rw [primeHorizonExtension_coe y n]
  congr 1
  rw [nearRowIndices, sum_filter, ← sum_coe_sort (Icc 1 N)]
  refine sum_congr rfl fun j _ => ?_
  rw [primeHorizonExtension_coe x j]
  dsimp only [overlapMatrix, K_ov]
  by_cases h : (j : ℕ) ≠ (n : ℕ) ∧ |Real.log (j : ℕ) - Real.log (n : ℕ)| ≤ 2 * c / N
  · rw [if_pos ⟨Ne.symm h.1, by rw [← mul_div_assoc]; exact h.2⟩, if_pos h]
  · rw [if_neg fun h' => h ⟨Ne.symm h'.1, by rw [mul_div_assoc]; exact h'.2⟩, if_neg h, zero_mul]

/-- The overlap quadratic form costs only `Oφ(c)` on a conductor packet.
The finite-period linear moment removes the logarithm from terminal-mass bounds. -/
theorem exists_overlapMatrix_self_inner_le_linear_of_four_log {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {R N : ℕ} {c : ℝ},
      2 ≤ R → R ^ 4 ≤ N → 4 * Real.log R + 18 ≤ Real.log N →
      1 ≤ c → c ≤ Real.log N → c / N ≤ 1 / 3 →
      ∀ {u : EuclideanSpace ℝ (PrimeHorizonIndex N)}, u ∈ conductorSubspace R N →
        |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u, u⟫| ≤ C * c * ‖u‖ ^ 2 := by
  obtain ⟨K_pair, hK_pair0, hpair⟩ := exists_abs_atomArchPair_near_sub_le hφ hsupp hM
  let M_ov : ℝ := K_pair + 2 + Real.exp (1 / 2)
  have hM_ov : 0 < M_ov := by dsimp only [M_ov]; positivity
  refine ⟨16 * Real.exp 2 * M_ov, by positivity, ?_⟩
  intro R N c hR hR4 hlog hc1 hcL hw1 u hu
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hw : c / N ≤ 1 := hw1.trans (by norm_num)
  have hN1 : 1 ≤ N := (pow_pos (by omega : 0 < R) 4).trans_le hR4
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hcN2 : 2 * c ≤ N := by
    have hh := (div_le_iff₀ hN0).mp hw1
    linarith only [hh, hc0]
  have hL1 : 1 ≤ Real.log N := hc1.trans hcL
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL1
  let g := atomDilate φ (c / N)
  let G0 := ∫ t, g t ^ 2
  let K_ov : ℕ → ℕ → ℝ := fun n j =>
    atomArchPair g n j / G0 + (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j
  have hKov_le : ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n,
      |K_ov n j| ≤ M_ov * Real.log N := by
    intro n hn j hj
    have hw0 : 0 < c / N := div_pos hc0 hN0
    have hs : |Real.log j - Real.log n| ≤ 2 * (c / N) := by
      simpa only [mul_div_assoc] using (mem_filter.mp hj).2.2
    let q := shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ t, φ t ^ 2)
    have hrem : |atomArchPair g n j / G0 - Real.log (1 / (c / N)) * q| ≤ K_pair := by
      simpa only [g, G0, q, mul_div_assoc] using hpair (c / N) hw0 hw1 n j hs
    have hq : |q| ≤ 1 := by
      dsimp only [q]
      rw [abs_div, abs_of_pos hM, div_le_one hM]
      exact abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp) _
    have hlog_inv : |Real.log (1 / (c / N))| ≤ Real.log N := by
      have heq : Real.log (1 / (c / N)) = Real.log N - Real.log c := by
        rw [one_div, Real.log_inv, Real.log_div hc0.ne' hN0.ne']; ring
      rw [heq, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hc0 (by linarith only [hcN2, hc0])))]
      linarith [Real.log_nonneg hc1]
    have hnc : |(completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j| ≤
        (1 + Real.exp (1 / 2)) * Real.log N := by
      have h1 := abs_nearCenter_entry_le (φ := φ) (m := 1) zero_lt_one hN1 hcN2 hn hj
      have hm1 : ∀ k, normalizedRamanujanMode 1 k = 1 := fun k => by
        rw [normalizedRamanujanMode, ramanujanMode_one, Nat.totient_one, Nat.cast_one,
          Real.sqrt_one, div_one]
      rw [hm1 j, mul_one, range_one, sum_singleton, hm1 0, abs_one, mul_one,
        abs_of_nonneg (completeWeilPoleShift_nonneg φ hc0.le)] at h1
      have hpole := (completeWeilPoleShift_le hφ.continuous hsupp hM hc0.le).trans hcL
      exact h1.trans (by simpa only [mul_comm (Real.log N)] using
        mul_le_mul_of_nonneg_right hpole (by positivity))
    have hid : K_ov n j = (atomArchPair g n j / G0 - Real.log (1 / (c / N)) * q) +
        Real.log (1 / (c / N)) * q +
        (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j := by
      dsimp only [K_ov]; ring
    rw [hid]
    calc
      _ ≤ |atomArchPair g n j / G0 - Real.log (1 / (c / N)) * q| +
            |Real.log (1 / (c / N)) * q| +
            |(completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ K_pair + Real.log N * 1 + (1 + Real.exp (1 / 2)) * Real.log N := by
        rw [abs_mul]
        exact add_le_add (add_le_add hrem (mul_le_mul hlog_inv hq (abs_nonneg _) hL0.le)) hnc
      _ ≤ M_ov * Real.log N := by
        dsimp only [M_ov]; nlinarith only [hL1, hK_pair0]
  let f := primeHorizonExtension u
  have hpairing : |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u, u⟫| ≤
      (M_ov * Real.log N) *
        ∑ n ∈ Icc 1 N, ((nearRowIndices c N n).card : ℝ) * f n ^ 2 := by
    rw [overlapMatrix_inner_eq]
    calc
      _ ≤ ∑ n ∈ Icc 1 N, ∑ j ∈ nearRowIndices c N n,
          |f n * (K_ov n j * f j)| := by
        simp only [mul_sum]
        exact (abs_sum_le_sum_abs _ _).trans
          (sum_le_sum fun n _ => abs_sum_le_sum_abs _ _)
      _ ≤ ∑ n ∈ Icc 1 N, ∑ j ∈ nearRowIndices c N n,
          (M_ov * Real.log N) * (|f n| * |f j|) := by
        refine sum_le_sum fun n hn => sum_le_sum fun j hj => ?_
        rw [abs_mul, abs_mul]
        have hh := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hKov_le n hn j hj) (abs_nonneg (f j))) (abs_nonneg (f n))
        exact hh.trans_eq (by ring)
      _ = (M_ov * Real.log N) *
          ∑ n ∈ Icc 1 N, ∑ j ∈ nearRowIndices c N n, |f n| * |f j| := by
        simp only [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (near_pair_abs_product_le_row_square c N f)
        (mul_nonneg hM_ov.le hL0.le)
  have hrows : (∑ n ∈ Icc 1 N, ((nearRowIndices c N n).card : ℝ) * f n ^ 2) ≤
      (2 * linearNearRowRadius c) * ∑ n ∈ Icc 1 N, ((n : ℝ) / N) * f n ^ 2 := by
    rw [mul_sum]
    exact sum_le_sum fun n hn =>
      (mul_le_mul_of_nonneg_right (card_nearRowIndices_le_relative_radius hc0 hn hw)
        (sq_nonneg _)).trans_eq (by ring)
  have hmoment := sum_linear_moment_sq_le_four_div_log_of_four_log hR hR4 hlog hu
  calc
    _ ≤ (M_ov * Real.log N) *
        ((2 * linearNearRowRadius c) * ∑ n ∈ Icc 1 N, ((n : ℝ) / N) * f n ^ 2) :=
      hpairing.trans (mul_le_mul_of_nonneg_left hrows (mul_nonneg hM_ov.le hL0.le))
    _ = (2 * linearNearRowRadius c * M_ov) *
        (Real.log N * ∑ n ∈ Icc 1 N, ((n : ℝ) / N) * f n ^ 2) := by ring
    _ ≤ (2 * linearNearRowRadius c * M_ov) * (4 * ‖u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hmoment (by unfold linearNearRowRadius; positivity)
    _ = _ := by unfold linearNearRowRadius; ring

/-- The linear overlap bound in the range `18 (1 + log R) ≤ log N`. -/
theorem exists_overlapMatrix_self_inner_le_linear {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {R N : ℕ} {c : ℝ},
      2 ≤ R → R ^ 4 ≤ N → 18 * (1 + Real.log R) ≤ Real.log N →
      1 ≤ c → c ≤ Real.log N → c / N ≤ 1 / 3 →
      ∀ {u : EuclideanSpace ℝ (PrimeHorizonIndex N)}, u ∈ conductorSubspace R N →
        |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u, u⟫| ≤ C * c * ‖u‖ ^ 2 := by
  obtain ⟨C, hC, h⟩ := exists_overlapMatrix_self_inner_le_linear_of_four_log hφ hsupp hM
  exact ⟨C, hC, fun hR hR4 hlog hc1 hcL hw1 _ hu =>
    h hR hR4 (four_log_add_eighteen_le_of_log_le hlog) hc1 hcL hw1 hu⟩

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
