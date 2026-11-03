import GaloisForLFunctions.ArithmeticCouplingTheory.TheCompleteFormAtEveryOverlap
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheNearAtomsHaveALogarithmicPairing
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCenterCollarIsPaidByTheTopAtoms
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.SmallWidthKeepsPrimeGeometryPolynomial

/-!
# Near-overlap energy retains the ordinary horizon moment

Near pairs lie above `N/(2e²c)`. A bounded near kernel therefore costs its
bound times `O(c²/N) Σ F(n)²` on the packet `F(n)/√n`. This keeps the ordinary
moment available when the harmonic norm alone loses the terminal saving.
-/

noncomputable section

open Finset MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticCouplingTheory

open RenormalizedArithmeticPotentialTheory CriticalArithmeticCorrelationTheory
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics HTGeometry
  RenormalizedArithmeticPotentialTheory.CompletedShell

private theorem near_mem_symm {c : ℝ} {N n j : ℕ}
    (hn : n ∈ Icc 1 N) (hj : j ∈ Icc 1 N) :
    j ∈ nearRowIndices c N n ↔ n ∈ nearRowIndices c N j := by
  simp only [nearRowIndices, mem_filter, hn, hj, true_and, ne_comm, abs_sub_comm]

/-- A near kernel is controlled by the ordinary square of packet amplitudes. -/
theorem abs_near_packet_form_le {c M : ℝ} {N : ℕ}
    (hc : 0 < c) (hN : 1 ≤ N) (hw : c / N ≤ 1) (hM : 0 ≤ M)
    (K : ℕ → ℕ → ℝ)
    (hK : ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n, |K n j| ≤ M)
    (F : ℕ → ℝ) :
    |∑ n ∈ Icc 1 N, ∑ j ∈ nearRowIndices c N n,
      (F n / Real.sqrt n) * (F j / Real.sqrt j) * K n j| ≤
      (2 * linearNearRowRadius c ^ 2 * M / N) * ∑ n ∈ Icc 1 N, F n ^ 2 := by
  let U : ℕ → ℕ → ℝ := fun n j => if j ∈ nearRowIndices c N n then M else 0
  let x : ℕ → ℝ := fun n => |F n / Real.sqrt n|
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
  have hU0 (n j : ℕ) : 0 ≤ U n j := by dsimp only [U]; split_ifs <;> positivity
  have hUsym (n : ℕ) (hn : n ∈ Icc 1 N) (j : ℕ) (hj : j ∈ Icc 1 N) :
      U n j = U j n := by simp only [U, near_mem_symm hn hj]
  have hcard (n : ℕ) (hn : n ∈ Icc 1 N) :
      ((nearRowIndices c N n).card : ℝ) ≤
        2 * linearNearRowRadius c ^ 2 * (n : ℝ) / N := by
    by_cases he : (nearRowIndices c N n).Nonempty
    · obtain ⟨j, hj⟩ := he
      have hgeom := (nearRow_geometry_small_width hc hn hj hw).2.1
      have hscale : 1 ≤ linearNearRowRadius c * (n : ℝ) / N := by
        rw [le_div_iff₀ hN0, one_mul]
        exact hgeom
      have hmul := mul_le_mul_of_nonneg_left hscale (mul_nonneg zero_le_two hr)
      rw [mul_one] at hmul
      exact (card_nearRowIndices_le_small_width hc hn hw).trans
        (hmul.trans_eq (by ring))
    · rw [not_nonempty_iff_eq_empty.mp he, card_empty, Nat.cast_zero]
      positivity
  have hrow (n : ℕ) (hn : n ∈ Icc 1 N) :
      (∑ j ∈ Icc 1 N, U n j) ≤ 2 * linearNearRowRadius c ^ 2 * M * n / N := by
    have heq : (∑ j ∈ Icc 1 N, U n j) = ((nearRowIndices c N n).card : ℝ) * M := by
      dsimp only [U]
      rw [← sum_filter]
      have hf : (Icc 1 N).filter (fun j => j ∈ nearRowIndices c N n) =
          nearRowIndices c N n := by
        ext j
        simp only [mem_filter, nearRowIndices, and_self_left]
      rw [hf, sum_const, nsmul_eq_mul]
    rw [heq]
    exact (mul_le_mul_of_nonneg_right (hcard n hn) hM).trans_eq (by ring)
  have hschur := finite_weighted_schur_row_potential (Icc 1 N) x (fun _ => 1) U
    (fun _ _ => zero_lt_one) (fun n _ j _ => hU0 n j) hUsym
  simp only [div_one, mul_one] at hschur
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ∑ j ∈ nearRowIndices c N n,
        |(F n / Real.sqrt n) * (F j / Real.sqrt j) * K n j| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun _ _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ n ∈ Icc 1 N, ∑ j ∈ nearRowIndices c N n, x n * x j * M := by
      apply sum_le_sum
      intro n hn
      apply sum_le_sum
      intro j hj
      simp only [abs_mul]
      exact mul_le_mul_of_nonneg_left (hK n hn j hj) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, x n * x j * U n j := by
      apply sum_congr rfl
      intro n _
      rw [nearRowIndices, sum_filter]
      apply sum_congr rfl
      intro j hj
      simp only [U, nearRowIndices, mem_filter, hj, true_and, mul_ite, mul_zero]
    _ ≤ ∑ n ∈ Icc 1 N, x n ^ 2 * (∑ j ∈ Icc 1 N, U n j) := hschur
    _ ≤ ∑ n ∈ Icc 1 N,
        x n ^ 2 * (2 * linearNearRowRadius c ^ 2 * M * n / N) :=
      sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hrow n hn) (sq_nonneg _)
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (mem_Icc.mp hn).1
      simp only [x, sq_abs, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      field_simp [hn0]

private theorem center_entry_le_log {N n j : ℕ}
    (hn : n ∈ Icc 1 N) (hj : j ∈ Icc 1 N) :
    archimedeanCenterKernel n j ≤ (N : ℝ) * (Real.log N + 2) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
  have hsingle := single_le_sum (f := fun k : ℕ => archimedeanCenterKernel n k / Real.sqrt k)
    (fun k _ => div_nonneg (archimedeanCenterKernel_nonneg _ _) (Real.sqrt_nonneg _)) hj
  have hrow := hsingle.trans (sum_archimedeanCenterKernel_div_sqrt_le hn)
  have hH := harmonic_le_one_add_log N
  have hpoint : archimedeanCenterKernel n j ≤
      Real.sqrt n * Real.sqrt j * (Real.log N + 2) := by
    have hmul := (div_le_iff₀ (Real.sqrt_pos.mpr hj0)).mp hrow
    have hlog := mul_le_mul_of_nonneg_left hH
      (mul_nonneg (Real.sqrt_nonneg (n : ℝ)) (Real.sqrt_nonneg (j : ℝ)))
    nlinarith only [hmul, hlog]
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
  have hjN : (j : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hj).2
  have hprod := mul_le_mul (Real.sqrt_le_sqrt hnN) (Real.sqrt_le_sqrt hjN)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [Real.mul_self_sqrt (Nat.cast_nonneg N)] at hprod
  exact hpoint.trans (mul_le_mul_of_nonneg_right hprod
    (by linarith only [Real.log_natCast_nonneg N]))

private theorem overlap_packet_eq (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (F : ℕ → ℝ) :
    ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) (packetVector F N), packetVector F N⟫ =
      ∑ n ∈ Icc 1 N, ∑ j ∈ nearRowIndices c N n,
        (F n / Real.sqrt n) * (F j / Real.sqrt j) *
          (atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2) +
            (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j) := by
  change ⟪Matrix.toEuclideanLin (horizonKernelMatrix
    (fun n j => if n ≠ j ∧ |Real.log j - Real.log n| ≤ 2 * (c / N) then
      atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2) +
        (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j else 0) N)
      (packetVector F N), packetVector F N⟫ = _
  rw [horizonKernelMatrix_inner]
  have hext (n : ℕ) (hn : n ∈ Icc 1 N) :
      primeHorizonExtension (packetVector F N) n = F n / Real.sqrt n := by
    simp only [primeHorizonExtension, hn]
    rfl
  apply sum_congr rfl
  intro n hn
  rw [nearRowIndices, sum_filter]
  apply sum_congr rfl
  intro j hj
  rw [hext n hn, hext j hj]
  simp only [mul_ite, mul_zero, ne_comm, mul_div_assoc]

/-- The actual overlap matrix costs a terminal ordinary moment, including its center correction. -/
theorem exists_abs_overlap_packet_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℝ) (N : ℕ), 1 ≤ c → 1 ≤ N → c / N ≤ 1 / 3 →
      ∀ F : ℕ → ℝ,
      |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) (packetVector F N), packetVector F N⟫| ≤
        (2 * linearNearRowRadius c ^ 2 *
          (Real.log N + C + c * (Real.log N + 2)) / N) * ∑ n ∈ Icc 1 N, F n ^ 2 := by
  obtain ⟨C, hC, hpair⟩ := exists_abs_atomArchPair_near_sub_le hφ hsupp hM
  refine ⟨C, hC, ?_⟩
  intro c N hc hN hw F
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw0 : 0 < c / N := div_pos hc0 hN0
  have hL0 : 0 ≤ Real.log (1 / (c / N)) :=
    Real.log_nonneg ((le_div_iff₀ hw0).2 (by linarith only [hw]))
  have hLN : Real.log (1 / (c / N)) ≤ Real.log N := by
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ hw0]
    have hcancel : (N : ℝ) * (c / N) = c := by
      rw [mul_comm, div_mul_cancel₀ _ hN0.ne']
    simpa only [hcancel] using hc
  rw [overlap_packet_eq]
  apply abs_near_packet_form_le hc0 hN (by linarith only [hw])
    (by positivity)
  intro n hn j hj
  have hjN := (mem_filter.mp hj).1
  have hnear : |Real.log j - Real.log n| ≤ 2 * (c / N) := by
    simpa only [mul_div_assoc] using (mem_filter.mp hj).2.2
  have hcorr : |shellAutocorr φ (|Real.log j - Real.log n| / (c / N))| ≤ ∫ u, φ u ^ 2 :=
    abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp) _
  have hmain : |Real.log (1 / (c / N)) *
      shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)| ≤
        Real.log N := by
    rw [abs_div, abs_mul, abs_of_nonneg hL0, abs_of_pos hM]
    apply le_trans _ hLN
    rw [div_le_iff₀ hM]
    exact mul_le_mul_of_nonneg_left hcorr hL0
  have harch : |atomArchPair (atomDilate φ (c / N)) n j /
      (∫ u, atomDilate φ (c / N) u ^ 2)| ≤ Real.log N + C := by
    have h := hpair (c / N) hw0 hw n j hnear
    have ht := abs_add_le
      (atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2) -
        Real.log (1 / (c / N)) * shellAutocorr φ
          (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2))
      (Real.log (1 / (c / N)) * shellAutocorr φ
        (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2))
    rw [sub_add_cancel] at ht
    linarith only [ht, h, hmain]
  have hshift0 := completeWeilPoleShift_nonneg φ hc0.le
  have hshift := completeWeilPoleShift_le hφ.continuous hsupp hM hc0.le
  have hcenter : |(completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j| ≤
      c * (Real.log N + 2) := by
    rw [abs_of_nonneg (mul_nonneg (div_nonneg hshift0 hN0.le)
      (archimedeanCenterKernel_nonneg n j))]
    calc
      _ ≤ (c / N) * ((N : ℝ) * (Real.log N + 2)) :=
        mul_le_mul (div_le_div_of_nonneg_right hshift hN0.le)
          (center_entry_le_log hn hjN) (archimedeanCenterKernel_nonneg n j)
          (div_nonneg hc0.le hN0.le)
      _ = _ := by field_simp
  exact (abs_add_le _ _).trans (add_le_add harch hcenter)

#print axioms abs_near_packet_form_le
#print axioms exists_abs_overlap_packet_le

end GaloisForLFunctions.ArithmeticCouplingTheory
