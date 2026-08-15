import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareInghamCriticalMoment
import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareFourthMomentPolylog

/-! # Polylogarithmic critical moments for Ingham's detector -/

noncomputable section

open Complex Set MeasureTheory

namespace RHTower.Sieve

theorem exists_inghamCriticalZetaFourthMoment_dyadic_le_polylog :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 4 ≤ N →
      inghamCriticalZetaFourthMoment (N : ℝ) (2 * N : ℝ) ≤
        C * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 4 := by
  obtain ⟨C, hC, hbound⟩ :=
    RHTower.exists_integral_Icc_norm_riemannZeta_line_pow_four_le_polylog
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hb := hbound hN
  have heq : inghamCriticalZetaFourthMoment (N : ℝ) (2 * N : ℝ) =
      ∫ t in Set.Icc (N : ℝ) (2 * N : ℝ),
        ‖riemannZeta (RHTower.linePt t)‖ ^ (4 : ℕ) := by
    unfold inghamCriticalZetaFourthMoment
    apply integral_congr_ae
    filter_upwards with t
    rw [inghamCriticalPoint_eq_linePt]
    exact Real.rpow_natCast _ 4
  rw [heq]
  exact hb

theorem exists_inghamCriticalMollifierSecondMoment_dyadic_le_polylog :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 4 ≤ N →
      inghamCriticalMollifierSecondMoment N (N : ℝ) (2 * N : ℝ) ≤
        C * (N : ℝ) * (1 + Real.log (N : ℝ)) := by
  let C : ℝ := 5 * Real.pi * Real.exp 1 + 5 * Real.pi
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N hN
  let L : ℝ := 1 + Real.log (N : ℝ)
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL1 : 1 ≤ L := by
    dsimp only [L]
    linarith [Real.log_nonneg hN1]
  have hbase := inghamCriticalMollifierSecondMoment_le N
    (U := (N : ℝ)) (V := 2 * (N : ℝ)) (by positivity) (by linarith)
  change inghamCriticalMollifierSecondMoment N (N : ℝ) (2 * N : ℝ) ≤
    C * (N : ℝ) * L
  calc
    inghamCriticalMollifierSecondMoment N (N : ℝ) (2 * N : ℝ) ≤
        5 * Real.pi * Real.exp 1 * (N : ℝ) +
          (5 * Real.pi / 2) * L * (2 * (N : ℝ)) := hbase
    _ ≤ 5 * Real.pi * Real.exp 1 * ((N : ℝ) * L) +
          (5 * Real.pi / 2) * L * (2 * (N : ℝ)) := by
      gcongr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hL1 hN0
    _ = C * (N : ℝ) * L := by
      dsimp only [C]
      ring

theorem exists_inghamCriticalErrorFourThirdMoment_dyadic_le_polylog :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 4 ≤ N →
      inghamCriticalErrorFourThirdMoment N (N : ℝ) (2 * N : ℝ) ≤
        C * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 2 := by
  obtain ⟨CZ, hCZ, hZbound⟩ :=
    exists_inghamCriticalZetaFourthMoment_dyadic_le_polylog
  obtain ⟨CM, hCM, hMbound⟩ :=
    exists_inghamCriticalMollifierSecondMoment_dyadic_le_polylog
  let A : ℝ := (2 : ℝ) ^ (1 / 3 : ℝ)
  let C : ℝ := A * CZ ^ (1 / 3 : ℝ) * CM ^ (2 / 3 : ℝ) + A
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N hN
  let L : ℝ := 1 + Real.log (N : ℝ)
  have hNpos : 0 < N := by omega
  have hNR0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNRnonneg : (0 : ℝ) ≤ N := hNR0.le
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL1 : 1 ≤ L := by
    dsimp only [L]
    linarith [Real.log_nonneg hN1]
  have hL0 : 0 ≤ L := by positivity
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hbase := inghamCriticalErrorFourThirdMoment_le N
    (U := (N : ℝ)) (V := 2 * (N : ℝ)) (by linarith)
  have hZb := hZbound hN
  have hMb := hMbound hN
  have hZ0 : 0 ≤ inghamCriticalZetaFourthMoment (N : ℝ) (2 * N : ℝ) := by
    unfold inghamCriticalZetaFourthMoment
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun _ _ =>
      Real.rpow_nonneg (norm_nonneg _) _
  have hM0 : 0 ≤ inghamCriticalMollifierSecondMoment N (N : ℝ) (2 * N : ℝ) := by
    unfold inghamCriticalMollifierSecondMoment
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun _ _ =>
      Real.rpow_nonneg (norm_nonneg _) _
  have hZpow :
      (inghamCriticalZetaFourthMoment (N : ℝ) (2 * N : ℝ)) ^ (1 / 3 : ℝ) ≤
        CZ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) * L ^ (4 / 3 : ℝ) := by
    calc
      (inghamCriticalZetaFourthMoment (N : ℝ) (2 * N : ℝ)) ^ (1 / 3 : ℝ) ≤
          (CZ * (N : ℝ) * L ^ 4) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow hZ0 hZb (by norm_num)
      _ = CZ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) *
          L ^ (4 / 3 : ℝ) := by
        rw [Real.mul_rpow (mul_nonneg hCZ hNRnonneg) (pow_nonneg hL0 4),
          Real.mul_rpow hCZ hNRnonneg, ← Real.rpow_natCast L 4,
          ← Real.rpow_mul hL0]
        norm_num
  have hMpow :
      (inghamCriticalMollifierSecondMoment N (N : ℝ) (2 * N : ℝ)) ^ (2 / 3 : ℝ) ≤
        CM ^ (2 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) * L ^ (2 / 3 : ℝ) := by
    calc
      (inghamCriticalMollifierSecondMoment N (N : ℝ) (2 * N : ℝ)) ^ (2 / 3 : ℝ) ≤
          (CM * (N : ℝ) * L) ^ (2 / 3 : ℝ) :=
        Real.rpow_le_rpow hM0 hMb (by norm_num)
      _ = CM ^ (2 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) *
          L ^ (2 / 3 : ℝ) := by
        rw [Real.mul_rpow (mul_nonneg hCM hNRnonneg) hL0,
          Real.mul_rpow hCM hNRnonneg]
  have hmulN :
      (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) = (N : ℝ) := by
    rw [← Real.rpow_add hNR0]
    norm_num
  have hmulL :
      L ^ (4 / 3 : ℝ) * L ^ (2 / 3 : ℝ) = L ^ 2 := by
    rw [← Real.rpow_add hLpos]
    norm_num
  have hfirstFactor :
      A * (inghamCriticalZetaFourthMoment (N : ℝ) (2 * N : ℝ)) ^ (1 / 3 : ℝ) ≤
        A * (CZ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) *
          L ^ (4 / 3 : ℝ)) :=
    mul_le_mul_of_nonneg_left hZpow hA
  have hfirstFactorNonneg : 0 ≤
      A * (CZ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) *
        L ^ (4 / 3 : ℝ)) := by positivity
  have hmainProduct :
      A * (inghamCriticalZetaFourthMoment (N : ℝ) (2 * N : ℝ)) ^ (1 / 3 : ℝ) *
          (inghamCriticalMollifierSecondMoment N (N : ℝ) (2 * N : ℝ)) ^ (2 / 3 : ℝ) ≤
        A * (CZ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) *
          L ^ (4 / 3 : ℝ)) *
          (CM ^ (2 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) *
            L ^ (2 / 3 : ℝ)) :=
    mul_le_mul hfirstFactor hMpow
      (Real.rpow_nonneg hM0 _) hfirstFactorNonneg
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
  have hlast : A * (N : ℝ) ≤ A * (N : ℝ) * L ^ 2 := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hL2 (mul_nonneg hA hNRnonneg)
  change inghamCriticalErrorFourThirdMoment N (N : ℝ) (2 * N : ℝ) ≤
    C * (N : ℝ) * L ^ 2
  calc
    inghamCriticalErrorFourThirdMoment N (N : ℝ) (2 * N : ℝ) ≤
        A * (inghamCriticalZetaFourthMoment (N : ℝ) (2 * N : ℝ)) ^ (1 / 3 : ℝ) *
          (inghamCriticalMollifierSecondMoment N (N : ℝ) (2 * N : ℝ)) ^ (2 / 3 : ℝ) +
        A * ((2 * (N : ℝ)) - (N : ℝ)) := by simpa only [A] using hbase
    _ ≤ A * (CZ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) *
          L ^ (4 / 3 : ℝ)) *
          (CM ^ (2 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) *
            L ^ (2 / 3 : ℝ)) + A * (N : ℝ) := by
      convert add_le_add_right hmainProduct (A * (N : ℝ)) using 1 <;> ring
    _ = (A * CZ ^ (1 / 3 : ℝ) * CM ^ (2 / 3 : ℝ)) *
          ((N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ)) *
          (L ^ (4 / 3 : ℝ) * L ^ (2 / 3 : ℝ)) + A * (N : ℝ) := by ring
    _ = (A * CZ ^ (1 / 3 : ℝ) * CM ^ (2 / 3 : ℝ)) *
          (N : ℝ) * L ^ 2 + A * (N : ℝ) := by rw [hmulN, hmulL]
    _ ≤ (A * CZ ^ (1 / 3 : ℝ) * CM ^ (2 / 3 : ℝ)) *
          (N : ℝ) * L ^ 2 + A * (N : ℝ) * L ^ 2 := by gcongr
    _ = C * (N : ℝ) * L ^ 2 := by
      dsimp only [C]
      ring

end RHTower.Sieve

