import GaloisForLFunctions.RHTower.Sieve.InghamCriticalGlobalMoment

noncomputable section

open Complex Set MeasureTheory

namespace RHTower.Sieve

theorem exists_inghamCriticalMollifierSecondMoment_symmetric_nat_le_routeTBudget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X N : ℕ}, 4 ≤ X → X ≤ N →
      inghamCriticalMollifierSecondMoment X (-(N : ℝ)) (N : ℝ) ≤
        C * (N : ℝ) ^ (1001 / 1000 : ℝ) := by
  let C : ℝ := 5 * Real.pi * Real.exp 1 + (5 * Real.pi / 2) * 1001
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro X N hX hXN
  have hX1 : 1 ≤ X := by omega
  have hN1 : 1 ≤ N := hX1.trans hXN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hXNR : (X : ℝ) ≤ N := by exact_mod_cast hXN
  have hbase := integral_Icc_normSq_inghamMollifier_critical_le X
    (T := (N : ℝ)) hNR1
  have hbase' :
      inghamCriticalMollifierSecondMoment X (-(N : ℝ)) (N : ℝ) ≤
        5 * Real.pi * Real.exp 1 * X +
          (5 * Real.pi / 2) * (1 + Real.log X) * N := by
    unfold inghamCriticalMollifierSecondMoment
    simpa only [Real.rpow_two] using hbase
  have hlogX := one_add_log_nat_le_rpow_one_thousandth hX1
  have hrpowXN : (X : ℝ) ^ (1 / 1000 : ℝ) ≤
      (N : ℝ) ^ (1 / 1000 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hXNR (by norm_num)
  have hlog : 1 + Real.log (X : ℝ) ≤
      1001 * (N : ℝ) ^ (1 / 1000 : ℝ) :=
    hlogX.trans (mul_le_mul_of_nonneg_left hrpowXN (by norm_num))
  have hNpow : (N : ℝ) ≤ (N : ℝ) ^ (1001 / 1000 : ℝ) := by
    calc
      (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N : ℝ) ^ (1001 / 1000 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hNR1 (by norm_num)
  have hXpow : (X : ℝ) ≤ (N : ℝ) ^ (1001 / 1000 : ℝ) :=
    hXNR.trans hNpow
  have hmul : (N : ℝ) ^ (1 / 1000 : ℝ) * (N : ℝ) =
      (N : ℝ) ^ (1001 / 1000 : ℝ) := by
    calc
      (N : ℝ) ^ (1 / 1000 : ℝ) * (N : ℝ) =
          (N : ℝ) ^ (1 / 1000 : ℝ) * (N : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = (N : ℝ) ^ ((1 / 1000 : ℝ) + 1) :=
        (Real.rpow_add hNpos _ _).symm
      _ = (N : ℝ) ^ (1001 / 1000 : ℝ) := by norm_num
  calc
    inghamCriticalMollifierSecondMoment X (-(N : ℝ)) (N : ℝ) ≤
        5 * Real.pi * Real.exp 1 * X +
          (5 * Real.pi / 2) * (1 + Real.log X) * N := hbase'
    _ ≤ 5 * Real.pi * Real.exp 1 * X +
          (5 * Real.pi / 2) *
            (1001 * (N : ℝ) ^ (1 / 1000 : ℝ)) * N := by gcongr
    _ = 5 * Real.pi * Real.exp 1 * X +
          ((5 * Real.pi / 2) * 1001) *
            ((N : ℝ) ^ (1 / 1000 : ℝ) * N) := by ring
    _ ≤ 5 * Real.pi * Real.exp 1 * (N : ℝ) ^ (1001 / 1000 : ℝ) +
          ((5 * Real.pi / 2) * 1001) *
            (N : ℝ) ^ (1001 / 1000 : ℝ) := by
      rw [hmul]
      gcongr
    _ = C * (N : ℝ) ^ (1001 / 1000 : ℝ) := by
      dsimp only [C]
      ring

theorem exists_inghamCriticalErrorFourThirdMoment_symmetric_nat_le_routeTBudget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X N : ℕ}, 4 ≤ X → X ≤ N →
      inghamCriticalErrorFourThirdMoment X (-(N : ℝ)) (N : ℝ) ≤
        C * (N : ℝ) ^ (251 / 250 : ℝ) := by
  obtain ⟨CZ, hCZ, hZbound⟩ :=
    exists_inghamCriticalZetaFourthMoment_symmetric_nat_le_routeTBudget
  obtain ⟨CM, hCM, hMbound⟩ :=
    exists_inghamCriticalMollifierSecondMoment_symmetric_nat_le_routeTBudget
  let A : ℝ := (2 : ℝ) ^ (1 / 3 : ℝ)
  let C : ℝ := A * CZ ^ (1 / 3 : ℝ) * CM ^ (2 / 3 : ℝ) + 2 * A
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro X N hX hXN
  have hN4 : 4 ≤ N := hX.trans hXN
  have hNpos : 0 < N := by omega
  have hNR0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hbase := inghamCriticalErrorFourThirdMoment_le X
    (U := -(N : ℝ)) (V := (N : ℝ)) (by linarith)
  have hZb := hZbound hN4
  have hMb := hMbound hX hXN
  have hZ0 : 0 ≤ inghamCriticalZetaFourthMoment (-(N : ℝ)) (N : ℝ) := by
    unfold inghamCriticalZetaFourthMoment
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun _ _ =>
      Real.rpow_nonneg (norm_nonneg _) _
  have hM0 : 0 ≤ inghamCriticalMollifierSecondMoment X (-(N : ℝ)) (N : ℝ) := by
    unfold inghamCriticalMollifierSecondMoment
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun _ _ =>
      Real.rpow_nonneg (norm_nonneg _) _
  have hZpow :
      (inghamCriticalZetaFourthMoment (-(N : ℝ)) (N : ℝ)) ^ (1 / 3 : ℝ) ≤
        CZ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (101 / 300 : ℝ) := by
    calc
      (inghamCriticalZetaFourthMoment (-(N : ℝ)) (N : ℝ)) ^ (1 / 3 : ℝ) ≤
          (CZ * (N : ℝ) ^ (101 / 100 : ℝ)) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow hZ0 hZb (by norm_num)
      _ = CZ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (101 / 300 : ℝ) := by
        rw [Real.mul_rpow hCZ (Real.rpow_nonneg hNR0.le _),
          ← Real.rpow_mul hNR0.le]
        norm_num
  have hMpow :
      (inghamCriticalMollifierSecondMoment X (-(N : ℝ)) (N : ℝ)) ^ (2 / 3 : ℝ) ≤
        CM ^ (2 / 3 : ℝ) * (N : ℝ) ^ (1001 / 1500 : ℝ) := by
    calc
      (inghamCriticalMollifierSecondMoment X (-(N : ℝ)) (N : ℝ)) ^ (2 / 3 : ℝ) ≤
          (CM * (N : ℝ) ^ (1001 / 1000 : ℝ)) ^ (2 / 3 : ℝ) :=
        Real.rpow_le_rpow hM0 hMb (by norm_num)
      _ = CM ^ (2 / 3 : ℝ) * (N : ℝ) ^ (1001 / 1500 : ℝ) := by
        rw [Real.mul_rpow hCM (Real.rpow_nonneg hNR0.le _),
          ← Real.rpow_mul hNR0.le]
        norm_num
  have hmulPow :
      (N : ℝ) ^ (101 / 300 : ℝ) * (N : ℝ) ^ (1001 / 1500 : ℝ) =
        (N : ℝ) ^ (251 / 250 : ℝ) := by
    rw [← Real.rpow_add hNR0]
    norm_num
  have hNpow : (N : ℝ) ≤ (N : ℝ) ^ (251 / 250 : ℝ) := by
    calc
      (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N : ℝ) ^ (251 / 250 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hNR1 (by norm_num)
  have hfirstFactor :
      A * (inghamCriticalZetaFourthMoment (-(N : ℝ)) (N : ℝ)) ^ (1 / 3 : ℝ) ≤
        A * (CZ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (101 / 300 : ℝ)) :=
    mul_le_mul_of_nonneg_left hZpow hA
  have hfirstFactorNonneg :
      0 ≤ A * (CZ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (101 / 300 : ℝ)) := by
    positivity
  have hmainProduct :
      A * (inghamCriticalZetaFourthMoment (-(N : ℝ)) (N : ℝ)) ^ (1 / 3 : ℝ) *
          (inghamCriticalMollifierSecondMoment X (-(N : ℝ)) (N : ℝ)) ^ (2 / 3 : ℝ) ≤
        A * (CZ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (101 / 300 : ℝ)) *
          (CM ^ (2 / 3 : ℝ) * (N : ℝ) ^ (1001 / 1500 : ℝ)) :=
    mul_le_mul hfirstFactor hMpow
      (Real.rpow_nonneg hM0 _) hfirstFactorNonneg
  have hlast : 2 * A * (N : ℝ) ≤
      2 * A * (N : ℝ) ^ (251 / 250 : ℝ) :=
    mul_le_mul_of_nonneg_left hNpow (by positivity)
  calc
    inghamCriticalErrorFourThirdMoment X (-(N : ℝ)) (N : ℝ) ≤
        A * (inghamCriticalZetaFourthMoment (-(N : ℝ)) (N : ℝ)) ^ (1 / 3 : ℝ) *
          (inghamCriticalMollifierSecondMoment X (-(N : ℝ)) (N : ℝ)) ^ (2 / 3 : ℝ) +
        A * ((N : ℝ) - (-(N : ℝ))) := by simpa only [A] using hbase
    _ ≤ A * (CZ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (101 / 300 : ℝ)) *
          (CM ^ (2 / 3 : ℝ) * (N : ℝ) ^ (1001 / 1500 : ℝ)) +
        2 * A * (N : ℝ) := by
      convert add_le_add_right hmainProduct (2 * A * (N : ℝ)) using 1 <;> ring
    _ = (A * CZ ^ (1 / 3 : ℝ) * CM ^ (2 / 3 : ℝ)) *
          (N : ℝ) ^ (251 / 250 : ℝ) + 2 * A * (N : ℝ) := by
      rw [← hmulPow]
      ring
    _ ≤ (A * CZ ^ (1 / 3 : ℝ) * CM ^ (2 / 3 : ℝ)) *
          (N : ℝ) ^ (251 / 250 : ℝ) +
        2 * A * (N : ℝ) ^ (251 / 250 : ℝ) := by
      simpa only [add_comm] using
        add_le_add_left hlast
          ((A * CZ ^ (1 / 3 : ℝ) * CM ^ (2 / 3 : ℝ)) *
            (N : ℝ) ^ (251 / 250 : ℝ))
    _ = C * (N : ℝ) ^ (251 / 250 : ℝ) := by
      dsimp only [C]
      ring

end RHTower.Sieve
