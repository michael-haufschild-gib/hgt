import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareFourthMomentRouteTBudget
import GaloisForLFunctions.RHTower.Sieve.InghamMollifierSecondMoment
import GaloisForLFunctions.RHTower.Sieve.InghamRouteTExponentBudget

noncomputable section

open Complex Set MeasureTheory

namespace RHTower.Sieve

theorem inghamCriticalPoint_eq_linePt (t : ℝ) :
    inghamCriticalPoint t = RHTower.linePt t := by
  unfold inghamCriticalPoint RHTower.linePt
  push_cast
  ring

/-- The exact-AFE critical-line fourth moment is the literal fourth moment used by Ingham's
mollified detector. -/
theorem exists_inghamCriticalZetaFourthMoment_dyadic_le_routeTBudget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 4 ≤ N →
      inghamCriticalZetaFourthMoment (N : ℝ) (2 * N : ℝ) ≤
        C * (N : ℝ) ^ (101 / 100 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ :=
    RHTower.exists_integral_Icc_norm_riemannZeta_line_pow_four_le_routeTBudget
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

/-- The logarithmic mollifier loss is absorbed at a fixed exponent much smaller than the
available fourth-moment budget. -/
theorem one_add_log_nat_le_rpow_one_thousandth
    {N : ℕ} (hN : 1 ≤ N) :
    1 + Real.log (N : ℝ) ≤
      1001 * (N : ℝ) ^ (1 / 1000 : ℝ) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : 1 ≤ (N : ℝ) ^ (1 / 1000 : ℝ) :=
    Real.one_le_rpow hNR (by norm_num)
  have hlog := Real.log_le_rpow_div (zero_le_one.trans hNR)
    (by norm_num : (0 : ℝ) < 1 / 1000)
  have hlog' : Real.log (N : ℝ) ≤
      1000 * (N : ℝ) ^ (1 / 1000 : ℝ) := by
    calc
      Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 1000 : ℝ) / (1 / 1000 : ℝ) := hlog
      _ = 1000 * (N : ℝ) ^ (1 / 1000 : ℝ) := by ring
  nlinarith

/-- The actual length-`N` Möbius mollifier has dyadic second moment `O(N^(1001/1000))`. -/
theorem exists_inghamCriticalMollifierSecondMoment_dyadic_le_routeTBudget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 4 ≤ N →
      inghamCriticalMollifierSecondMoment N (N : ℝ) (2 * N : ℝ) ≤
        C * (N : ℝ) ^ (1001 / 1000 : ℝ) := by
  let C : ℝ := 5 * Real.pi * Real.exp 1 + 5 * Real.pi * 1001
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := by omega
  have hNR0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hbase := inghamCriticalMollifierSecondMoment_le N
    (U := (N : ℝ)) (V := 2 * (N : ℝ)) (by positivity) (by linarith)
  have hlog := one_add_log_nat_le_rpow_one_thousandth hN1
  have hpowN : (N : ℝ) ≤ (N : ℝ) ^ (1001 / 1000 : ℝ) := by
    calc
      (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N : ℝ) ^ (1001 / 1000 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hNR1 (by norm_num)
  have hmul : (N : ℝ) ^ (1 / 1000 : ℝ) * (N : ℝ) =
      (N : ℝ) ^ (1001 / 1000 : ℝ) := by
    calc
      (N : ℝ) ^ (1 / 1000 : ℝ) * (N : ℝ) =
          (N : ℝ) ^ (1 / 1000 : ℝ) * (N : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = (N : ℝ) ^ ((1 / 1000 : ℝ) + 1) :=
        (Real.rpow_add hNR0 _ _).symm
      _ = (N : ℝ) ^ (1001 / 1000 : ℝ) := by norm_num
  calc
    inghamCriticalMollifierSecondMoment N (N : ℝ) (2 * N : ℝ) ≤
        5 * Real.pi * Real.exp 1 * (N : ℝ) +
          (5 * Real.pi / 2) * (1 + Real.log (N : ℝ)) * (2 * (N : ℝ)) := hbase
    _ ≤ 5 * Real.pi * Real.exp 1 * (N : ℝ) +
          (5 * Real.pi / 2) *
            (1001 * (N : ℝ) ^ (1 / 1000 : ℝ)) * (2 * (N : ℝ)) := by gcongr
    _ = 5 * Real.pi * Real.exp 1 * (N : ℝ) +
          (5 * Real.pi * 1001) *
            ((N : ℝ) ^ (1 / 1000 : ℝ) * (N : ℝ)) := by ring
    _ ≤ 5 * Real.pi * Real.exp 1 * (N : ℝ) ^ (1001 / 1000 : ℝ) +
          (5 * Real.pi * 1001) *
            (N : ℝ) ^ (1001 / 1000 : ℝ) := by
      rw [hmul]
      gcongr
    _ = C * (N : ℝ) ^ (1001 / 1000 : ℝ) := by
      dsimp only [C]
      ring

/-- Hölder composition of any dyadic zeta fourth-moment and mollifier second-moment bounds with
the precise exponents produced by the exact-AFE and affine-mollifier modules. -/
theorem exists_inghamCriticalErrorFourThirdMoment_dyadic_le_of_bounds
    (CZ CM : ℝ) (hCZ : 0 ≤ CZ) (hCM : 0 ≤ CM)
    (hZbound : ∀ {N : ℕ}, 4 ≤ N →
      inghamCriticalZetaFourthMoment (N : ℝ) (2 * N : ℝ) ≤
        CZ * (N : ℝ) ^ (101 / 100 : ℝ))
    (hMbound : ∀ {N : ℕ}, 4 ≤ N →
      inghamCriticalMollifierSecondMoment N (N : ℝ) (2 * N : ℝ) ≤
        CM * (N : ℝ) ^ (1001 / 1000 : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 4 ≤ N →
      inghamCriticalErrorFourThirdMoment N (N : ℝ) (2 * N : ℝ) ≤
        C * (N : ℝ) ^ (251 / 250 : ℝ) := by
  let A : ℝ := (2 : ℝ) ^ (1 / 3 : ℝ)
  let C : ℝ := A * CZ ^ (1 / 3 : ℝ) * CM ^ (2 / 3 : ℝ) + A
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hNpos : 0 < N := by omega
  have hNR0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
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
        CZ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (101 / 300 : ℝ) := by
    calc
      (inghamCriticalZetaFourthMoment (N : ℝ) (2 * N : ℝ)) ^ (1 / 3 : ℝ) ≤
          (CZ * (N : ℝ) ^ (101 / 100 : ℝ)) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow hZ0 hZb (by norm_num)
      _ = CZ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (101 / 300 : ℝ) := by
        rw [Real.mul_rpow hCZ (Real.rpow_nonneg hNR0.le _),
          ← Real.rpow_mul hNR0.le]
        norm_num
  have hMpow :
      (inghamCriticalMollifierSecondMoment N (N : ℝ) (2 * N : ℝ)) ^ (2 / 3 : ℝ) ≤
        CM ^ (2 / 3 : ℝ) * (N : ℝ) ^ (1001 / 1500 : ℝ) := by
    calc
      (inghamCriticalMollifierSecondMoment N (N : ℝ) (2 * N : ℝ)) ^ (2 / 3 : ℝ) ≤
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
      A * (inghamCriticalZetaFourthMoment (N : ℝ) (2 * N : ℝ)) ^ (1 / 3 : ℝ) ≤
        A * (CZ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (101 / 300 : ℝ)) :=
    mul_le_mul_of_nonneg_left hZpow hA
  have hfirstFactorNonneg :
      0 ≤ A * (CZ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (101 / 300 : ℝ)) := by
    positivity
  have hmainProduct :
      A * (inghamCriticalZetaFourthMoment (N : ℝ) (2 * N : ℝ)) ^ (1 / 3 : ℝ) *
          (inghamCriticalMollifierSecondMoment N (N : ℝ) (2 * N : ℝ)) ^ (2 / 3 : ℝ) ≤
        A * (CZ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (101 / 300 : ℝ)) *
          (CM ^ (2 / 3 : ℝ) * (N : ℝ) ^ (1001 / 1500 : ℝ)) :=
    mul_le_mul hfirstFactor hMpow
      (Real.rpow_nonneg hM0 _) hfirstFactorNonneg
  have hlast : A * (N : ℝ) ≤ A * (N : ℝ) ^ (251 / 250 : ℝ) :=
    mul_le_mul_of_nonneg_left hNpow hA
  calc
    inghamCriticalErrorFourThirdMoment N (N : ℝ) (2 * N : ℝ) ≤
        A * (inghamCriticalZetaFourthMoment (N : ℝ) (2 * N : ℝ)) ^ (1 / 3 : ℝ) *
          (inghamCriticalMollifierSecondMoment N (N : ℝ) (2 * N : ℝ)) ^ (2 / 3 : ℝ) +
        A * ((2 * (N : ℝ)) - (N : ℝ)) := by simpa only [A] using hbase
    _ ≤ A * (CZ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (101 / 300 : ℝ)) *
          (CM ^ (2 / 3 : ℝ) * (N : ℝ) ^ (1001 / 1500 : ℝ)) +
        A * (N : ℝ) := by
      convert add_le_add_right hmainProduct (A * (N : ℝ)) using 1 <;> ring
    _ = (A * CZ ^ (1 / 3 : ℝ) * CM ^ (2 / 3 : ℝ)) *
          (N : ℝ) ^ (251 / 250 : ℝ) + A * (N : ℝ) := by
      rw [← hmulPow]
      ring
    _ ≤ (A * CZ ^ (1 / 3 : ℝ) * CM ^ (2 / 3 : ℝ)) *
          (N : ℝ) ^ (251 / 250 : ℝ) +
        A * (N : ℝ) ^ (251 / 250 : ℝ) := by
      simpa only [add_comm] using
        add_le_add_left hlast
          ((A * CZ ^ (1 / 3 : ℝ) * CM ^ (2 / 3 : ℝ)) *
            (N : ℝ) ^ (251 / 250 : ℝ))
    _ = C * (N : ℝ) ^ (251 / 250 : ℝ) := by
      dsimp only [C]
      ring

/-- Complete unconditional dyadic `4/3` moment bound for Ingham's literal mollified zeta error. -/
theorem exists_inghamCriticalErrorFourThirdMoment_dyadic_le_routeTBudget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 4 ≤ N →
      inghamCriticalErrorFourThirdMoment N (N : ℝ) (2 * N : ℝ) ≤
        C * (N : ℝ) ^ (251 / 250 : ℝ) := by
  obtain ⟨CZ, hCZ, hZbound⟩ :=
    exists_inghamCriticalZetaFourthMoment_dyadic_le_routeTBudget
  obtain ⟨CM, hCM, hMbound⟩ :=
    exists_inghamCriticalMollifierSecondMoment_dyadic_le_routeTBudget
  exact exists_inghamCriticalErrorFourThirdMoment_dyadic_le_of_bounds
    CZ CM hCZ hCM hZbound hMbound

/-- The fully absorbed critical detector loss remains inside Route T's `7/10` Gabriel budget. -/
theorem inghamRouteTHeightExponent_three_twoHundredFiftieths_oneThousandth :
    inghamRouteTHeightExponent (3 / 250 : ℝ) (1 / 1000 : ℝ) < 7 / 10 := by
  rw [inghamRouteTHeightExponent_lt_seven_tenths_iff (by norm_num)]
  unfold inghamRouteTZetaMomentLossBudget
  norm_num

end RHTower.Sieve
