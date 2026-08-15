import GaloisForLFunctions.RHTower.Sieve.InghamCriticalGlobalErrorMoment
import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareInghamCriticalMomentPolylog

/-! # Global polylogarithmic critical moments for Ingham's detector -/

noncomputable section

open Complex Set MeasureTheory intervalIntegral

namespace RHTower.Sieve

private def polylogCriticalZetaFourthDensity (t : ℝ) : ℝ :=
  ‖riemannZeta (inghamCriticalPoint t)‖ ^ (4 : ℝ)

private theorem continuous_polylogCriticalZetaFourthDensity :
    Continuous polylogCriticalZetaFourthDensity := by
  exact continuous_riemannZeta_inghamCriticalPoint.norm.rpow_const
    (fun _ => Or.inr (by norm_num))

private theorem inghamCriticalZetaFourthMoment_eq_intervalIntegral_polylog
    {a b : ℝ} (hab : a ≤ b) :
    inghamCriticalZetaFourthMoment a b =
      ∫ t in a..b, polylogCriticalZetaFourthDensity t := by
  rw [inghamCriticalZetaFourthMoment,
    intervalIntegral.integral_of_le hab,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rfl

private theorem inghamCriticalZetaFourthMoment_add_adjacent_polylog
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    inghamCriticalZetaFourthMoment a c =
      inghamCriticalZetaFourthMoment a b +
        inghamCriticalZetaFourthMoment b c := by
  rw [inghamCriticalZetaFourthMoment_eq_intervalIntegral_polylog (hab.trans hbc),
    inghamCriticalZetaFourthMoment_eq_intervalIntegral_polylog hab,
    inghamCriticalZetaFourthMoment_eq_intervalIntegral_polylog hbc]
  exact (intervalIntegral.integral_add_adjacent_intervals
    (continuous_polylogCriticalZetaFourthDensity.intervalIntegrable a b)
    (continuous_polylogCriticalZetaFourthDensity.intervalIntegrable b c)).symm

private theorem inghamCriticalZetaFourthMoment_nonneg_polylog {a b : ℝ} :
    0 ≤ inghamCriticalZetaFourthMoment a b := by
  unfold inghamCriticalZetaFourthMoment
  exact setIntegral_nonneg measurableSet_Icc fun _ _ =>
    Real.rpow_nonneg (norm_nonneg _) _

private theorem inghamCriticalZetaFourthMoment_mono_right_polylog
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    inghamCriticalZetaFourthMoment a b ≤
      inghamCriticalZetaFourthMoment a c := by
  rw [inghamCriticalZetaFourthMoment_add_adjacent_polylog hab hbc]
  exact le_add_of_nonneg_right inghamCriticalZetaFourthMoment_nonneg_polylog

private theorem dyadic_initial_inghamCriticalZetaFourthMoment_le_polylog
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ {N : ℕ}, 4 ≤ N →
      inghamCriticalZetaFourthMoment (N : ℝ) (2 * N : ℝ) ≤
        C * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 4) :
    ∀ k : ℕ,
      inghamCriticalZetaFourthMoment 4 (4 * 2 ^ k : ℕ) ≤
        C * ((4 * 2 ^ k : ℕ) : ℝ) *
          (1 + Real.log ((4 * 2 ^ k : ℕ) : ℝ)) ^ 4 := by
  intro k
  induction k with
  | zero =>
      norm_num only [pow_zero, mul_one, Nat.cast_ofNat]
      rw [show inghamCriticalZetaFourthMoment 4 4 = 0 by
        norm_num [inghamCriticalZetaFourthMoment]]
      positivity
  | succ k ih =>
      let N : ℕ := 4 * 2 ^ k
      have hN4 : 4 ≤ N := by
        dsimp only [N]
        have hp : 0 < 2 ^ k := pow_pos (by omega : 0 < (2 : ℕ)) k
        omega
      have hnext : 4 * 2 ^ (k + 1) = 2 * N := by
        dsimp only [N]
        rw [pow_succ]
        ring
      have hsplit := inghamCriticalZetaFourthMoment_add_adjacent_polylog
        (a := (4 : ℝ)) (b := (N : ℝ)) (c := 2 * (N : ℝ))
        (by exact_mod_cast hN4) (by
          have : (0 : ℝ) ≤ N := by positivity
          linarith)
      have hshell := hbound hN4
      have hNpos : (0 : ℝ) < N := by positivity
      have hlog : Real.log (N : ℝ) ≤ Real.log (2 * (N : ℝ)) :=
        Real.log_le_log hNpos (by linarith)
      have hL0 : 0 ≤ 1 + Real.log (N : ℝ) := by
        have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
        linarith [Real.log_nonneg hN1]
      have hLmono : (1 + Real.log (N : ℝ)) ^ 4 ≤
          (1 + Real.log (2 * (N : ℝ))) ^ 4 := by gcongr
      rw [hnext]
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      rw [hsplit]
      calc
        inghamCriticalZetaFourthMoment 4 (N : ℝ) +
              inghamCriticalZetaFourthMoment (N : ℝ) (2 * N : ℝ) ≤
            C * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 4 +
              C * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 4 :=
          add_le_add ih hshell
        _ ≤ C * (2 * (N : ℝ)) *
            (1 + Real.log (2 * (N : ℝ))) ^ 4 := by
          calc
            C * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 4 +
                C * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 4 =
              C * (2 * (N : ℝ)) * (1 + Real.log (N : ℝ)) ^ 4 := by ring
            _ ≤ C * (2 * (N : ℝ)) *
                (1 + Real.log (2 * (N : ℝ))) ^ 4 := by gcongr

private theorem pow_clog_two_lt_two_mul_polylog {N : ℕ} (hN : 1 < N) :
    2 ^ Nat.clog 2 N < 2 * N := by
  have hkpos : 0 < Nat.clog 2 N := Nat.clog_pos (by norm_num) hN
  have hpred := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hN
  rw [← Nat.succ_pred_eq_of_pos hkpos, pow_succ]
  omega

theorem exists_inghamCriticalZetaFourthMoment_initial_nat_le_polylog :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {N : ℕ}, 4 ≤ N →
      inghamCriticalZetaFourthMoment 0 (N : ℝ) ≤
        D * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 4 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_inghamCriticalZetaFourthMoment_dyadic_le_polylog
  let B : ℝ := inghamCriticalZetaFourthMoment 0 4
  let Q : ℝ := 8 * 9 ^ 4
  let D : ℝ := B + C * Q
  have hB : 0 ≤ B := inghamCriticalZetaFourthMoment_nonneg_polylog
  have hD : 0 ≤ D := by dsimp only [D, Q]; positivity
  refine ⟨D, hD, ?_⟩
  intro N hN
  let k : ℕ := Nat.clog 2 N
  let E : ℕ := 4 * 2 ^ k
  have hN1nat : 1 < N := by omega
  have hNpow : N ≤ 2 ^ k := by
    dsimp only [k]
    exact Nat.le_pow_clog (by norm_num) N
  have hEupper : E ≤ 8 * N := by
    have hlt := pow_clog_two_lt_two_mul_polylog hN1nat
    dsimp only [E, k]
    omega
  have hNendpoint : N ≤ E := by
    dsimp only [E]
    exact hNpow.trans (Nat.le_mul_of_pos_left (2 ^ k) (by omega))
  have hmono : inghamCriticalZetaFourthMoment 4 (N : ℝ) ≤
      inghamCriticalZetaFourthMoment 4 (E : ℝ) :=
    inghamCriticalZetaFourthMoment_mono_right_polylog
      (by exact_mod_cast hN) (by exact_mod_cast hNendpoint)
  have hdyadic := dyadic_initial_inghamCriticalZetaFourthMoment_le_polylog
    C hC hbound k
  have hEdef : (4 * 2 ^ k : ℕ) = E := rfl
  rw [hEdef] at hdyadic
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hEpos : (0 : ℝ) < E := by positivity
  have hL1 : 1 ≤ 1 + Real.log (N : ℝ) := by
    linarith [Real.log_nonneg hN1]
  have hlogE : Real.log (E : ℝ) ≤ Real.log (8 * (N : ℝ)) :=
    Real.log_le_log hEpos (by exact_mod_cast hEupper)
  have hlog8 : Real.log (8 : ℝ) ≤ 8 := Real.log_le_self (by norm_num)
  have hlogMul : Real.log (8 * (N : ℝ)) = Real.log 8 + Real.log (N : ℝ) := by
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hNpos.ne']
  have hLscale : 1 + Real.log (E : ℝ) ≤
      9 * (1 + Real.log (N : ℝ)) := by
    rw [hlogMul] at hlogE
    linarith
  have hLE0 : 0 ≤ 1 + Real.log (E : ℝ) := by
    have hE1 : (1 : ℝ) ≤ E := by exact_mod_cast (show 1 ≤ E by omega)
    linarith [Real.log_nonneg hE1]
  have hLscale4 : (1 + Real.log (E : ℝ)) ^ 4 ≤
      (9 * (1 + Real.log (N : ℝ))) ^ 4 := by gcongr
  have hscale : (E : ℝ) * (1 + Real.log (E : ℝ)) ^ 4 ≤
      Q * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 4 := by
    have hEr : (E : ℝ) ≤ 8 * (N : ℝ) := by exact_mod_cast hEupper
    calc
      (E : ℝ) * (1 + Real.log (E : ℝ)) ^ 4 ≤
          (8 * (N : ℝ)) * (9 * (1 + Real.log (N : ℝ))) ^ 4 := by gcongr
      _ = Q * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 4 := by
        dsimp only [Q]
        ring
  have hunit : 1 ≤ (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 4 := by
    have hL4 : 1 ≤ (1 + Real.log (N : ℝ)) ^ 4 := one_le_pow₀ hL1
    nlinarith [show (1 : ℝ) ≤ N from hN1]
  have hBscale : B ≤ B * ((N : ℝ) * (1 + Real.log (N : ℝ)) ^ 4) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hunit hB
  have hCscale : C * ((E : ℝ) * (1 + Real.log (E : ℝ)) ^ 4) ≤
      C * (Q * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 4) :=
    mul_le_mul_of_nonneg_left hscale hC
  rw [inghamCriticalZetaFourthMoment_add_adjacent_polylog (a := 0) (b := 4)
    (c := (N : ℝ)) (by norm_num) (by exact_mod_cast hN)]
  calc
    B + inghamCriticalZetaFourthMoment 4 (N : ℝ) ≤
        B + inghamCriticalZetaFourthMoment 4 (E : ℝ) := by gcongr
    _ ≤ B + C * (E : ℝ) * (1 + Real.log (E : ℝ)) ^ 4 := by gcongr
    _ = B + C * ((E : ℝ) * (1 + Real.log (E : ℝ)) ^ 4) := by ring
    _ ≤ B * ((N : ℝ) * (1 + Real.log (N : ℝ)) ^ 4) +
        C * (Q * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 4) :=
      add_le_add hBscale hCscale
    _ = D * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 4 := by
      dsimp only [D]
      ring

private theorem polylogCriticalZetaFourthDensity_neg (t : ℝ) :
    polylogCriticalZetaFourthDensity (-t) =
      polylogCriticalZetaFourthDensity t := by
  have hpoint : inghamCriticalPoint (-t) =
      starRingEnd ℂ (inghamCriticalPoint t) := by
    apply Complex.ext <;> simp [inghamCriticalPoint]
  rw [polylogCriticalZetaFourthDensity, polylogCriticalZetaFourthDensity, hpoint,
    riemannZeta_conj, Complex.norm_conj]

private theorem inghamCriticalZetaFourthMoment_neg_eq_polylog
    {H : ℝ} (hH : 0 ≤ H) :
    inghamCriticalZetaFourthMoment (-H) 0 =
      inghamCriticalZetaFourthMoment 0 H := by
  rw [inghamCriticalZetaFourthMoment_eq_intervalIntegral_polylog (by linarith),
    inghamCriticalZetaFourthMoment_eq_intervalIntegral_polylog hH]
  calc
    (∫ t in -H..0, polylogCriticalZetaFourthDensity t) =
        ∫ t in 0..H, polylogCriticalZetaFourthDensity (-t) := by
      simpa only [neg_zero] using
        (intervalIntegral.integral_comp_neg polylogCriticalZetaFourthDensity
          (a := 0) (b := H)).symm
    _ = ∫ t in 0..H, polylogCriticalZetaFourthDensity t := by
      apply intervalIntegral.integral_congr
      intro t _
      exact polylogCriticalZetaFourthDensity_neg t

theorem exists_inghamCriticalZetaFourthMoment_symmetric_nat_le_polylog :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {N : ℕ}, 4 ≤ N →
      inghamCriticalZetaFourthMoment (-(N : ℝ)) (N : ℝ) ≤
        D * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 4 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_inghamCriticalZetaFourthMoment_initial_nat_le_polylog
  refine ⟨2 * C, by positivity, ?_⟩
  intro N hN
  have hpos : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hneg : -(N : ℝ) ≤ 0 := neg_nonpos.mpr hpos
  rw [inghamCriticalZetaFourthMoment_add_adjacent_polylog (a := -(N : ℝ))
    (b := 0) (c := (N : ℝ)) hneg hpos,
    inghamCriticalZetaFourthMoment_neg_eq_polylog hpos]
  nlinarith [hbound hN]

theorem exists_inghamCriticalMollifierSecondMoment_symmetric_nat_le_polylog :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X N : ℕ}, 4 ≤ X → X ≤ N →
      inghamCriticalMollifierSecondMoment X (-(N : ℝ)) (N : ℝ) ≤
        C * (N : ℝ) * (1 + Real.log (N : ℝ)) := by
  let C : ℝ := 5 * Real.pi * Real.exp 1 + (5 * Real.pi / 2)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro X N hX hXN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hXNr : (X : ℝ) ≤ N := by exact_mod_cast hXN
  have hlog : Real.log (X : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hXpos hXNr
  have hLN1 : 1 ≤ 1 + Real.log (N : ℝ) := by
    linarith [Real.log_nonneg hN1]
  have hbase := integral_Icc_normSq_inghamMollifier_critical_le X
    (T := (N : ℝ)) hN1
  have hbase' :
      inghamCriticalMollifierSecondMoment X (-(N : ℝ)) (N : ℝ) ≤
        5 * Real.pi * Real.exp 1 * X +
          (5 * Real.pi / 2) * (1 + Real.log X) * N := by
    unfold inghamCriticalMollifierSecondMoment
    simpa only [Real.rpow_two] using hbase
  calc
    inghamCriticalMollifierSecondMoment X (-(N : ℝ)) (N : ℝ) ≤
        5 * Real.pi * Real.exp 1 * X +
          (5 * Real.pi / 2) * (1 + Real.log X) * N := hbase'
    _ ≤ 5 * Real.pi * Real.exp 1 *
          ((N : ℝ) * (1 + Real.log (N : ℝ))) +
        (5 * Real.pi / 2) * (1 + Real.log (N : ℝ)) * N := by
      gcongr
      · exact hXNr.trans (by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hLN1 (Nat.cast_nonneg N))
    _ = C * (N : ℝ) * (1 + Real.log (N : ℝ)) := by
      dsimp only [C]
      ring

theorem exists_inghamCriticalErrorFourThirdMoment_symmetric_nat_le_polylog :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {X N : ℕ}, 4 ≤ X → X ≤ N →
      inghamCriticalErrorFourThirdMoment X (-(N : ℝ)) (N : ℝ) ≤
        C * (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 2 := by
  obtain ⟨CZ, hCZ, hZbound⟩ :=
    exists_inghamCriticalZetaFourthMoment_symmetric_nat_le_polylog
  obtain ⟨CM, hCM, hMbound⟩ :=
    exists_inghamCriticalMollifierSecondMoment_symmetric_nat_le_polylog
  let A : ℝ := (2 : ℝ) ^ (1 / 3 : ℝ)
  let C : ℝ := A * CZ ^ (1 / 3 : ℝ) * CM ^ (2 / 3 : ℝ) + 2 * A
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro X N hX hXN
  let L : ℝ := 1 + Real.log (N : ℝ)
  have hN4 : 4 ≤ N := hX.trans hXN
  have hNpos : 0 < N := by omega
  have hNR0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNRnonneg : (0 : ℝ) ≤ N := hNR0.le
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL1 : 1 ≤ L := by
    dsimp only [L]
    linarith [Real.log_nonneg hN1]
  have hL0 : 0 ≤ L := by positivity
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
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
        CZ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) * L ^ (4 / 3 : ℝ) := by
    calc
      (inghamCriticalZetaFourthMoment (-(N : ℝ)) (N : ℝ)) ^ (1 / 3 : ℝ) ≤
          (CZ * (N : ℝ) * L ^ 4) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow hZ0 hZb (by norm_num)
      _ = CZ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) *
          L ^ (4 / 3 : ℝ) := by
        rw [Real.mul_rpow (mul_nonneg hCZ hNRnonneg) (pow_nonneg hL0 4),
          Real.mul_rpow hCZ hNRnonneg, ← Real.rpow_natCast L 4,
          ← Real.rpow_mul hL0]
        norm_num
  have hMpow :
      (inghamCriticalMollifierSecondMoment X (-(N : ℝ)) (N : ℝ)) ^ (2 / 3 : ℝ) ≤
        CM ^ (2 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) * L ^ (2 / 3 : ℝ) := by
    calc
      (inghamCriticalMollifierSecondMoment X (-(N : ℝ)) (N : ℝ)) ^ (2 / 3 : ℝ) ≤
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
      A * (inghamCriticalZetaFourthMoment (-(N : ℝ)) (N : ℝ)) ^ (1 / 3 : ℝ) ≤
        A * (CZ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) *
          L ^ (4 / 3 : ℝ)) :=
    mul_le_mul_of_nonneg_left hZpow hA
  have hfirstFactorNonneg : 0 ≤
      A * (CZ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) *
        L ^ (4 / 3 : ℝ)) := by positivity
  have hmainProduct :
      A * (inghamCriticalZetaFourthMoment (-(N : ℝ)) (N : ℝ)) ^ (1 / 3 : ℝ) *
          (inghamCriticalMollifierSecondMoment X (-(N : ℝ)) (N : ℝ)) ^ (2 / 3 : ℝ) ≤
        A * (CZ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) *
          L ^ (4 / 3 : ℝ)) *
          (CM ^ (2 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) *
            L ^ (2 / 3 : ℝ)) :=
    mul_le_mul hfirstFactor hMpow
      (Real.rpow_nonneg hM0 _) hfirstFactorNonneg
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
  have hlast : 2 * A * (N : ℝ) ≤ 2 * A * (N : ℝ) * L ^ 2 := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hL2 (mul_nonneg (by positivity) hNRnonneg)
  change inghamCriticalErrorFourThirdMoment X (-(N : ℝ)) (N : ℝ) ≤
    C * (N : ℝ) * L ^ 2
  calc
    inghamCriticalErrorFourThirdMoment X (-(N : ℝ)) (N : ℝ) ≤
        A * (inghamCriticalZetaFourthMoment (-(N : ℝ)) (N : ℝ)) ^ (1 / 3 : ℝ) *
          (inghamCriticalMollifierSecondMoment X (-(N : ℝ)) (N : ℝ)) ^ (2 / 3 : ℝ) +
        A * ((N : ℝ) - (-(N : ℝ))) := by simpa only [A] using hbase
    _ ≤ A * (CZ ^ (1 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) *
          L ^ (4 / 3 : ℝ)) *
          (CM ^ (2 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) *
            L ^ (2 / 3 : ℝ)) + 2 * A * (N : ℝ) := by
      convert add_le_add_right hmainProduct (2 * A * (N : ℝ)) using 1 <;> ring
    _ = (A * CZ ^ (1 / 3 : ℝ) * CM ^ (2 / 3 : ℝ)) *
          ((N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ)) *
          (L ^ (4 / 3 : ℝ) * L ^ (2 / 3 : ℝ)) + 2 * A * (N : ℝ) := by ring
    _ = (A * CZ ^ (1 / 3 : ℝ) * CM ^ (2 / 3 : ℝ)) *
          (N : ℝ) * L ^ 2 + 2 * A * (N : ℝ) := by rw [hmulN, hmulL]
    _ ≤ (A * CZ ^ (1 / 3 : ℝ) * CM ^ (2 / 3 : ℝ)) *
          (N : ℝ) * L ^ 2 + 2 * A * (N : ℝ) * L ^ 2 := by gcongr
    _ = C * (N : ℝ) * L ^ 2 := by
      dsimp only [C]
      ring

end RHTower.Sieve

