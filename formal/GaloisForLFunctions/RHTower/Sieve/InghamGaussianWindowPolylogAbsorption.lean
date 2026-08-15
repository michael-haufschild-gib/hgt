import GaloisForLFunctions.RHTower.Sieve.InghamGaussianWindowAbsorption
import GaloisForLFunctions.RHTower.Sieve.InghamCriticalGlobalErrorMomentPolylog

/-! # Gaussian absorption with retained polylogarithmic endpoint loss -/

noncomputable section

open Set

namespace RHTower.Sieve

theorem gaussianCriticalWindowPolylogAbsorption
    (X : ℕ) (tau : ℝ) (hX : 4 ≤ X) :
    let N := Nat.ceil (|tau| + (X : ℝ))
    Real.exp (-(4 / 3 : ℝ) *
        (max 0 (|tau| - (X : ℝ)) / (X : ℝ)) ^ 2) *
        ((N : ℝ) * (1 + Real.log (N : ℝ)) ^ 2) ≤
      64 * Real.exp 3 * (X : ℝ) *
        (1 + Real.log (X : ℝ)) ^ 2 := by
  let d : ℝ := max 0 (|tau| - (X : ℝ))
  let y : ℝ := d / (X : ℝ)
  let N : ℕ := Nat.ceil (|tau| + (X : ℝ))
  dsimp only
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hXone : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hd0 : 0 ≤ d := by dsimp only [d]; exact le_max_left _ _
  have hy0 : 0 ≤ y := div_nonneg hd0 hXpos.le
  have habsd : |tau| + (X : ℝ) ≤ d + 2 * (X : ℝ) := by
    by_cases h : |tau| ≤ (X : ℝ)
    · have hd : d = 0 := by
        dsimp only [d]
        rw [max_eq_left (sub_nonpos.mpr h)]
      rw [hd]
      linarith
    · have hd : d = |tau| - (X : ℝ) := by
        dsimp only [d]
        rw [max_eq_right (sub_nonneg.mpr (le_of_not_ge h))]
      rw [hd]
      linarith
  have hceil : (N : ℝ) < |tau| + (X : ℝ) + 1 := by
    dsimp only [N]
    exact Nat.ceil_lt_add_one (by positivity)
  have hNle : (N : ℝ) ≤ d + 3 * (X : ℝ) := by linarith
  have hfactor : d + 3 * (X : ℝ) = (X : ℝ) * (y + 3) := by
    dsimp only [y]
    field_simp
  have hNfactor : (N : ℝ) ≤ (X : ℝ) * (y + 3) := by
    rw [← hfactor]
    exact hNle
  have hXleN : (X : ℝ) ≤ (N : ℝ) := by
    dsimp only [N]
    exact (show (X : ℝ) ≤ |tau| + (X : ℝ) by linarith [abs_nonneg tau]) |>.trans
      (Nat.le_ceil _)
  have hNpos : (0 : ℝ) < N := by
    exact lt_of_lt_of_le hXpos hXleN
  have hy3pos : 0 < y + 3 := by linarith
  have hprodpos : 0 < (X : ℝ) * (y + 3) := mul_pos hXpos hy3pos
  have hlogN : Real.log (N : ℝ) ≤ Real.log ((X : ℝ) * (y + 3)) :=
    Real.log_le_log hNpos hNfactor
  have hlogProd : Real.log ((X : ℝ) * (y + 3)) =
      Real.log (X : ℝ) + Real.log (y + 3) := by
    rw [Real.log_mul hXpos.ne' hy3pos.ne']
  have hlogy : Real.log (y + 3) ≤ y + 2 := by
    have h := Real.log_le_sub_one_of_pos hy3pos
    linarith
  have hLX1 : 1 ≤ 1 + Real.log (X : ℝ) := by
    linarith [Real.log_nonneg hXone]
  have hLN0 : 0 ≤ 1 + Real.log (N : ℝ) := by
    have hNone : (1 : ℝ) ≤ N := hXone.trans hXleN
    linarith [Real.log_nonneg hNone]
  have hlogScale : 1 + Real.log (N : ℝ) ≤
      (1 + Real.log (X : ℝ)) * (y + 3) := by
    rw [hlogProd] at hlogN
    have hprod : 0 ≤ ((1 + Real.log (X : ℝ)) - 1) * (y + 2) :=
      mul_nonneg (sub_nonneg.mpr hLX1) (by linarith)
    nlinarith
  have hlogSq : (1 + Real.log (N : ℝ)) ^ 2 ≤
      ((1 + Real.log (X : ℝ)) * (y + 3)) ^ 2 := by gcongr
  have hNL : (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 2 ≤
      (X : ℝ) * (1 + Real.log (X : ℝ)) ^ 2 * (y + 3) ^ 3 := by
    calc
      (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 2 ≤
          ((X : ℝ) * (y + 3)) *
            ((1 + Real.log (X : ℝ)) * (y + 3)) ^ 2 := by gcongr
      _ = (X : ℝ) * (1 + Real.log (X : ℝ)) ^ 2 * (y + 3) ^ 3 := by ring
  have hcore : Real.exp (-(4 / 3 : ℝ) * y ^ 2) * (y + 3) ^ 3 ≤
      64 * Real.exp 3 := by
    by_cases hy : y ≤ 1
    · have hy4 : y + 3 ≤ 4 := by linarith
      have hcub : (y + 3) ^ 3 ≤ (4 : ℝ) ^ 3 := by gcongr
      have hexp : Real.exp (-(4 / 3 : ℝ) * y ^ 2) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg y])
      have hexp3 : (1 : ℝ) ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
      calc
        Real.exp (-(4 / 3 : ℝ) * y ^ 2) * (y + 3) ^ 3 ≤
            1 * (4 : ℝ) ^ 3 := mul_le_mul hexp hcub (by positivity) (by positivity)
        _ = 64 := by norm_num
        _ ≤ 64 * Real.exp 3 := by nlinarith
    · have hy1 : 1 ≤ y := le_of_not_ge hy
      have hy4 : y + 3 ≤ 4 * y := by linarith
      have hcub : (y + 3) ^ 3 ≤ (4 * y) ^ 3 := by gcongr
      have hy3le4 : y ^ 3 ≤ y ^ 4 := by nlinarith [sq_nonneg y, sq_nonneg (y - 1)]
      have habsorb := RHTower.rpow_mul_exp_neg_le
        (m := (2 : ℝ)) (c := (4 / 3 : ℝ)) (u := y ^ 2)
        (by norm_num) (by norm_num) (by nlinarith)
      have habsorb' : y ^ 4 * Real.exp (-((4 / 3 : ℝ) * y ^ 2)) ≤
          Real.exp 3 := by
        calc
          y ^ 4 * Real.exp (-((4 / 3 : ℝ) * y ^ 2)) =
              (y ^ 2) ^ (2 : ℝ) * Real.exp (-((4 / 3 : ℝ) * y ^ 2)) := by
            rw [Real.rpow_two]
            ring
          _ ≤ Real.exp ((2 : ℝ) ^ 2 / (4 / 3 : ℝ)) := habsorb
          _ = Real.exp 3 := by norm_num
      calc
        Real.exp (-(4 / 3 : ℝ) * y ^ 2) * (y + 3) ^ 3 ≤
            Real.exp (-(4 / 3 : ℝ) * y ^ 2) * (4 * y) ^ 3 := by gcongr
        _ = 64 * (y ^ 3 * Real.exp (-((4 / 3 : ℝ) * y ^ 2))) := by ring
        _ ≤ 64 * (y ^ 4 * Real.exp (-((4 / 3 : ℝ) * y ^ 2))) := by gcongr
        _ ≤ 64 * Real.exp 3 := by gcongr
  rw [show max 0 (|tau| - (X : ℝ)) = d by rfl,
    show d / (X : ℝ) = y by rfl]
  calc
    Real.exp (-(4 / 3 : ℝ) * y ^ 2) *
        ((N : ℝ) * (1 + Real.log (N : ℝ)) ^ 2) ≤
      Real.exp (-(4 / 3 : ℝ) * y ^ 2) *
        ((X : ℝ) * (1 + Real.log (X : ℝ)) ^ 2 * (y + 3) ^ 3) := by gcongr
    _ = (X : ℝ) * (1 + Real.log (X : ℝ)) ^ 2 *
        (Real.exp (-(4 / 3 : ℝ) * y ^ 2) * (y + 3) ^ 3) := by ring
    _ ≤ (X : ℝ) * (1 + Real.log (X : ℝ)) ^ 2 *
        (64 * Real.exp 3) := by gcongr
    _ = 64 * Real.exp 3 * (X : ℝ) *
        (1 + Real.log (X : ℝ)) ^ 2 := by ring

end RHTower.Sieve

