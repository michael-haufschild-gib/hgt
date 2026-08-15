import GaloisForLFunctions.RHTower.Sieve.InghamCriticalGlobalErrorMoment
import GaloisForLFunctions.RHTower.MellinOrderOneEnvelope

noncomputable section

open Set

namespace RHTower.Sieve

/-- Gaussian damping uniformly absorbs polynomial growth of the symmetric window needed to cover
an arbitrary translate of `[-X,X]`. -/
theorem gaussianCriticalWindowAbsorption
    (X : ℕ) (tau : ℝ) (hX : 4 ≤ X) :
    let N := Nat.ceil (|tau| + (X : ℝ))
    Real.exp (-(4 / 3 : ℝ) *
        (max 0 (|tau| - (X : ℝ)) / (X : ℝ)) ^ 2) *
        (N : ℝ) ^ (251 / 250 : ℝ) ≤
      (4 : ℝ) ^ (251 / 250 : ℝ) * Real.exp (3 / 4 : ℝ) *
        (X : ℝ) ^ (251 / 250 : ℝ) := by
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
  have hNpow : (N : ℝ) ^ (251 / 250 : ℝ) ≤
      ((X : ℝ) * (y + 3)) ^ (251 / 250 : ℝ) := by
    rw [← hfactor]
    exact Real.rpow_le_rpow (by positivity) hNle (by norm_num)
  have hmulrpow : ((X : ℝ) * (y + 3)) ^ (251 / 250 : ℝ) =
      (X : ℝ) ^ (251 / 250 : ℝ) *
        (y + 3) ^ (251 / 250 : ℝ) := by
    exact Real.mul_rpow hXpos.le (by linarith)
  have hcore : Real.exp (-(4 / 3 : ℝ) * y ^ 2) *
      (y + 3) ^ (251 / 250 : ℝ) ≤
        (4 : ℝ) ^ (251 / 250 : ℝ) * Real.exp (3 / 4 : ℝ) := by
    by_cases hy : y ≤ 1
    · have hy4 : y + 3 ≤ 4 := by linarith
      have hpow : (y + 3) ^ (251 / 250 : ℝ) ≤
          (4 : ℝ) ^ (251 / 250 : ℝ) :=
        Real.rpow_le_rpow (by linarith) hy4 (by norm_num)
      have hexp : Real.exp (-(4 / 3 : ℝ) * y ^ 2) ≤ 1 := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        nlinarith [sq_nonneg y]
      have hexpone : (1 : ℝ) ≤ Real.exp (3 / 4 : ℝ) := Real.one_le_exp (by norm_num)
      calc
        Real.exp (-(4 / 3 : ℝ) * y ^ 2) *
            (y + 3) ^ (251 / 250 : ℝ) ≤
            1 * (4 : ℝ) ^ (251 / 250 : ℝ) :=
          mul_le_mul hexp hpow (by positivity) (by positivity)
        _ = (4 : ℝ) ^ (251 / 250 : ℝ) := one_mul _
        _ ≤ (4 : ℝ) ^ (251 / 250 : ℝ) * Real.exp (3 / 4 : ℝ) := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hexpone
              (Real.rpow_nonneg (show (0 : ℝ) ≤ 4 by norm_num) (251 / 250 : ℝ))
    · have hy1 : 1 ≤ y := le_of_not_ge hy
      have hy4 : y + 3 ≤ 4 * y := by linarith
      have hpow4 : (y + 3) ^ (251 / 250 : ℝ) ≤
          (4 * y) ^ (251 / 250 : ℝ) :=
        Real.rpow_le_rpow (by linarith) hy4 (by norm_num)
      have hyrpow : y ^ (251 / 250 : ℝ) ≤ y ^ 2 := by
        simpa only [Real.rpow_two] using
          (Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num :
            (251 / 250 : ℝ) ≤ 2))
      have habsorb := RHTower.rpow_mul_exp_neg_le
        (m := (1 : ℝ)) (c := (4 / 3 : ℝ)) (u := y ^ 2)
        (by norm_num) (by norm_num) (by nlinarith)
      have habsorb' : y ^ 2 * Real.exp (-((4 / 3 : ℝ) * y ^ 2)) ≤
          Real.exp (3 / 4 : ℝ) := by
        convert habsorb using 1 <;> norm_num
      calc
        Real.exp (-(4 / 3 : ℝ) * y ^ 2) *
            (y + 3) ^ (251 / 250 : ℝ) ≤
            Real.exp (-(4 / 3 : ℝ) * y ^ 2) *
              (4 * y) ^ (251 / 250 : ℝ) := by gcongr
        _ = (4 : ℝ) ^ (251 / 250 : ℝ) *
              (y ^ (251 / 250 : ℝ) *
                Real.exp (-((4 / 3 : ℝ) * y ^ 2))) := by
          rw [Real.mul_rpow (by norm_num) hy0]
          ring
        _ ≤ (4 : ℝ) ^ (251 / 250 : ℝ) *
              (y ^ 2 * Real.exp (-((4 / 3 : ℝ) * y ^ 2))) := by gcongr
        _ ≤ (4 : ℝ) ^ (251 / 250 : ℝ) * Real.exp (3 / 4 : ℝ) := by gcongr
  rw [show max 0 (|tau| - (X : ℝ)) = d by rfl,
    show d / (X : ℝ) = y by rfl]
  calc
    Real.exp (-(4 / 3 : ℝ) * y ^ 2) *
        (N : ℝ) ^ (251 / 250 : ℝ) ≤
        Real.exp (-(4 / 3 : ℝ) * y ^ 2) *
          ((X : ℝ) * (y + 3)) ^ (251 / 250 : ℝ) := by gcongr
    _ = (X : ℝ) ^ (251 / 250 : ℝ) *
          (Real.exp (-(4 / 3 : ℝ) * y ^ 2) *
            (y + 3) ^ (251 / 250 : ℝ)) := by
      rw [hmulrpow]
      ring
    _ ≤ (X : ℝ) ^ (251 / 250 : ℝ) *
        ((4 : ℝ) ^ (251 / 250 : ℝ) * Real.exp (3 / 4 : ℝ)) := by gcongr
    _ = (4 : ℝ) ^ (251 / 250 : ℝ) * Real.exp (3 / 4 : ℝ) *
        (X : ℝ) ^ (251 / 250 : ℝ) := by ring

end RHTower.Sieve
