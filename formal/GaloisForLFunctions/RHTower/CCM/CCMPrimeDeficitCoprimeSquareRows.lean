import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitCoprimeHeadControl

/-!
# Signed control for all square-index coprime rows

Coprimality ignores positive powers of a row index. Consequently every
square-index row up to the full cutoff has the same cancellation as its
square root. Combining this identity with the actual reconstruction
bound controls the entire square-index block, including its large
indices and all partners.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

theorem ccmPrimeDeficitCoprimeRow_pow_succ (a k : ℕ) (T : ℝ) :
    ccmPrimeDeficitCoprimeRow (a ^ (k + 1)) T = ccmPrimeDeficitCoprimeRow a T := by
  simp only [ccmPrimeDeficitCoprimeRow, Nat.coprime_pow_left_iff (Nat.succ_pos k)]

def ccmPrimeDeficitCoprimeSquareCross (T : ℝ) : ℝ :=
  Real.exp (-T) * ∑ a ∈ Finset.Icc 2 ⌊Real.exp (T / 2)⌋₊,
    ccmPrimeDeficitMobiusCenteredWork (T - Real.log (a ^ 2 : ℕ)) *
      ccmPrimeDeficitCoprimeRow (a ^ 2) T

private theorem weighted_square_row_bound {T : ℝ} {a : ℕ}
    (hT : 0 ≤ T) (ha : a ∈ Finset.Icc 2 ⌊Real.exp (T / 2)⌋₊) :
    |ccmPrimeDeficitMobiusCenteredWork (T - Real.log (a ^ 2 : ℕ)) *
      ccmPrimeDeficitCoprimeRow (a ^ 2) T| ≤
        (7 / 8) * (T + 14) * (1 + T / 2) * (a : ℝ)⁻¹ := by
  have hapos : 0 < a := by have := (Finset.mem_Icc.mp ha).1; omega
  have haposR : (0 : ℝ) < a := by exact_mod_cast hapos
  have haT : (a : ℝ) ≤ Real.exp (T / 2) :=
    (Nat.le_floor_iff (Real.exp_pos _).le).mp (Finset.mem_Icc.mp ha).2
  have hlog : Real.log a ≤ T / 2 := (Real.log_le_iff_le_exp haposR).mpr haT
  have haFull : a ∈ Finset.Icc 1 ⌊Real.exp T⌋₊ := Finset.mem_Icc.mpr ⟨hapos,
    (Finset.mem_Icc.mp ha).2.trans
      (Nat.floor_mono (Real.exp_le_exp.mpr (by linarith only [hT])))⟩
  have hq := abs_ccmPrimeDeficitMobiusCenteredWork_le_exp (T - Real.log (a ^ 2 : ℕ))
  rw [Nat.cast_pow, Real.exp_sub, Real.exp_log (by positivity : (0 : ℝ) < (a : ℝ) ^ 2)] at hq
  have hr := abs_ccmPrimeDeficitCoprimeRow_le_logMass hT haFull
    (by have := (Finset.mem_Icc.mp ha).1; omega)
  have he : Real.exp T * Real.exp (-T) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [show (2 : ℕ) = 1 + 1 from rfl, ccmPrimeDeficitCoprimeRow_pow_succ,
    Nat.cast_pow, abs_mul]
  calc
    _ ≤ ((7 / 2) * (Real.exp T / (a : ℝ) ^ 2)) *
        (Real.exp (-T) * (T + 14) / 4 * ((a : ℝ) * (1 + Real.log a))) :=
      mul_le_mul hq hr (abs_nonneg _) (by positivity)
    _ = (7 / 8) * (T + 14) * (1 + Real.log a) * (a : ℝ)⁻¹ := by
      calc
        _ = (Real.exp T * Real.exp (-T)) *
            ((7 / 8) * (T + 14) * (1 + Real.log a) * (a : ℝ)⁻¹) := by
          field_simp
          ring
        _ = _ := by rw [he, one_mul]
    _ ≤ _ := by gcongr

/-- Complete square-index cross work decays even though its first index
can be as large as the full cutoff. Every coprime partner is retained. -/
theorem abs_ccmPrimeDeficitCoprimeSquareCross_le {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeDeficitCoprimeSquareCross T| ≤
      (7 / 8) * Real.exp (-T) * (T + 14) * (1 + T / 2) ^ 2 := by
  let B : ℝ := (7 / 8) * (T + 14) * (1 + T / 2)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hh : (∑ a ∈ Finset.Icc 2 ⌊Real.exp (T / 2)⌋₊, (a : ℝ)⁻¹) ≤ 1 + T / 2 := by
    calc
      _ ≤ ∑ a ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊, (a : ℝ)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun a ha => Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp ha).1; omega,
            (Finset.mem_Icc.mp ha).2⟩) (fun a _ _ => by positivity)
      _ = harmonic ⌊Real.exp (T / 2)⌋₊ := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      _ ≤ 1 + Real.log (Real.exp (T / 2)) :=
        harmonic_floor_le_one_add_log _ (Real.one_le_exp_iff.mpr (by positivity))
      _ = _ := by rw [Real.log_exp]
  have hs : |∑ a ∈ Finset.Icc 2 ⌊Real.exp (T / 2)⌋₊,
      ccmPrimeDeficitMobiusCenteredWork (T - Real.log (a ^ 2 : ℕ)) *
        ccmPrimeDeficitCoprimeRow (a ^ 2) T| ≤ B * (1 + T / 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ a ∈ Finset.Icc 2 ⌊Real.exp (T / 2)⌋₊, B * (a : ℝ)⁻¹ :=
        Finset.sum_le_sum (fun a ha => weighted_square_row_bound hT ha)
      _ = B * ∑ a ∈ Finset.Icc 2 ⌊Real.exp (T / 2)⌋₊, (a : ℝ)⁻¹ := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hh hB
  rw [ccmPrimeDeficitCoprimeSquareCross, abs_mul, abs_of_pos (Real.exp_pos (-T))]
  calc
    _ ≤ Real.exp (-T) * (B * (1 + T / 2)) :=
      mul_le_mul_of_nonneg_left hs (Real.exp_pos (-T)).le
    _ = _ := by dsimp only [B]; ring

end RHTower
