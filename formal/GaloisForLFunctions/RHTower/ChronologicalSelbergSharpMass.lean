import GaloisForLFunctions.RHTower.ChronologicalSelbergCoefficientMass
import Mathlib.NumberTheory.ArithmeticFunction.Liouville

/-!
# The exact coefficient-mass norm of finite Selberg inversion

Let `P(e) = Σ_{d∣e} d |μ(e/d)|`. The optimal constant in
`(Σ_{d≤N}|c_d|)² ≤ A Q_N(c)` is exactly `Σ_{e≤N} P(e)²/φ(e)`.
Liouville-signed coordinates `Y_e = λ(e) P(e)/φ(e)` attain equality:
complete multiplicativity aligns every nonzero term in each inverse row.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Absolute column mass of finite Möbius multiples inversion. -/
def selbergInverseMassWeight (e : ℕ) : ℝ :=
  ∑ d ∈ e.divisors, (d : ℝ) * |(moebius (e / d) : ℝ)|

/-- The exact squared norm from Selberg energy to absolute coefficient mass. -/
def selbergCoefficientMassConstant (N : ℕ) : ℝ :=
  ∑ e ∈ Icc 1 N, selbergInverseMassWeight e ^ 2 / (Nat.totient e : ℝ)

theorem selbergInverseMassWeight_nonneg (e : ℕ) : 0 ≤ selbergInverseMassWeight e :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)

@[simp] theorem selbergInverseMassWeight_one : selbergInverseMassWeight 1 = 1 := by
  simp [selbergInverseMassWeight]

theorem selbergInverseMassWeight_le_sigma (e : ℕ) :
    selbergInverseMassWeight e ≤ ((sigma 1 e : ℕ) : ℝ) := by
  calc
    _ ≤ ∑ d ∈ e.divisors, (d : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hμ : |(moebius (e / d) : ℝ)| ≤ 1 := by
        rcases moebius_eq_or (e / d) with h | h | h <;> simp [h]
      simpa using mul_le_mul_of_nonneg_left hμ (Nat.cast_nonneg d)
    _ = _ := by simp [sigma_apply]

theorem selbergCoefficientMassConstant_nonneg (N : ℕ) :
    0 ≤ selbergCoefficientMassConstant N :=
  Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

theorem selbergCoefficientMassConstant_pos {N : ℕ} (hN : 1 ≤ N) :
    0 < selbergCoefficientMassConstant N := by
  have h : (1 : ℝ) ≤ selbergCoefficientMassConstant N := by
    have hs := Finset.single_le_sum
      (s := Icc 1 N) (f := fun e => selbergInverseMassWeight e^2 / (Nat.totient e : ℝ))
      (fun e _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)
    simpa [selbergCoefficientMassConstant] using hs
  linarith

/-- The exact norm constant has quadratic growth at most, uniformly in the cutoff. -/
theorem selbergCoefficientMassConstant_le (N : ℕ) :
    selbergCoefficientMassConstant N ≤ 16384 * (N : ℝ)^2 := by
  apply le_trans _ (sum_sigma_sq_div_totient_le N)
  apply Finset.sum_le_sum
  intro e he
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (selbergInverseMassWeight_nonneg e) (selbergInverseMassWeight_le_sigma e) 2)
    (Nat.cast_nonneg _)

private theorem inverse_abs_mass_le (N : ℕ) (y : ℕ → ℝ) :
    (∑ d ∈ Icc 1 N, |pmRamanujanResidueCoeff y N d|) ≤
      ∑ e ∈ Icc 1 N, selbergInverseMassWeight e * |y e| := by
  have hterm (d : ℕ) :
      |pmRamanujanResidueCoeff y N d| ≤
        ∑ m ∈ Icc 1 (N / d), (d : ℝ) * |(moebius m : ℝ)| * |y (d * m)| := by
    unfold pmRamanujanResidueCoeff
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg d)]
    calc
      _ ≤ (d : ℝ) * ∑ m ∈ Icc 1 (N / d), |(moebius m : ℝ) * y (d * m)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg d)
      _ = _ := by simp only [Finset.mul_sum, abs_mul, mul_assoc]
  calc
    _ ≤ ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d),
        (d : ℝ) * |(moebius m : ℝ)| * |y (d * m)| := Finset.sum_le_sum fun d _ => hterm d
    _ = ∑ e ∈ Icc 1 N, ∑ d ∈ e.divisors,
        (d : ℝ) * |(moebius (e / d) : ℝ)| * |y (d * (e / d))| :=
      (Sieve.sum_divisors_swap N (fun d m =>
        (d : ℝ) * |(moebius m : ℝ)| * |y (d * m)|)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      rw [selbergInverseMassWeight, Finset.sum_mul]
      exact Finset.sum_congr rfl fun d hd => by
        rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]

/-- The sharp universal mass inequality, with its exact arithmetic constant. -/
theorem sum_abs_coeff_sq_le_sharp_selberg (N : ℕ) (c : ℕ → ℝ) :
    (∑ d ∈ Icc 1 N, |c d|)^2 ≤
      selbergCoefficientMassConstant N * selbergTotientDiagonalForm N c := by
  have hmass : (∑ d ∈ Icc 1 N, |c d|) ≤
      ∑ e ∈ Icc 1 N, selbergInverseMassWeight e * |selbergMultiplesCoord N c e| := by
    calc
      _ = ∑ d ∈ Icc 1 N,
          |pmRamanujanResidueCoeff (selbergMultiplesCoord N c) N d| :=
        Finset.sum_congr rfl fun d hd => by rw [ramanujan_inverse_selbergCoords_eq N c d hd]
      _ ≤ _ := inverse_abs_mass_le N (selbergMultiplesCoord N c)
  apply le_trans (pow_le_pow_left₀ (Finset.sum_nonneg fun d _ => abs_nonneg (c d)) hmass 2)
  unfold selbergCoefficientMassConstant selbergTotientDiagonalForm
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro e he
    exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  · intro e he
    exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  · intro e he
    have hφ : (Nat.totient e : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (Finset.mem_Icc.mp he).1).ne'
    apply le_of_eq
    rw [mul_pow, sq_abs]
    field_simp

private theorem abs_liouville_real {e : ℕ} (he : e ≠ 0) : |(liouville e : ℝ)| = 1 := by
  simp [liouville_apply he]

private theorem moebius_mul_liouville_real (m : ℕ) :
    (moebius m : ℝ) * (liouville m : ℝ) = |(moebius m : ℝ)| := by
  by_cases hm : Squarefree m
  · have heq : (liouville m : ℝ) = (moebius m : ℝ) := by
      simp [liouville_apply hm.ne_zero, moebius_apply_of_squarefree hm]
    rw [heq]
    rcases moebius_eq_or m with h | h | h <;> simp [h]
  · simp [moebius_eq_zero_of_not_squarefree hm]

/-- Liouville signs align every nonzero summand in each row of the inverse. -/
theorem moebius_mul_liouville_mul_real (d m : ℕ) :
    (moebius m : ℝ) * (liouville (d * m) : ℝ) =
      (liouville d : ℝ) * |(moebius m : ℝ)| := by
  rw [liouville_apply_mul]
  push_cast
  calc
    _ = (liouville d : ℝ) * ((moebius m : ℝ) * (liouville m : ℝ)) := by ring
    _ = _ := by rw [moebius_mul_liouville_real]

/-- Coordinates attaining the full inverse coefficient-mass norm. -/
def selbergMassExtremalCoord (e : ℕ) : ℝ :=
  (liouville e : ℝ) * selbergInverseMassWeight e / (Nat.totient e : ℝ)

/-- An explicit extremal coefficient row at each finite cutoff. -/
def selbergMassExtremalRow (N : ℕ) : ℕ → ℝ :=
  pmRamanujanResidueCoeff selbergMassExtremalCoord N

private theorem extremal_row_abs {d : ℕ} (hd : 0 < d) (N : ℕ) :
    |selbergMassExtremalRow N d| =
      ∑ m ∈ Icc 1 (N / d), (d : ℝ) * |(moebius m : ℝ)| *
        (selbergInverseMassWeight (d * m) / (Nat.totient (d * m) : ℝ)) := by
  have hrow : selbergMassExtremalRow N d =
      (liouville d : ℝ) * ∑ m ∈ Icc 1 (N / d), (d : ℝ) * |(moebius m : ℝ)| *
        (selbergInverseMassWeight (d * m) / (Nat.totient (d * m) : ℝ)) := by
    unfold selbergMassExtremalRow pmRamanujanResidueCoeff
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    dsimp [selbergMassExtremalCoord]
    calc
      _ = (d : ℝ) * ((moebius m : ℝ) * (liouville (d * m) : ℝ)) *
          (selbergInverseMassWeight (d * m) / (Nat.totient (d * m) : ℝ)) := by ring
      _ = _ := by rw [moebius_mul_liouville_mul_real]; ring
  rw [hrow, abs_mul, abs_liouville_real hd.ne', one_mul, abs_of_nonneg]
  exact Finset.sum_nonneg fun m _ => mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
    (div_nonneg (selbergInverseMassWeight_nonneg _) (Nat.cast_nonneg _))

/-- The extremal row has absolute coefficient mass exactly equal to the sharp constant. -/
theorem sum_abs_selbergMassExtremalRow (N : ℕ) :
    ∑ d ∈ Icc 1 N, |selbergMassExtremalRow N d| = selbergCoefficientMassConstant N := by
  rw [Finset.sum_congr rfl (fun d hd => extremal_row_abs (Finset.mem_Icc.mp hd).1 N),
    ← Sieve.sum_divisors_swap N (fun d m => (d : ℝ) * |(moebius m : ℝ)| *
      (selbergInverseMassWeight (d * m) / (Nat.totient (d * m) : ℝ)))]
  unfold selbergCoefficientMassConstant
  apply Finset.sum_congr rfl
  intro e he
  calc
    _ = ∑ d ∈ e.divisors, (d : ℝ) * |(moebius (e / d) : ℝ)| *
        (selbergInverseMassWeight e / (Nat.totient e : ℝ)) :=
      Finset.sum_congr rfl fun d hd => by
        rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
    _ = selbergInverseMassWeight e *
        (selbergInverseMassWeight e / (Nat.totient e : ℝ)) := (Finset.sum_mul ..).symm
    _ = _ := by ring

/-- The same row has Selberg energy exactly equal to the sharp constant. -/
theorem selberg_selbergMassExtremalRow (N : ℕ) :
    selbergTotientDiagonalForm N (selbergMassExtremalRow N) =
      selbergCoefficientMassConstant N := by
  unfold selbergTotientDiagonalForm selbergCoefficientMassConstant
  apply Finset.sum_congr rfl
  intro e he
  have hepos : 0 < e := (Finset.mem_Icc.mp he).1
  have hφ : (Nat.totient e : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hepos).ne'
  have hSignSq : (liouville e : ℝ)^2 = 1 := by
    have h := congrArg (fun x : ℝ => x^2) (abs_liouville_real hepos.ne')
    simpa only [sq_abs, one_pow] using h
  rw [selbergMassExtremalRow, selbergMultiplesCoord_ramanujan_inverse, if_pos he]
  simp only [selbergMassExtremalCoord, div_pow, mul_pow, hSignSq, one_mul]
  field_simp

/-- Complete classification of constants in the universal coefficient-mass inequality. -/
theorem selberg_mass_inequality_iff {N : ℕ} (hN : 1 ≤ N) (C : ℝ) :
    (∀ c : ℕ → ℝ, (∑ d ∈ Icc 1 N, |c d|)^2 ≤
      C * selbergTotientDiagonalForm N c) ↔ selbergCoefficientMassConstant N ≤ C := by
  constructor
  · intro h
    have hs := h (selbergMassExtremalRow N)
    rw [sum_abs_selbergMassExtremalRow, selberg_selbergMassExtremalRow, pow_two] at hs
    exact (mul_le_mul_iff_of_pos_right (selbergCoefficientMassConstant_pos hN)).mp hs
  · intro h c
    exact (sum_abs_coeff_sq_le_sharp_selberg N c).trans
      (mul_le_mul_of_nonneg_right h (selbergTotientDiagonalForm_nonneg N c))

end

end RHTower
