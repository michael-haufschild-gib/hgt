import GaloisForLFunctions.RHTower.Sieve.MaynardFixedDivisorMoment
import GaloisForLFunctions.RHTower.Sieve.MaynardGroupedFactor
import GaloisForLFunctions.RHTower.Sieve.MaynardRaisedCoefficient

/-!
# Fixed-polylog energy for raised Maynard factors

This file converts a fixed divisor-power pointwise bound on a coefficient vector into an explicit
polylogarithmic energy bound for every bounded convolution power.  It is the coefficient-energy
replacement for the nonuniform `Y^ρ` bound: no constant depends on a moving `ρ`.
-/

namespace RHTower.Sieve

open Finset

/-- A convolution power of a divisor-controlled vector is again divisor-controlled, with fully
explicit exponent and scalar dependence. -/
theorem norm_convPow_le_const_mul_divisors_pow
    {N ell w : ℕ} {C : ℝ} (hC : 0 ≤ C) (a : Fin N → ℂ)
    (hpoint : ∀ n : Fin N,
      ‖a n‖ ≤ C * ((((n : ℕ) + 1).divisors.card : ℝ) ^ w))
    (j : Fin (N ^ ell)) :
    ‖convPow N ell a j‖ ≤
      C ^ ell * ((((j : ℕ) + 1).divisors.card : ℝ) ^ ((w + 1) * ell)) := by
  classical
  let fibre : Finset (Fin ell → Fin N) :=
    (Finset.univ : Finset (Fin ell → Fin N)).filter (fun p => powIdx p = j)
  have hcard : (fibre.card : ℝ) ≤
      (((j : ℕ) + 1).divisors.card : ℝ) ^ ell := by
    simpa [fibre, powFibreOn] using
      (show ((powFibreOn N ell (Finset.univ : Finset (Fin N)) j).card : ℝ) ≤
          (((j : ℕ) + 1).divisors.card : ℝ) ^ ell from
        (by exact_mod_cast powFibreOn_card_le_divisors_pow N ell Finset.univ j))
  have hterm : ∀ p ∈ fibre,
      ‖∏ i : Fin ell, a (p i)‖ ≤
        (C * ((((j : ℕ) + 1).divisors.card : ℝ) ^ w)) ^ ell := by
    intro p hp
    have hpj : powIdx p = j := by
      simpa [fibre] using hp
    have hprod : ∏ i : Fin ell, ((p i : ℕ) + 1) = (j : ℕ) + 1 := by
      rw [← powIdx_val_add_one p, hpj]
    rw [norm_prod]
    calc
      ∏ i : Fin ell, ‖a (p i)‖
          ≤ ∏ _i : Fin ell,
              (C * ((((j : ℕ) + 1).divisors.card : ℝ) ^ w)) := by
            apply Finset.prod_le_prod
            · intro i hi
              exact norm_nonneg _
            · intro i hi
              have hdvd : (p i : ℕ) + 1 ∣ (j : ℕ) + 1 := by
                rw [← hprod]
                exact Finset.dvd_prod_of_mem
                  (fun k : Fin ell => ((p k : ℕ) + 1)) (Finset.mem_univ i)
              have hmono : (((p i : ℕ) + 1).divisors.card : ℝ) ≤
                  (((j : ℕ) + 1).divisors.card : ℝ) := by
                exact_mod_cast card_divisors_mono_of_dvd hdvd (by omega)
              exact (hpoint (p i)).trans
                (mul_le_mul_of_nonneg_left
                  (pow_le_pow_left₀ (by positivity) hmono w) hC)
      _ = (C * ((((j : ℕ) + 1).divisors.card : ℝ) ^ w)) ^ ell := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsum : ‖convPow N ell a j‖ ≤
      (fibre.card : ℝ) *
        (C * ((((j : ℕ) + 1).divisors.card : ℝ) ^ w)) ^ ell := by
    rw [convPow]
    change ‖∑ p ∈ fibre, ∏ i : Fin ell, a (p i)‖ ≤ _
    calc
      ‖∑ p ∈ fibre, ∏ i : Fin ell, a (p i)‖
          ≤ ∑ p ∈ fibre, ‖∏ i : Fin ell, a (p i)‖ := norm_sum_le _ _
      _ ≤ ∑ _p ∈ fibre,
          (C * ((((j : ℕ) + 1).divisors.card : ℝ) ^ w)) ^ ell := by
            exact Finset.sum_le_sum fun p hp => hterm p hp
      _ = (fibre.card : ℝ) *
          (C * ((((j : ℕ) + 1).divisors.card : ℝ) ^ w)) ^ ell := by
            rw [Finset.sum_const, nsmul_eq_mul]
  calc
    ‖convPow N ell a j‖
        ≤ (fibre.card : ℝ) *
            (C * ((((j : ℕ) + 1).divisors.card : ℝ) ^ w)) ^ ell := hsum
    _ ≤ ((((j : ℕ) + 1).divisors.card : ℝ) ^ ell) *
          (C * ((((j : ℕ) + 1).divisors.card : ℝ) ^ w)) ^ ell := by
            exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = C ^ ell *
          ((((j : ℕ) + 1).divisors.card : ℝ) ^ ((w + 1) * ell)) := by
            rw [mul_pow, ← pow_mul]
            ring

/-- **Fixed-polylog raised energy.**  The complete coefficient energy of a bounded convolution
power has linear length and a fixed, explicit log power. -/
theorem sum_normSq_convPow_le_fixed_polylog
    {N ell w : ℕ} (hN : 1 ≤ N) {C : ℝ} (hC : 0 ≤ C) (a : Fin N → ℂ)
    (hpoint : ∀ n : Fin N,
      ‖a n‖ ≤ C * ((((n : ℕ) + 1).divisors.card : ℝ) ^ w)) :
    ∑ j : Fin (N ^ ell), ‖convPow N ell a j‖ ^ (2 : ℕ) ≤
      C ^ (2 * ell) *
        (((N ^ ell : ℕ) : ℝ) *
          (1 + Real.log ((N ^ ell : ℕ) : ℝ)) ^
            (2 ^ (2 * ((w + 1) * ell)) - 1)) := by
  have hM : 1 ≤ N ^ ell := Nat.one_le_pow ell N (by omega)
  have hCpow : 0 ≤ C ^ (2 * ell) := pow_nonneg hC _
  have hpoint' : ∀ j : Fin (N ^ ell),
      ‖convPow N ell a j‖ ^ (2 : ℕ) ≤
        C ^ (2 * ell) *
          ((((j : ℕ) + 1).divisors.card : ℝ) ^ (2 * ((w + 1) * ell))) := by
    intro j
    have hnorm := norm_convPow_le_const_mul_divisors_pow hC a hpoint j
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    calc
      ‖convPow N ell a j‖ ^ (2 : ℕ)
          ≤ (C ^ ell *
              ((((j : ℕ) + 1).divisors.card : ℝ) ^ ((w + 1) * ell))) ^ (2 : ℕ) := hsq
      _ = C ^ (2 * ell) *
          ((((j : ℕ) + 1).divisors.card : ℝ) ^ (2 * ((w + 1) * ell))) := by
            rw [mul_pow, ← pow_mul, ← pow_mul]
            congr 2 <;> ring
  calc
    ∑ j : Fin (N ^ ell), ‖convPow N ell a j‖ ^ (2 : ℕ)
        ≤ ∑ j : Fin (N ^ ell),
            C ^ (2 * ell) *
              ((((j : ℕ) + 1).divisors.card : ℝ) ^ (2 * ((w + 1) * ell))) := by
          exact Finset.sum_le_sum fun j hj => hpoint' j
    _ = C ^ (2 * ell) *
          ∑ j : Fin (N ^ ell),
            ((((j : ℕ) + 1).divisors.card : ℝ) ^ (2 * ((w + 1) * ell))) := by
          rw [Finset.mul_sum]
    _ ≤ C ^ (2 * ell) *
        (((N ^ ell : ℕ) : ℝ) *
          (1 + Real.log ((N ^ ell : ℕ) : ℝ)) ^
            (2 ^ (2 * ((w + 1) * ell)) - 1)) := by
          exact mul_le_mul_of_nonneg_left
            (sum_fin_card_divisors_pow_le_polylog
              (2 * ((w + 1) * ell)) (N ^ ell) hM) hCpow

/-- Specialized fixed-polylog energy for a grouped dyadic Heath--Brown factor. -/
theorem sum_normSq_convPow_groupedDyadicCoeffVector_le_fixed_polylog
    {ι : Type*} [Fintype ι] (F : ι → ArithmeticFunction ℝ) (q : ι → ℕ)
    {L : ℝ} (hL : 0 ≤ L)
    (hfactor : ∀ i n, ‖arithmeticDyadicBlock (F i) (q i) n‖ ≤ L)
    (ell : ℕ) :
    ∑ j : Fin ((groupedDyadicUpper q) ^ ell),
        ‖convPow (groupedDyadicUpper q) ell (groupedDyadicCoeffVector F q) j‖ ^ (2 : ℕ) ≤
      (L ^ Fintype.card ι) ^ (2 * ell) *
        (((((groupedDyadicUpper q) ^ ell : ℕ) : ℝ)) *
          (1 + Real.log ((((groupedDyadicUpper q) ^ ell : ℕ) : ℝ))) ^
            (2 ^ (2 * ((Fintype.card ι + 1) * ell)) - 1)) := by
  apply sum_normSq_convPow_le_fixed_polylog
    (one_le_groupedDyadicUpper q) (pow_nonneg hL _) _
  intro n
  have hnorm := norm_groupedDyadicProduct_le_divisors_mul_pow F q hL hfactor
    ((n : ℕ) + 1)
  have hnorm' : ‖groupedDyadicCoeffVector F q n‖ ≤
      (((((n : ℕ) + 1).divisors.card : ℝ) * L) ^ Fintype.card ι) := by
    simpa [groupedDyadicCoeffVector, complexCoeff_apply] using hnorm
  calc
    ‖groupedDyadicCoeffVector F q n‖
        ≤ ((((n : ℕ) + 1).divisors.card : ℝ) * L) ^ Fintype.card ι := hnorm'
    _ = L ^ Fintype.card ι *
        ((((n : ℕ) + 1).divisors.card : ℝ) ^ Fintype.card ι) := by
      rw [mul_pow]
      ring

/-- Literal Heath--Brown specialization: fixed block logarithms merge with the fixed divisor
moment into one explicit polylogarithmic energy factor. -/
theorem sum_normSq_convPow_heathBrownGrouped_le_fixed_polylog
    {ι : Type*} [Fintype ι] (ell : ℕ) (hell : 0 < ell)
    (L X : ℕ) (kind : ι → HeathBrownFactorKind) (q : ι → ℕ) :
    ∑ j : Fin ((groupedDyadicUpper q) ^ ell),
        ‖convPow (groupedDyadicUpper q) ell
          (groupedDyadicCoeffVector
            (fun i => heathBrownFactorBase L X (kind i)) q) j‖ ^ (2 : ℕ) ≤
      (((groupedDyadicUpper q) ^ ell : ℕ) : ℝ) *
        (1 + Real.log ((((groupedDyadicUpper q) ^ ell : ℕ) : ℝ))) ^
          (2 * (Fintype.card ι * ell) +
            (2 ^ (2 * ((Fintype.card ι + 1) * ell)) - 1)) := by
  let M : ℕ := groupedDyadicUpper q
  let Z : ℕ := M ^ ell
  let W : ℝ := 1 + Real.log (M : ℝ)
  let P : ℕ := 2 ^ (2 * ((Fintype.card ι + 1) * ell)) - 1
  have hM1 : 1 ≤ M := one_le_groupedDyadicUpper q
  have hW0 : 0 ≤ W := by
    dsimp [W]
    have hM1r : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
    have := Real.log_nonneg hM1r
    linarith
  have hfactor : ∀ i n,
      ‖arithmeticDyadicBlock (heathBrownFactorBase L X (kind i)) (q i) n‖ ≤ W :=
    norm_heathBrownGroupedFactorBlock_le L X kind q
  have hraw := sum_normSq_convPow_groupedDyadicCoeffVector_le_fixed_polylog
    (fun i => heathBrownFactorBase L X (kind i)) q hW0 hfactor ell
  have hMZnat : M ≤ Z := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ell ≠ 0)
    dsimp [Z]
    rw [pow_succ]
    have hk : 1 ≤ M ^ k := Nat.one_le_pow k M (by omega)
    simpa using Nat.mul_le_mul_right M hk
  have hMZ : (M : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hMZnat
  have hWZ : W ≤ 1 + Real.log (Z : ℝ) := by
    dsimp [W]
    simpa [add_comm] using
      (add_le_add_left (Real.log_le_log (by positivity) hMZ) 1)
  have hLZ0 : 0 ≤ 1 + Real.log (Z : ℝ) := hW0.trans hWZ
  have hWpow : W ^ (2 * (Fintype.card ι * ell)) ≤
      (1 + Real.log (Z : ℝ)) ^ (2 * (Fintype.card ι * ell)) :=
    pow_le_pow_left₀ hW0 hWZ _
  calc
    ∑ j : Fin ((groupedDyadicUpper q) ^ ell),
        ‖convPow (groupedDyadicUpper q) ell
          (groupedDyadicCoeffVector
            (fun i => heathBrownFactorBase L X (kind i)) q) j‖ ^ (2 : ℕ)
        ≤ (W ^ Fintype.card ι) ^ (2 * ell) *
          ((Z : ℝ) * (1 + Real.log (Z : ℝ)) ^ P) := by
            simpa [M, Z, W, P] using hraw
    _ = (Z : ℝ) *
          (W ^ (2 * (Fintype.card ι * ell)) *
            (1 + Real.log (Z : ℝ)) ^ P) := by
          rw [← pow_mul]
          rw [show Fintype.card ι * (2 * ell) =
            2 * (Fintype.card ι * ell) by ring]
          ring
    _ ≤ (Z : ℝ) *
          ((1 + Real.log (Z : ℝ)) ^ (2 * (Fintype.card ι * ell)) *
            (1 + Real.log (Z : ℝ)) ^ P) := by
          gcongr
    _ = (Z : ℝ) *
          (1 + Real.log (Z : ℝ)) ^
            (2 * (Fintype.card ι * ell) + P) := by
          rw [pow_add]
    _ = _ := rfl

end RHTower.Sieve
