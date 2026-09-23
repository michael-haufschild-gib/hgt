import GaloisForLFunctions.RHTower.Sieve.DyadicPrimeMeanSquare

/-!
# `(FS7)` in affine form

`Sieve/DyadicPrimeMeanSquare` bounds the mean square of a dyadic prime Dirichlet polynomial with a
free smoothing parameter `δ`.  The mixed-moment assembly of `Sieve/MixedMomentAssembly` consumes an
*affine* majorant `Q + κ·W` in the height, so the free parameter is eliminated here by the natural
choice `δ = 1/(2πW)`, `K = ⌈6Rδ⌉`.  The diagonal supplies `κ`, and the shifted prime pairs supply
both a constant and a linear part, because the shift range `K ≍ R/W` shrinks exactly as the height
grows.

This is the paper's step 4 in the shape its step 3 uses.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The constant part of the affine majorant. -/
def fs7Const (R h P₁ : ℕ) (z : ℝ) : ℝ :=
  60 * Real.exp 1 / (Real.exp (mertensS h - mertensS P₁)) ^ (2 : ℕ)
    + 15 * (∑ e ∈ (rangePrimorial P₁ h).divisors,
        (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0)) / (R : ℝ)

/-- The slope of the affine majorant. -/
def fs7Slope (R h P₁ : ℕ) (z : ℝ) : ℝ :=
  5 * Real.pi / 2 * (((bigPrimeSet R (2 * R)).card : ℝ) / (R : ℝ) ^ (2 : ℕ))
    + 20 * Real.pi * Real.exp 1 / ((R : ℝ) * (Real.exp (mertensS h - mertensS P₁)) ^ (2 : ℕ))
    + 5 * Real.pi * (∑ e ∈ (rangePrimorial P₁ h).divisors,
        (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0)) / (R : ℝ) ^ (2 : ℕ)

/-- **`(FS7)`, affine in the height.** -/
theorem integral_normSq_dyadicPrimePoly_affine {R h k P₁ : ℕ} {W z : ℝ}
    (hW : 1 ≤ W) (hhR : h ≤ R) (hR1 : 1 ≤ R)
    (hP₁ : 2 ≤ P₁) (hP₁h : P₁ ≤ h) (hh1 : 1 ≤ h) (hz : 1 ≤ z)
    (hlev : ((h : ℝ)) ^ (2 * k) ≤ z)
    (hk : Real.exp 1 * (∑ p ∈ rangePrimes P₁ h, 2 / ((p : ℝ) - 2)) + Real.log 2 ≤ (k : ℝ)) :
    (∫ w in Set.Icc (-W) W,
        ‖logPoly (fun n => ((1 : ℂ) / (n : ℂ))) (bigPrimeSet R (2 * R)) w‖ ^ (2 : ℕ))
      ≤ fs7Const R h P₁ z + fs7Slope R h P₁ z * W := by
  classical
  set δ : ℝ := 1 / (2 * Real.pi * W) with hδdef
  set Rem : ℝ := ∑ e ∈ (rangePrimorial P₁ h).divisors,
      (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0) with hRem
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hW0 : (0 : ℝ) < W := by linarith
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one (by positivity)]
    nlinarith [hW, hpi3]
  have hWδ : 2 * Real.pi * δ * W ≤ 1 := by
    rw [hδdef]
    field_simp
    exact le_rfl
  set K : ℕ := ⌈6 * (R : ℝ) * δ⌉₊ with hKdef
  have hK : 6 * (R : ℝ) * δ ≤ (K : ℝ) := Nat.le_ceil _
  have hR0 : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR1
  have hKle : (K : ℝ) ≤ 6 * (R : ℝ) * δ + 1 := by
    rw [hKdef]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hbase := integral_normSq_dyadicPrimePoly_le (R := R) (h := h) (K := K) (k := k) (P₁ := P₁)
    (δ := δ) (W := W) (z := z) hδ0 hδ1 hWδ hK hhR hR1 hP₁ hP₁h hh1 hz hlev hk
  refine le_trans hbase ?_
  -- the free parameter is now eliminated
  set E : ℝ := Real.exp (mertensS h - mertensS P₁) with hE
  have hE0 : (0 : ℝ) < E := Real.exp_pos _
  have hcard : (0 : ℝ) ≤ ((bigPrimeSet R (2 * R)).card : ℝ) := Nat.cast_nonneg _
  have hRem0 : (0 : ℝ) ≤ Rem := by
    refine Finset.sum_nonneg fun e _ => ?_
    split_ifs with hle
    · positivity
    · exact le_rfl
  have hinv : (5 : ℝ) / (4 * δ) = 5 * Real.pi * W / 2 := by
    rw [hδdef]
    field_simp
    ring
  rw [hinv, fs7Const, fs7Slope, ← hE, ← hRem]
  have hKW : (K : ℝ) * W ≤ 3 * (R : ℝ) / Real.pi + W := by
    have h1 : (K : ℝ) * W ≤ (6 * (R : ℝ) * δ + 1) * W :=
      mul_le_mul_of_nonneg_right hKle hW0.le
    have h2 : (6 * (R : ℝ) * δ) * W = 3 * (R : ℝ) / Real.pi := by
      rw [hδdef]
      field_simp
      ring
    nlinarith [h1, h2]
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  have hexp1 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  -- expand and compare termwise
  have hexpand : 5 * Real.pi * W / 2 * (1 / (R : ℝ) ^ (2 : ℕ))
        * (((bigPrimeSet R (2 * R)).card : ℝ)
          + 2 * (2 * Real.exp 1 * (K : ℝ) * (2 * (R : ℝ)) / E ^ (2 : ℕ) + (K : ℝ) * Rem))
      = 5 * Real.pi / 2 * (((bigPrimeSet R (2 * R)).card : ℝ) / (R : ℝ) ^ (2 : ℕ)) * W
        + 20 * Real.pi * Real.exp 1 * ((K : ℝ) * W) / ((R : ℝ) * E ^ (2 : ℕ))
        + 5 * Real.pi * Rem * ((K : ℝ) * W) / (R : ℝ) ^ (2 : ℕ) := by
    field_simp
    ring
  rw [hexpand]
  have hA : 20 * Real.pi * Real.exp 1 * ((K : ℝ) * W) / ((R : ℝ) * E ^ (2 : ℕ))
      ≤ 60 * Real.exp 1 / E ^ (2 : ℕ)
        + 20 * Real.pi * Real.exp 1 / ((R : ℝ) * E ^ (2 : ℕ)) * W := by
    have hc : (0 : ℝ) < 20 * Real.pi * Real.exp 1 / ((R : ℝ) * E ^ (2 : ℕ)) := by positivity
    have := mul_le_mul_of_nonneg_left hKW hc.le
    calc 20 * Real.pi * Real.exp 1 * ((K : ℝ) * W) / ((R : ℝ) * E ^ (2 : ℕ))
        = 20 * Real.pi * Real.exp 1 / ((R : ℝ) * E ^ (2 : ℕ)) * ((K : ℝ) * W) := by ring
      _ ≤ 20 * Real.pi * Real.exp 1 / ((R : ℝ) * E ^ (2 : ℕ)) * (3 * (R : ℝ) / Real.pi + W) := this
      _ = 60 * Real.exp 1 / E ^ (2 : ℕ) + 20 * Real.pi * Real.exp 1 / ((R : ℝ) * E ^ (2 : ℕ)) * W := by
          field_simp
          ring
  have hB : 5 * Real.pi * Rem * ((K : ℝ) * W) / (R : ℝ) ^ (2 : ℕ)
      ≤ 15 * Rem / (R : ℝ) + 5 * Real.pi * Rem / (R : ℝ) ^ (2 : ℕ) * W := by
    have hc : (0 : ℝ) ≤ 5 * Real.pi * Rem / (R : ℝ) ^ (2 : ℕ) := by positivity
    have := mul_le_mul_of_nonneg_left hKW hc
    calc 5 * Real.pi * Rem * ((K : ℝ) * W) / (R : ℝ) ^ (2 : ℕ)
        = 5 * Real.pi * Rem / (R : ℝ) ^ (2 : ℕ) * ((K : ℝ) * W) := by ring
      _ ≤ 5 * Real.pi * Rem / (R : ℝ) ^ (2 : ℕ) * (3 * (R : ℝ) / Real.pi + W) := this
      _ = 15 * Rem / (R : ℝ) + 5 * Real.pi * Rem / (R : ℝ) ^ (2 : ℕ) * W := by
          field_simp
          ring
  linarith [hA, hB]

end

end RHTower.Sieve
