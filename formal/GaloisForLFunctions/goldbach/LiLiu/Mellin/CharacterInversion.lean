import GaloisForLFunctions.goldbach.LiLiu.Mellin.CharacterContour
import GaloisForLFunctions.goldbach.LiLiu.Mellin.DirichletInversion
import GaloisForLFunctions.goldbach.LiLiu.FiniteProjection
import GaloisForLFunctions.RHTower.SelbergKloostermanCongruence

/-! # The Mellin integral of the odd character polynomial -/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex ArithmeticFunction MeasureTheory Finset
open MetaplecticMobiusDescent.CubicEisenstein
open scoped Classical
noncomputable section

/-- The twist of the von Mangoldt coefficients by the actual character. -/
def twistedMangoldt {N : ℕ} (χ : DirichletCharacter ℂ N) (k : ℕ) : ℂ :=
  χ (k : ZMod N) * (Λ k : ℂ)

private theorem companion_sample {N k : ℕ} (hN : 0 < N) (hk : 0 < k) (φ : TestWeight) :
    (k : ℂ)^(-(1/2 : ℂ)) * companion φ ((k : ℝ)/N) =
      (φ ((k : ℝ)/N) : ℂ) / (Real.sqrt N : ℂ) := by
  have hh : (k : ℂ) ^ (1/2 : ℂ) = (Real.sqrt k : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg k)]
    push_cast
    rfl
  rw [Complex.cpow_neg, hh, companion, Vstar, Real.sqrt_div (Nat.cast_nonneg k), Complex.ofReal_div]
  field_simp [Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk)).ne',
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)).ne']

private theorem weighted_samples_eq_units (n : ℕ) (φ : TestWeight) (χ : DirichletCharacter ℂ (n+1)) :
    (∑' k : ℕ, (twistedMangoldt χ k * (k : ℂ)^(-(1/2 : ℂ))) * companion φ ((k : ℝ)/(n+1 : ℕ))) =
      unitCharacterSum n (fun u => (coefficient φ (n+1) (u : ZMod (n+1)).val : ℂ)) χ / (Real.sqrt (n+1 : ℕ) : ℂ) := by
  let N := n+1
  have hN : 0 < N := Nat.succ_pos n
  have hx (k : ℕ) : (twistedMangoldt χ k * (k : ℂ)^(-(1/2 : ℂ))) * companion φ ((k : ℝ)/N) =
      (coefficient φ N k : ℂ) * χ (k : ZMod N) / (Real.sqrt N : ℂ) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [twistedMangoldt, coefficient]
    rw [mul_assoc, companion_sample hN hk]
    simp only [twistedMangoldt, coefficient, Complex.ofReal_mul]
    ring
  simp_rw [hx]
  rw [tsum_eq_sum (s := range N)]
  · rw [← Finset.sum_div, unitCharacterSum, ← RHTower.SelbergKloostermanCongruence.sum_range_units N
      (fun u => (coefficient φ N u.val : ℂ) * χ u)]
    congr 1
    apply sum_congr rfl
    intro k hk
    rw [ZMod.val_natCast_of_lt (mem_range.mp hk)]
    by_cases hu : IsUnit (k : ZMod N)
    · rw [if_pos hu]
    · simp [hu, χ.map_nonunit hu]
  · intro k hk
    have hkN : N ≤ k := Nat.le_of_not_gt fun h => hk (mem_range.mpr h)
    have hφ : φ ((k : ℝ)/N) = 0 := by
      by_contra hn
      have hb := (φ.supported hn).2
      have h1 : 1 ≤ (k : ℝ)/N := (one_le_div (Nat.cast_pos.mpr hN)).mpr (by exact_mod_cast hkN)
      linarith only [hb,h1]
    simp [coefficient, hφ]

private theorem twisted_LSeries_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < (1/2+s : ℂ).re) :
    LSeries (twistedMangoldt χ) (1/2+s) = -characterFeature χ s := by
  rw [characterFeature, logDeriv, χ.deriv_LFunction_eq_deriv_LSeries hs, χ.LFunction_eq_LSeries hs,
    ← neg_div]
  exact χ.LSeries_twist_vonMangoldt_eq hs

/-- Formula (7.2) with the finite unit polynomial and its factor 1/√N. -/
theorem character_polynomial_integral {n : ℕ} (φ : TestWeight) (h : modulusGRH (n+1))
    {χ : DirichletCharacter ℂ (n+1)} (hχ : χ ≠ 1) {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1) :
    unitCharacterSum n (fun u => (coefficient φ (n+1) (u : ZMod (n+1)).val : ℂ)) χ / (Real.sqrt (n+1 : ℕ) : ℂ) =
      -(1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, characterIntegrand φ χ ((a : ℂ)+t*I) := by
  rw [character_contour_shift φ h hχ ha ha']
  have hinv := companion_LSeries_inversion φ (twistedMangoldt χ) (by simp [twistedMangoldt])
    (Nat.succ_pos n) (1/2) 1 (χ.LSeriesSummable_twist_vonMangoldt (by norm_num))
  push_cast at hinv
  rw [weighted_samples_eq_units] at hinv
  rw [← hinv, neg_mul, ← mul_neg, ← integral_neg]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [show (1/2:ℂ) + 1 + t*I = 1/2 + (1+t*I) by ring, twisted_LSeries_eq χ (by norm_num)]
  unfold characterIntegrand
  ring

#print axioms character_polynomial_integral
end
end GaloisForLFunctions.Goldbach.LiLiu
