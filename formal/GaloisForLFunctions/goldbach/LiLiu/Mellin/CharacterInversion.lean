import GaloisForLFunctions.goldbach.LiLiu.Mellin.CharacterContour
import GaloisForLFunctions.goldbach.LiLiu.Mellin.DirichletInversion
import GaloisForLFunctions.goldbach.LiLiu.Arithmetic.UnitSamples

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

private theorem character_sample {N : ℕ} [NeZero N] (φ : TestWeight)
    (χ : DirichletCharacter ℂ N) (k : ℕ) :
    (twistedMangoldt χ k * (k:ℂ)^(-(1/2:ℂ))) * companion φ ((k:ℝ)/N) =
      (coefficient φ N k : ℂ) * χ (k : ZMod N) / (Real.sqrt N : ℂ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [twistedMangoldt,coefficient]
  rw [mul_assoc,companion_sample (NeZero.pos N) hk]
  simp only [twistedMangoldt,coefficient,Complex.ofReal_mul]
  ring

/-- A Dirichlet character vanishes on nonunits, and the supported weight
only samples representatives strictly below the modulus. -/
private theorem weighted_samples_eq_units (n : ℕ) (φ : TestWeight) (χ : DirichletCharacter ℂ (n+1)) :
    (∑' k : ℕ, (twistedMangoldt χ k * (k:ℂ)^(-(1/2:ℂ))) * companion φ ((k:ℝ)/(n+1:ℕ))) =
      unitCharacterSum n (fun u => (coefficient φ (n+1) (u : ZMod (n+1)).val : ℂ)) χ /
        (Real.sqrt (n+1:ℕ) : ℂ) := by
  let f (k : ℕ) := (coefficient φ (n+1) k : ℂ) * χ (k : ZMod (n+1)) / (Real.sqrt (n+1:ℕ) : ℂ)
  have hf (k : ℕ) (hk : n+1 ≤ k) : f k=0 := by
    simp only [f,coefficient,weight_sample_zero (Nat.succ_pos n) hk φ,mul_zero,
      Complex.ofReal_zero,zero_mul,zero_div]
  have he (k : ℕ) : f k = if k.Coprime (n+1) then f k else 0 := by
    split_ifs with h
    · rfl
    · have hn : ¬ IsUnit (k : ZMod (n+1)) := fun hu => h ((ZMod.isUnit_iff_coprime k (n+1)).mp hu)
      simp only [f,χ.map_nonunit hn,mul_zero,zero_div]
  calc
    _ = ∑' k : ℕ, f k := tsum_congr (character_sample φ χ)
    _ = ∑' k : ℕ, if k.Coprime (n+1) then f k else 0 := tsum_congr he
    _ = ∑ u : (ZMod (n+1))ˣ, f (u : ZMod (n+1)).val := tsum_coprime_eq_sum_units (n+1) f hf
    _ = _ := by simp only [f,unitCharacterSum,Finset.sum_div,ZMod.natCast_zmod_val]

private theorem twisted_LSeries_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < (1/2+s : ℂ).re) :
    LSeries (twistedMangoldt χ) (1/2+s) = -characterFeature χ s := by
  change LSeries (twistedMangoldt χ) (1/2+s) = -(deriv χ.LFunction (1/2+s) / χ.LFunction (1/2+s))
  rw [χ.deriv_LFunction_eq_deriv_LSeries hs, χ.LFunction_eq_LSeries hs,
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
  simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] at hinv
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
