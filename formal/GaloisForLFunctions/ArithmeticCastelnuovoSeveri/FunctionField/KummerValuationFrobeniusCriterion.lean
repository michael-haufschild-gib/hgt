import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerCartierLogarithmic
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.ValuationLogarithmicDifferentials

/-!
# Frobenius powers detected by all valuation orders

For this prime-power Kummer family, a function is a `p`th power in the
same field exactly when every finite normalized valuation order and its
infinity order are divisible by `p`. Divisibility makes its logarithmic
differential regular everywhere; Cartier nilpotence then forces that
differential to vanish. This detects actual roots, not merely divisors.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open IsDedekindDomain ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
    (c : (SquareConstantField p (kummerSquareIndex d n))ˣ)
local notation "s" => kummerSquareIndex d n
local notation "K" => SquareConstantField p s
local notation "b" => p ^ (d + 1) - 2
local notation "R" => kummerExponent (p ^ (d + 1)) r
local notation "L" => SquareKummerField p s c b R
local notation "B" => SquareKummerNormalization p s c b R

/-- Actual Frobenius roots are characterized exactly by characteristic-divisible orders at all finite places and infinity. -/
theorem primePowerKummer_frobenius_iff_valuation_orders (f : L) :
    (∃ a : L, a ^ p = f) ↔
      (∀ v : HeightOneSpectrum B, (p : ℤ) ∣ WithZero.log (v.valuation L f)) ∧
        (p : ℤ) ∣ WithZero.log (squareKummerInfinityValuation p s c d r f) := by
  constructor
  · rintro ⟨a, rfl⟩
    constructor
    · intro v
      rw [map_pow, WithZero.log_pow, nsmul_eq_mul]
      exact ⟨WithZero.log (v.valuation L a), rfl⟩
    · rw [map_pow, WithZero.log_pow, nsmul_eq_mul]
      exact ⟨WithZero.log (squareKummerInfinityValuation p s c d r a), rfl⟩
  · rintro ⟨hfinite, hinfty⟩
    apply (primePowerKummer_logarithmic_regular_iff p d n r c f).mp
    rw [mem_globalRegularDifferentials_iff]
    intro W
    rcases squareKummer_constantPlace_cases p s c d r W with ⟨v, hv⟩ | hv
    · rw [← hv]
      exact valuation_logarithmic_mem_of_characteristic_dvd p (v.valuation L)
        (heightOne_constants_mem v) (placeUniformizer L v) (placeUniformizer_valuation L v)
        f (hfinite v)
    · rw [← hv]
      exact valuation_logarithmic_mem_of_characteristic_dvd p
        (squareKummerInfinityValuation p s c d r)
        (squareKummerInfinityConstantPlace p s c d r).property.2
        (squareKummerInfinityUniformizer p s c d r) (squareKummerInfinityUniformizer_value p s c d r)
        f hinfty

private theorem characteristic_power_dvd_cancel (e : ℕ) (a : ℤ)
    (h : (p : ℤ) ^ (e + 1) ∣ (p : ℤ) * a) : (p : ℤ) ^ e ∣ a := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t, mul_left_cancel₀ (show (p : ℤ) ≠ 0 by exact_mod_cast (Fact.out : p.Prime).ne_zero) ?_⟩
  calc
    (p : ℤ) * a = (p : ℤ) ^ (e + 1) * t := ht
    _ = (p : ℤ) * ((p : ℤ) ^ e * t) := by rw [pow_succ]; ring

/-- Every higher Frobenius root is detected exactly by divisibility of all normalized valuation orders. -/
theorem primePowerKummer_frobenius_pow_iff_valuation_orders (e : ℕ) (f : L) :
    (∃ a : L, a ^ (p ^ e) = f) ↔
      (∀ v : HeightOneSpectrum B, (p : ℤ) ^ e ∣ WithZero.log (v.valuation L f)) ∧
        (p : ℤ) ^ e ∣ WithZero.log (squareKummerInfinityValuation p s c d r f) := by
  induction e generalizing f with
  | zero => simp
  | succ e ih =>
    constructor
    · rintro ⟨a, rfl⟩
      constructor
      · intro v
        rw [map_pow, WithZero.log_pow, nsmul_eq_mul, Nat.cast_pow]
        exact ⟨WithZero.log (v.valuation L a), rfl⟩
      · rw [map_pow, WithZero.log_pow, nsmul_eq_mul, Nat.cast_pow]
        exact ⟨WithZero.log (squareKummerInfinityValuation p s c d r a), rfl⟩
    · rintro ⟨hfinite, hinfty⟩
      have hpdiv : (p : ℤ) ∣ (p : ℤ) ^ (e + 1) :=
        ⟨(p : ℤ) ^ e, by rw [pow_succ, mul_comm]⟩
      obtain ⟨a, ha⟩ := (primePowerKummer_frobenius_iff_valuation_orders p d n r c f).mpr
        ⟨fun v => hpdiv.trans (hfinite v), hpdiv.trans hinfty⟩
      have haorders :
          (∀ v : HeightOneSpectrum B, (p : ℤ) ^ e ∣ WithZero.log (v.valuation L a)) ∧
          (p : ℤ) ^ e ∣ WithZero.log (squareKummerInfinityValuation p s c d r a) := by
        constructor
        · intro v
          have h := hfinite v
          rw [← ha, map_pow, WithZero.log_pow, nsmul_eq_mul] at h
          exact characteristic_power_dvd_cancel p e _ h
        · rw [← ha, map_pow, WithZero.log_pow, nsmul_eq_mul] at hinfty
          exact characteristic_power_dvd_cancel p e _ hinfty
      obtain ⟨a', ha'⟩ := (ih a).mpr haorders
      refine ⟨a', ?_⟩
      calc
        a' ^ (p ^ (e + 1)) = (a' ^ (p ^ e)) ^ p :=
          (congrArg (fun j : ℕ => a' ^ j) (pow_succ p e)).trans
            (pow_mul a' (p ^ e) p)
        _ = f := by rw [ha', ha]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
