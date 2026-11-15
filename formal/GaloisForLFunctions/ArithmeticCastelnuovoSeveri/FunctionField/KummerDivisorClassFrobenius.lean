import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerPrincipalDivisorSaturation
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.ValuationPrincipalDivisors
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Data.Finsupp.Basic

/-!
# Characteristic torsion in actual place-divisor classes

Finite divisors use the normalization's finite places and its unique
place at infinity. Principal divisors are the normalized valuation logs
of nonzero functions. These are negatives of the usual principal
divisors and hence generate the same subgroup. Frobenius saturation
implies that their quotient has no characteristic-power torsion.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open IsDedekindDomain ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
    (c : (SquareConstantField p (kummerSquareIndex d n))ˣ)
local notation "s" => kummerSquareIndex d n
local notation "b" => p ^ (d + 1) - 2
local notation "R" => kummerExponent (p ^ (d + 1)) r
local notation "L" => SquareKummerField p s c b R
local notation "B" => SquareKummerNormalization p s c b R

/-- Finite divisors on the actual finite normalization places and the unique infinity place. -/
abbrev PrimePowerKummerPlaceDivisor := (HeightOneSpectrum B →₀ ℤ) × ℤ

/-- The complete finite place divisor of a function, with its infinity coefficient. -/
def primePowerKummerFunctionDivisor (f : L) : PrimePowerKummerPlaceDivisor p d n r c :=
  (finiteValuationDivisor B L f, WithZero.log (squareKummerInfinityValuation p s c d r f))

/-- Principal place divisors come from actual nonzero functions in the same function field. -/
def primePowerKummerPrincipalDivisors : AddSubgroup (PrimePowerKummerPlaceDivisor p d n r c) where
  carrier D := ∃ f : L, f ≠ 0 ∧
    (∀ v, WithZero.log (v.valuation L f) = D.1 v) ∧
      WithZero.log (squareKummerInfinityValuation p s c d r f) = D.2
  zero_mem' := ⟨1, one_ne_zero, fun v => by rw [map_one, WithZero.log_one]; rfl,
    by rw [map_one, WithZero.log_one]; rfl⟩
  add_mem' := by
    rintro D E ⟨f, hf, hfinite, hinfty⟩ ⟨g, hg, hfinite', hinfty'⟩
    refine ⟨f * g, mul_ne_zero hf hg, ?_, ?_⟩
    · intro v
      rw [map_mul, WithZero.log_mul ((map_ne_zero _).mpr hf) ((map_ne_zero _).mpr hg),
        hfinite, hfinite']
      rfl
    · rw [map_mul, WithZero.log_mul ((map_ne_zero _).mpr hf) ((map_ne_zero _).mpr hg),
        hinfty, hinfty']
      rfl
  neg_mem' := by
    rintro D ⟨f, hf, hfinite, hinfty⟩
    refine ⟨f⁻¹, inv_ne_zero hf, ?_, ?_⟩
    · intro v
      rw [map_inv₀, WithZero.log_inv, hfinite]
      rfl
    · rw [map_inv₀, WithZero.log_inv, hinfty]
      rfl

/-- Every nonzero function gives an actual finite principal divisor. -/
theorem primePowerKummerFunctionDivisor_mem (f : L) (hf : f ≠ 0) :
    primePowerKummerFunctionDivisor p d n r c f ∈ primePowerKummerPrincipalDivisors p d n r c :=
  ⟨f, hf, fun _ => rfl, rfl⟩

/-- Place-divisor classes are finite divisors modulo the principal divisors of actual functions. -/
abbrev PrimePowerKummerPlaceDivisorClass :=
  PrimePowerKummerPlaceDivisor p d n r c ⧸ primePowerKummerPrincipalDivisors p d n r c

/-- Multiplying a finite divisor by a characteristic power preserves and reflects principality. -/
theorem primePowerKummerPrincipalDivisors_nsmul_iff
    (e : ℕ) (D : PrimePowerKummerPlaceDivisor p d n r c) :
    (p ^ e) • D ∈ primePowerKummerPrincipalDivisors p d n r c ↔
      D ∈ primePowerKummerPrincipalDivisors p d n r c := by
  change (∃ f : L, f ≠ 0 ∧
    (∀ v, WithZero.log (v.valuation L f) = (p ^ e) • D.1 v) ∧
      WithZero.log (squareKummerInfinityValuation p s c d r f) = (p ^ e) • D.2) ↔ _
  simpa only [nsmul_eq_mul, Nat.cast_pow] using
    primePowerKummer_principal_orders_frobenius_saturated p d n r c e (fun v => D.1 v) D.2

/-- Actual place-divisor classes contain no nonzero element killed by a characteristic power. -/
theorem primePowerKummerPlaceDivisorClass_frobenius_torsion_iff
    (e : ℕ) (x : PrimePowerKummerPlaceDivisorClass p d n r c) :
    (p ^ e) • x = 0 ↔ x = 0 := by
  let P := primePowerKummerPrincipalDivisors p d n r c
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk'_surjective P x
  rw [← map_nsmul]
  change (((p ^ e) • D : PrimePowerKummerPlaceDivisor p d n r c) :
    PrimePowerKummerPlaceDivisorClass p d n r c) = 0 ↔
      (D : PrimePowerKummerPlaceDivisorClass p d n r c) = 0
  rw [QuotientAddGroup.eq_zero_iff, QuotientAddGroup.eq_zero_iff]
  exact primePowerKummerPrincipalDivisors_nsmul_iff p d n r c e D

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
