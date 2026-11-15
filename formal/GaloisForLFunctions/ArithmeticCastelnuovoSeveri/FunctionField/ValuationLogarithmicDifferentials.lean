import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.ValuationDifferentials
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerUniformizerDifferentials

/-!
# Local regularity of logarithmic differentials

A unit in a valuation ring has a regular logarithmic differential.
Multiplying a function by a Frobenius power leaves its logarithmic
differential unchanged. If its normalized valuation order is divisible
by the characteristic, a uniformizer Frobenius power makes it a unit.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.HTGeometry
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The logarithmic differential of a valuation-ring unit lies in its actual local Kähler image. -/
theorem valuation_logarithmic_mem_of_unit
    (W : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ W)
    (f : L) (hf : f ∈ W) (hfi : f⁻¹ ∈ W) :
    f⁻¹ • KaehlerDifferential.D K L f ∈ valuationLocalDifferentials W hK := by
  letI := valuationConstantAlgebra W hK
  let u : W := ⟨f, hf⟩
  let ui : W := ⟨f⁻¹, hfi⟩
  change ∃ ω, algHomKaehlerMap (valuationConstantInclusion W hK) ω = _
  refine ⟨ui • KaehlerDifferential.D K W u, ?_⟩
  rw [algHomKaehlerMap_smul, algHomKaehlerMap_D]
  rfl

/-- Multiplication by a nonzero Frobenius power preserves every logarithmic differential. -/
theorem logarithmic_differential_mul_frobenius
    (p : ℕ) [Fact p.Prime] [CharP L p] (f w : L) (hw : w ≠ 0) :
    (f * w ^ p)⁻¹ • KaehlerDifferential.D K L (f * w ^ p) =
      f⁻¹ • KaehlerDifferential.D K L f := by
  let D := KaehlerDifferential.D K L
  rw [D.leibniz, derivation_frobenius_power_eq_zero p D w, smul_zero, zero_add,
    mul_inv_rev, smul_smul, mul_right_comm, inv_mul_cancel₀ (pow_ne_zero _ hw), one_mul]

/-- Characteristic-divisible valuation order makes a logarithmic differential locally regular. -/
theorem valuation_logarithmic_mem_of_characteristic_dvd
    (p : ℕ) [Fact p.Prime] [CharP L p]
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (hK : ∀ a : K, algebraMap K L a ∈ v.valuationSubring)
    (π : L) (hπ : v π = WithZero.exp (-1 : ℤ))
    (f : L) (hf : (p : ℤ) ∣ WithZero.log (v f)) :
    f⁻¹ • KaehlerDifferential.D K L f ∈ valuationLocalDifferentials v.valuationSubring hK := by
  by_cases hf0 : f = 0
  · rw [hf0, inv_zero, zero_smul]
    exact Submodule.zero_mem _
  · obtain ⟨j, hj⟩ := hf
    have hvf : v f ≠ 0 := (map_ne_zero v).mpr hf0
    have hfexp : v f = WithZero.exp ((p : ℤ) * j) := by
      rw [← WithZero.exp_log hvf, hj]
    have hπ0 : π ≠ 0 := by
      intro h
      rw [h, map_zero] at hπ
      exact WithZero.exp_ne_zero hπ.symm
    let w := π ^ j
    have hw : w ≠ 0 := zpow_ne_zero j hπ0
    have hunit : v (f * w ^ p) = 1 := by
      change v (f * (π ^ j) ^ p) = 1
      rw [map_mul, map_pow, map_zpow₀, hπ, ← WithZero.exp_zsmul,
        ← WithZero.exp_nsmul, hfexp, ← WithZero.exp_add]
      have he : (p : ℤ) * j + p • (j • (-1 : ℤ)) = 0 := by
        simp only [nsmul_eq_mul, zsmul_eq_mul]
        ring
      rw [he, WithZero.exp_zero]
    have hu : f * w ^ p ∈ v.valuationSubring := by
      change v (f * w ^ p) ≤ 1
      rw [hunit]
    have hui : (f * w ^ p)⁻¹ ∈ v.valuationSubring := by
      change v ((f * w ^ p)⁻¹) ≤ 1
      rw [map_inv₀, hunit, inv_one]
    have hreg := valuation_logarithmic_mem_of_unit v.valuationSubring hK (f * w ^ p) hu hui
    rwa [logarithmic_differential_mul_frobenius p f w hw] at hreg

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
