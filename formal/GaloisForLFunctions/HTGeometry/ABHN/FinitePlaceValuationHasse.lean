import GaloisForLFunctions.HTGeometry.ABHN.LocalValuationSequence

/-!
# Hasse classification at a finite Dedekind place

At every height-one place of a Dedekind domain, the associated discrete valuation classifies
nonzero fraction-field elements modulo valuation-zero units.  This is the algebraic finite-place
version of the completed nonarchimedean local-field classification.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v

open IsDedekindDomain

/-- The finite-place valuation quotient equivalence is induced by the place valuation. -/
@[simp] theorem finitePlaceQuotientKerValuationEquiv_mk
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    (L : Type v) [Field L] [Algebra R L] [IsFractionRing R L]
    (p : HeightOneSpectrum R) (x : Lˣ) :
    finitePlaceQuotientKerValuationEquiv L p (QuotientGroup.mk x) =
      (residueDataAtPlace L p).val x := by
  rfl

/-- Two fraction-field elements have equal value at a finite place exactly when their quotient is
a valuation-zero unit there. -/
theorem finitePlaceValuation_congr_hasse_iff
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    (L : Type v) [Field L] [Algebra R L] [IsFractionRing R L]
    (p : HeightOneSpectrum R) (x y : Lˣ) :
    x * y⁻¹ ∈ (residueDataAtPlace L p).val.ker ↔
      (residueDataAtPlace L p).val x = (residueDataAtPlace L p).val y := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]

/-- Every integer value at a finite Dedekind place is realized, uniquely modulo valuation-zero
units. -/
theorem finitePlaceValuation_exists_unique_mod_kernel
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    (L : Type v) [Field L] [Algebra R L] [IsFractionRing R L]
    (p : HeightOneSpectrum R) (n : Multiplicative ℤ) :
    ∃ x : Lˣ,
      (residueDataAtPlace L p).val x = n ∧
      ∀ y : Lˣ,
        (residueDataAtPlace L p).val y = n ↔
          y * x⁻¹ ∈ (residueDataAtPlace L p).val.ker := by
  obtain ⟨x, hx⟩ := finitePlaceValuation_surjective L p n
  refine ⟨x, hx, fun y => ?_⟩
  rw [finitePlaceValuation_congr_hasse_iff L p y x, hx]

end GaloisForLFunctions.HTGeometry.ABHN
