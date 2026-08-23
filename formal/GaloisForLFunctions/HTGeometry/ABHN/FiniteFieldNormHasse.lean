import GaloisForLFunctions.HTGeometry.HasseExactSequence
import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldArithmeticFrobenius

/-!
# Hasse quotients for the finite-field norm sequence

The arithmetic-Frobenius Hilbert--90 sequence gives two consecutive quotient classifications.
Extension units modulo Frobenius coboundaries are base units via the norm, while extension units
modulo base units are precisely the realized Frobenius-coboundary range.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Extension units modulo arithmetic-Frobenius coboundaries are base-field units via the norm. -/
noncomputable def finiteFieldArithmeticFrobeniusNormHasseQuotientEquiv
    (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] [Finite L] :
    (Additive Lˣ ⧸
      (cyclicGaloisAdditiveCoboundary (finiteFieldArithmeticFrobenius K L)).range) ≃+
        Additive Kˣ :=
  addHasseQuotientEquiv
    (cyclicGaloisAdditiveCoboundary (finiteFieldArithmeticFrobenius K L))
    (cyclicGaloisAdditiveNormUnits K L)
    (finiteFieldArithmeticFrobenius_normSequence K L).1
    (finiteFieldArithmeticFrobenius_normSequence K L).2

@[simp] theorem finiteFieldArithmeticFrobeniusNormHasseQuotientEquiv_mk
    (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] [Finite L]
    (x : Additive Lˣ) :
    finiteFieldArithmeticFrobeniusNormHasseQuotientEquiv K L
        (QuotientAddGroup.mk x) = cyclicGaloisAdditiveNormUnits K L x := by
  simp [finiteFieldArithmeticFrobeniusNormHasseQuotientEquiv]

/-- Two extension units have equal norm exactly when their difference is a Frobenius
coboundary. -/
theorem finiteFieldArithmeticFrobeniusNorm_congr_hasse_iff
    (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] [Finite L]
    (x y : Additive Lˣ) :
    x - y ∈
        (cyclicGaloisAdditiveCoboundary (finiteFieldArithmeticFrobenius K L)).range ↔
      cyclicGaloisAdditiveNormUnits K L x = cyclicGaloisAdditiveNormUnits K L y :=
  addHasse_congr_iff
    (cyclicGaloisAdditiveCoboundary (finiteFieldArithmeticFrobenius K L))
    (cyclicGaloisAdditiveNormUnits K L)
    (finiteFieldArithmeticFrobenius_normSequence K L).1 x y

/-- Every base-field unit is a norm, with its extension-unit lift unique modulo Frobenius
coboundaries. -/
theorem finiteFieldArithmeticFrobeniusNorm_exists_unique_mod_coboundary
    (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] [Finite L]
    (a : Additive Kˣ) :
    ∃ x : Additive Lˣ, cyclicGaloisAdditiveNormUnits K L x = a ∧
      ∀ y : Additive Lˣ, cyclicGaloisAdditiveNormUnits K L y = a ↔
        y - x ∈
          (cyclicGaloisAdditiveCoboundary (finiteFieldArithmeticFrobenius K L)).range :=
  addHasse_exists_unique_mod_global
    (cyclicGaloisAdditiveCoboundary (finiteFieldArithmeticFrobenius K L))
    (cyclicGaloisAdditiveNormUnits K L)
    (finiteFieldArithmeticFrobenius_normSequence K L).1
    (finiteFieldArithmeticFrobenius_normSequence K L).2 a

/-- Base units are exactly the kernel of the coboundary map restricted to its range. -/
theorem finiteFieldArithmeticFrobeniusBaseUnits_coboundaryRange_exact
    (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] [Finite L] :
    Function.Exact (cyclicGaloisBaseUnitsMap (K := K) (L := L))
      (cyclicGaloisAdditiveCoboundary
        (finiteFieldArithmeticFrobenius K L)).rangeRestrict := by
  intro x
  have h := finiteField_cyclicGaloisBaseUnits_coboundary_exact
    (finiteFieldArithmeticFrobenius_generates K L) x
  constructor
  · intro hx
    apply h.mp
    exact congrArg Subtype.val hx
  · intro hx
    apply Subtype.ext
    exact h.mpr hx

/-- Extension units modulo base-field units are the realized Frobenius-coboundary range. -/
noncomputable def finiteFieldArithmeticFrobeniusCoboundaryHasseQuotientEquiv
    (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] [Finite L] :
    (Additive Lˣ ⧸ (cyclicGaloisBaseUnitsMap (K := K) (L := L)).range) ≃+
      (cyclicGaloisAdditiveCoboundary
        (finiteFieldArithmeticFrobenius K L)).range :=
  addHasseQuotientEquiv
    (cyclicGaloisBaseUnitsMap (K := K) (L := L))
    (cyclicGaloisAdditiveCoboundary
      (finiteFieldArithmeticFrobenius K L)).rangeRestrict
    (finiteFieldArithmeticFrobeniusBaseUnits_coboundaryRange_exact K L)
    (AddMonoidHom.rangeRestrict_surjective _)

@[simp] theorem finiteFieldArithmeticFrobeniusCoboundaryHasseQuotientEquiv_mk
    (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] [Finite L]
    (x : Additive Lˣ) :
    finiteFieldArithmeticFrobeniusCoboundaryHasseQuotientEquiv K L
        (QuotientAddGroup.mk x) =
      (cyclicGaloisAdditiveCoboundary
        (finiteFieldArithmeticFrobenius K L)).rangeRestrict x := by
  simp [finiteFieldArithmeticFrobeniusCoboundaryHasseQuotientEquiv]

/-- Two extension units have equal Frobenius coboundary exactly when they differ by a base-field
unit. -/
theorem finiteFieldArithmeticFrobeniusCoboundary_congr_hasse_iff
    (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] [Finite L]
    (x y : Additive Lˣ) :
    x - y ∈ (cyclicGaloisBaseUnitsMap (K := K) (L := L)).range ↔
      cyclicGaloisAdditiveCoboundary (finiteFieldArithmeticFrobenius K L) x =
        cyclicGaloisAdditiveCoboundary (finiteFieldArithmeticFrobenius K L) y :=
  addHasse_congr_iff
    (cyclicGaloisBaseUnitsMap (K := K) (L := L))
    (cyclicGaloisAdditiveCoboundary (finiteFieldArithmeticFrobenius K L))
    (finiteField_cyclicGaloisBaseUnits_coboundary_exact
      (finiteFieldArithmeticFrobenius_generates K L)) x y

/-- Every realized Frobenius coboundary has an extension-unit representative, unique modulo
base-field units. -/
theorem finiteFieldArithmeticFrobeniusCoboundary_exists_unique_mod_baseUnits
    (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] [Finite L]
    (z : (cyclicGaloisAdditiveCoboundary
      (finiteFieldArithmeticFrobenius K L)).range) :
    ∃ x : Additive Lˣ,
      (cyclicGaloisAdditiveCoboundary
        (finiteFieldArithmeticFrobenius K L)).rangeRestrict x = z ∧
      ∀ y : Additive Lˣ,
        (cyclicGaloisAdditiveCoboundary
          (finiteFieldArithmeticFrobenius K L)).rangeRestrict y = z ↔
          y - x ∈ (cyclicGaloisBaseUnitsMap (K := K) (L := L)).range :=
  addHasse_exists_unique_mod_global
    (cyclicGaloisBaseUnitsMap (K := K) (L := L))
    (cyclicGaloisAdditiveCoboundary
      (finiteFieldArithmeticFrobenius K L)).rangeRestrict
    (finiteFieldArithmeticFrobeniusBaseUnits_coboundaryRange_exact K L)
    (AddMonoidHom.rangeRestrict_surjective _) z

end
end GaloisForLFunctions.HTGeometry.ABHN
