import Mathlib.NumberTheory.NumberField.AdeleRing
import GaloisForLFunctions.RHTower.KRealCompactlySupportedLocallyConstant

/-!
# Real reflection on the rational finite-adele Bruhat factor

This file instantiates the generic compactly supported locally constant reflection on the
finite adele ring of `ℚ`. It supplies the finite local algebraic factor of the rational CCM
source involution.

Mathlib does not yet package the LF topology of this Bruhat function space, so continuity and
the restricted tensor-product comparison remain outside this leaf. No positivity, zero
spectrum, or Riemann-hypothesis premise occurs.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

/-- Rational finite adele ring in the `ℤ, ℚ` presentation. -/
abbrev CCMRationalFiniteAdele :=
  IsDedekindDomain.FiniteAdeleRing ℤ ℚ

/-- Compactly supported locally constant complex functions on rational finite adeles. -/
abbrev CCMRationalFiniteBruhatSchwartz :=
  compactlySupportedLocallyConstant CCMRationalFiniteAdele

/-- Rational finite-adele sign-reflection. -/
abbrev ccmRationalFiniteBruhatReflection :=
  compactlySupportedLocallyConstantReflection CCMRationalFiniteAdele

@[simp]
theorem ccmRationalFiniteBruhatReflection_apply
    (f : CCMRationalFiniteBruhatSchwartz)
    (x : CCMRationalFiniteAdele) :
    (ccmRationalFiniteBruhatReflection f).1 x =
      star (f.1 (-x)) :=
  compactlySupportedLocallyConstantReflection_apply
    CCMRationalFiniteAdele f x

/-- The rational finite-adele Bruhat reflection is an involution. -/
theorem ccmRationalFiniteBruhatReflection_sq
    (f : CCMRationalFiniteBruhatSchwartz) :
    ccmRationalFiniteBruhatReflection
      (ccmRationalFiniteBruhatReflection f) = f :=
  compactlySupportedLocallyConstantReflection_sq
    CCMRationalFiniteAdele f

/-- Even `KRealStructure` on the rational finite-adele Bruhat factor. -/
abbrev ccmRationalFiniteBruhatKRealEven :
    KRealStructure false CCMRationalFiniteBruhatSchwartz :=
  compactlySupportedLocallyConstantKRealEven CCMRationalFiniteAdele

end RHTower
end GaloisForLFunctions
