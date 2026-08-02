import GaloisForLFunctions.HTGeometry.RelativeContractionTransgressionLaw
import GaloisForLFunctions.RHTower.DeningerCalderonWittMilnorIncidence

/-!
# Relative boundary transgression of the Calderón--Witt source

The algebraic Calderón--Witt Milnor complex is contractible.  Consequently
an exterior cocycle cannot carry an absolute source-cohomology class.  After
restricting the admitted incidence primitives to a sector `S`, its complete
remaining invariant is the Green primitive modulo `S`.

This file specializes the general relative-contraction law to both the
one-prime and all-prime arithmetic sources.  It gives a necessity-and-
sufficiency theorem: the relative class vanishes exactly when the canonical
Green contraction preserves the admitted sector.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-! ## One-prime relative class -/

/--
Relative class of a local exterior source cocycle after restricting its
admitted Milnor-incidence primitives to `S`.
-/
def deningerCalderonWittRelativeBoundaryClass
    (p : Nat.Primes)
    (S : Submodule ℂ (deningerCalderonWittMilnorIncidence p))
    (w : ⋀[ℂ]^2 (DeningerCalderonWittAlgebraicDegreeOne p)) :=
  relativePrimitiveObstruction
    (R := ℂ)
    (A0 := deningerCalderonWittMilnorIncidence p)
    (A1 := ⋀[ℂ]^2 (DeningerCalderonWittAlgebraicDegreeOne p))
    S
    (deningerCalderonWittMilnorIncidence p).subtype
    (deningerCalderonWittMilnorGreenRetraction p)
    w

/--
**Local acyclic-source boundary-transgression law.**  For a local exterior
cocycle, the relative boundary class vanishes exactly when its canonical
Green primitive belongs to the admitted incidence sector.
-/
theorem deningerCalderonWittRelativeBoundaryClass_eq_zero_iff
    (p : Nat.Primes)
    (S : Submodule ℂ (deningerCalderonWittMilnorIncidence p))
    (w : ⋀[ℂ]^2 (DeningerCalderonWittAlgebraicDegreeOne p))
    (hcocycle : deningerCalderonWittAlgebraicExteriorCup p w = 0) :
    deningerCalderonWittRelativeBoundaryClass p S w = 0 ↔
      deningerCalderonWittMilnorGreenRetraction p w ∈ S := by
  simpa [deningerCalderonWittRelativeBoundaryClass] using
    (contractedCocycle_relativePrimitiveObstruction_eq_zero_iff_of_injective
      (R := ℂ)
      (A0 := deningerCalderonWittMilnorIncidence p)
      (A1 := ⋀[ℂ]^2 (DeningerCalderonWittAlgebraicDegreeOne p))
      (A2 := DeningerCalderonWittAlgebraicDegreeTwo p)
      (S0 := S)
      (d0 := (deningerCalderonWittMilnorIncidence p).subtype)
      (d1 := deningerCalderonWittAlgebraicExteriorCup p)
      (h1 := deningerCalderonWittMilnorGreenRetraction p)
      (h2 := deningerCalderonWittExteriorCupSection p)
      (hcontract := deningerCalderonWittMilnorGreenContraction_middle p)
      (hinjective :=
        (deningerCalderonWittMilnorIncidence p).subtype_injective)
      (x := w)
      hcocycle)

/--
Equivalent local existence form: vanishing means precisely that the exterior
cocycle has an incidence primitive in the admitted sector.
-/
theorem deningerCalderonWittRelativeBoundaryClass_eq_zero_iff_exists
    (p : Nat.Primes)
    (S : Submodule ℂ (deningerCalderonWittMilnorIncidence p))
    (w : ⋀[ℂ]^2 (DeningerCalderonWittAlgebraicDegreeOne p))
    (hcocycle : deningerCalderonWittAlgebraicExteriorCup p w = 0) :
    deningerCalderonWittRelativeBoundaryClass p S w = 0 ↔
      ∃ i : deningerCalderonWittMilnorIncidence p,
        i ∈ S ∧
          (deningerCalderonWittMilnorIncidence p).subtype i = w := by
  simpa [deningerCalderonWittRelativeBoundaryClass] using
    (contractedCocycle_relativePrimitiveObstruction_eq_zero_iff
      (R := ℂ)
      (A0 := deningerCalderonWittMilnorIncidence p)
      (A1 := ⋀[ℂ]^2 (DeningerCalderonWittAlgebraicDegreeOne p))
      (A2 := DeningerCalderonWittAlgebraicDegreeTwo p)
      (S0 := S)
      (d0 := (deningerCalderonWittMilnorIncidence p).subtype)
      (d1 := deningerCalderonWittAlgebraicExteriorCup p)
      (h1 := deningerCalderonWittMilnorGreenRetraction p)
      (h2 := deningerCalderonWittExteriorCupSection p)
      (hcontract := deningerCalderonWittMilnorGreenContraction_middle p)
      (x := w)
      hcocycle)

/-! ## All-prime relative class -/

/--
Relative class of an all-prime finite-support exterior cocycle after
restricting its admitted global Milnor-incidence primitives to `S`.
-/
def deningerCalderonWittGlobalRelativeBoundaryClass
    (S : Submodule ℂ deningerCalderonWittGlobalMilnorIncidence)
    (w : ⋀[ℂ]^2 DeningerCalderonWittAlgebraicGlobalDegreeOne) :=
  relativePrimitiveObstruction
    (R := ℂ)
    (A0 := deningerCalderonWittGlobalMilnorIncidence)
    (A1 := ⋀[ℂ]^2 DeningerCalderonWittAlgebraicGlobalDegreeOne)
    S
    deningerCalderonWittGlobalMilnorIncidence.subtype
    deningerCalderonWittGlobalMilnorGreenRetraction
    w

/--
**All-prime acyclic-source boundary-transgression law.**  For an all-prime
exterior cocycle, its relative class vanishes exactly when the canonical
global Green primitive remains in the admitted incidence sector.
-/
theorem deningerCalderonWittGlobalRelativeBoundaryClass_eq_zero_iff
    (S : Submodule ℂ deningerCalderonWittGlobalMilnorIncidence)
    (w : ⋀[ℂ]^2 DeningerCalderonWittAlgebraicGlobalDegreeOne)
    (hcocycle : deningerCalderonWittAlgebraicGlobalExteriorCup w = 0) :
    deningerCalderonWittGlobalRelativeBoundaryClass S w = 0 ↔
      deningerCalderonWittGlobalMilnorGreenRetraction w ∈ S := by
  simpa [deningerCalderonWittGlobalRelativeBoundaryClass] using
    (contractedCocycle_relativePrimitiveObstruction_eq_zero_iff_of_injective
      (R := ℂ)
      (A0 := deningerCalderonWittGlobalMilnorIncidence)
      (A1 := ⋀[ℂ]^2 DeningerCalderonWittAlgebraicGlobalDegreeOne)
      (A2 := DeningerCalderonWittAlgebraicGlobalDegreeTwo)
      (S0 := S)
      (d0 := deningerCalderonWittGlobalMilnorIncidence.subtype)
      (d1 := deningerCalderonWittAlgebraicGlobalExteriorCup)
      (h1 := deningerCalderonWittGlobalMilnorGreenRetraction)
      (h2 := deningerCalderonWittGlobalExteriorCupSection)
      (hcontract := deningerCalderonWittGlobalMilnorGreenContraction_middle)
      (hinjective :=
        deningerCalderonWittGlobalMilnorIncidence.subtype_injective)
      (x := w)
      hcocycle)

/--
Equivalent all-prime existence form: the relative class vanishes precisely
when the global exterior cocycle has a primitive in the admitted sector.
-/
theorem deningerCalderonWittGlobalRelativeBoundaryClass_eq_zero_iff_exists
    (S : Submodule ℂ deningerCalderonWittGlobalMilnorIncidence)
    (w : ⋀[ℂ]^2 DeningerCalderonWittAlgebraicGlobalDegreeOne)
    (hcocycle : deningerCalderonWittAlgebraicGlobalExteriorCup w = 0) :
    deningerCalderonWittGlobalRelativeBoundaryClass S w = 0 ↔
      ∃ i : deningerCalderonWittGlobalMilnorIncidence,
        i ∈ S ∧
          deningerCalderonWittGlobalMilnorIncidence.subtype i = w := by
  simpa [deningerCalderonWittGlobalRelativeBoundaryClass] using
    (contractedCocycle_relativePrimitiveObstruction_eq_zero_iff
      (R := ℂ)
      (A0 := deningerCalderonWittGlobalMilnorIncidence)
      (A1 := ⋀[ℂ]^2 DeningerCalderonWittAlgebraicGlobalDegreeOne)
      (A2 := DeningerCalderonWittAlgebraicGlobalDegreeTwo)
      (S0 := S)
      (d0 := deningerCalderonWittGlobalMilnorIncidence.subtype)
      (d1 := deningerCalderonWittAlgebraicGlobalExteriorCup)
      (h1 := deningerCalderonWittGlobalMilnorGreenRetraction)
      (h2 := deningerCalderonWittGlobalExteriorCupSection)
      (hcontract := deningerCalderonWittGlobalMilnorGreenContraction_middle)
      (x := w)
      hcocycle)

end

end RHTower
