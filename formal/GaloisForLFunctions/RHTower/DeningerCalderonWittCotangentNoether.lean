import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.CyclicCotangentNoether
import GaloisForLFunctions.RHTower.DeningerCalderonWittKoszulSource

/-!
# Fixed cotangent Noether law on the oriented Calderón--Witt source

A three-term arithmetic cochain complex has an algebraic total carrier on which its two
differentials combine to one square-zero endomorphism.  Cotangent doubling therefore gives that
total source a canonical cyclic Maurer--Cartan law.

The final construction specializes this generic fact to the zero-independent all-prime oriented
Calderón--Witt Koszul--Arakelov source.  It proves that a fixed arithmetic cyclic/Noether law already
exists before any Xi divisor is selected.  Consequently, existence of an action or annihilation of
its own gauge boundaries cannot be the RH-bearing input.  A future bridge must identify the fixed
Gamma-six physical reporter and its completed Xi Green event class with this same cotangent theory,
without changing the differential or dual coefficient system at the selected divisor.
-/

namespace RHTower

open HTGeometry.NomologicalHomotopyGeometry
open HTGeometry.NomologicalHomotopyGeometry.CyclicActionNoether
open HTGeometry.NomologicalHomotopyGeometry.CyclicCotangentNoether

noncomputable section

universe u v

section ThreeTermCotangent

variable {k : Type u} [Field k]
variable {A0 A1 A2 : Type v}
variable [AddCommGroup A0] [Module k A0]
variable [AddCommGroup A1] [Module k A1]
variable [AddCommGroup A2] [Module k A2]

/-- Algebraic total carrier of a three-term arithmetic cochain complex. -/
abbrev deningerThreeTermTotalCarrier := A0 × (A1 × A2)

/-- Total differential `d(a₀,a₁,a₂) = (0,d₀a₀,d₁a₁)`. -/
def deningerThreeTermTotalDifferential
    (C : DeningerArithmeticThreeTermComplex k A0 A1 A2) :
    Module.End k (deningerThreeTermTotalCarrier (A0 := A0) (A1 := A1) (A2 := A2)) where
  toFun x := (0, C.d0 x.1, C.d1 x.2.1)
  map_add' x y := by
    ext <;> simp
  map_smul' c x := by
    ext <;> simp

@[simp] theorem deningerThreeTermTotalDifferential_apply
    (C : DeningerArithmeticThreeTermComplex k A0 A1 A2)
    (x : deningerThreeTermTotalCarrier (A0 := A0) (A1 := A1) (A2 := A2)) :
    deningerThreeTermTotalDifferential C x =
      (0, C.d0 x.1, C.d1 x.2.1) :=
  rfl

/-- The total differential squares to zero exactly by the three-term chain law. -/
theorem deningerThreeTermTotalDifferential_sq
    (C : DeningerArithmeticThreeTermComplex k A0 A1 A2) :
    (deningerThreeTermTotalDifferential C).comp
        (deningerThreeTermTotalDifferential C) = 0 := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · simp
  · apply Prod.ext
    · simp
    · change C.d1 (C.d0 x.1) = 0
      exact LinearMap.congr_fun C.d1_comp_d0 x.1

variable [CharZero k]

/-- Canonical fixed cyclic cotangent law of any three-term arithmetic source. -/
def deningerThreeTermCotangentLaw
    (C : DeningerArithmeticThreeTermComplex k A0 A1 A2) :
    CyclicMaurerCartanLaw
      (k := k)
      (L := CotangentFields k
        (deningerThreeTermTotalCarrier (A0 := A0) (A1 := A1) (A2 := A2))) :=
  cotangentCyclicMaurerCartanLaw
    (deningerThreeTermTotalDifferential C)
    (deningerThreeTermTotalDifferential_sq C)

/-- Noether annihilation of every totalized three-term source boundary. -/
theorem deningerThreeTermCotangent_variationalForm_boundary
    (C : DeningerArithmeticThreeTermComplex k A0 A1 A2)
    (alpha epsilon : CotangentFields k
      (deningerThreeTermTotalCarrier (A0 := A0) (A1 := A1) (A2 := A2))) :
    variationalForm (deningerThreeTermCotangentLaw C) alpha
        (cotangentDifferential (deningerThreeTermTotalDifferential C) epsilon) = 0 := by
  exact cotangent_variationalForm_boundary
    (deningerThreeTermTotalDifferential C)
    (deningerThreeTermTotalDifferential_sq C) alpha epsilon

end ThreeTermCotangent

/-! ## Actual all-prime oriented Calderón--Witt source -/

/-- Total carrier of the fixed all-prime oriented Koszul--Arakelov source. -/
abbrev DeningerCalderonWittGlobalOrientedKoszulTotalCarrier :=
  deningerThreeTermTotalCarrier
    (A0 := DeningerCalderonWittGlobalDefectAxis)
    (A1 := DeningerCalderonWittAlgebraicGlobalDegreeOne)
    (A2 := DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ)

/-- Zero-independent total differential of the actual all-prime source. -/
def deningerCalderonWittGlobalOrientedKoszulTotalDifferential :
    Module.End ℂ DeningerCalderonWittGlobalOrientedKoszulTotalCarrier :=
  deningerThreeTermTotalDifferential
    deningerCalderonWittGlobalOrientedKoszulSourceComplex

theorem deningerCalderonWittGlobalOrientedKoszulTotalDifferential_sq :
    deningerCalderonWittGlobalOrientedKoszulTotalDifferential.comp
        deningerCalderonWittGlobalOrientedKoszulTotalDifferential = 0 :=
  deningerThreeTermTotalDifferential_sq
    deningerCalderonWittGlobalOrientedKoszulSourceComplex

/-- Fixed cyclic cotangent action on the actual all-prime oriented arithmetic source. -/
def deningerCalderonWittGlobalOrientedKoszulCotangentLaw :
    CyclicMaurerCartanLaw
      (k := ℂ)
      (L := CotangentFields ℂ
        DeningerCalderonWittGlobalOrientedKoszulTotalCarrier) :=
  deningerThreeTermCotangentLaw
    deningerCalderonWittGlobalOrientedKoszulSourceComplex

/-- The actual source law annihilates all of its fixed gauge boundaries before Xi selection. -/
theorem deningerCalderonWittGlobalOrientedKoszulCotangent_variationalForm_boundary
    (alpha epsilon : CotangentFields ℂ
      DeningerCalderonWittGlobalOrientedKoszulTotalCarrier) :
    variationalForm deningerCalderonWittGlobalOrientedKoszulCotangentLaw alpha
        (cotangentDifferential
          deningerCalderonWittGlobalOrientedKoszulTotalDifferential epsilon) = 0 := by
  exact deningerThreeTermCotangent_variationalForm_boundary
    deningerCalderonWittGlobalOrientedKoszulSourceComplex alpha epsilon

end

end RHTower
