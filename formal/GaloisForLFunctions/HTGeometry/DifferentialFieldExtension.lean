import GaloisForLFunctions.HTGeometry.DifferentialSystemSolution

/-!
# Differential field extensions, bundled

A differential field extension carries a field, a derivation, a structure map, and the statement
that the structure map is differential.  Bundling them makes an extension a value that can be
returned, composed, and iterated, which is what the construction of a differentially closed field
needs.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

universe u

/-- A differential field extension of a differential field, bundled with its structures. -/
structure DiffFieldExt (F : Type u) [Field F] [Algebra ℚ F] [Differential F] where
  /-- The extension field. -/
  carrier : Type u
  [field : Field carrier]
  [ratAlgebra : Algebra ℚ carrier]
  [differential : Differential carrier]
  [algebra : Algebra F carrier]
  /-- The structure map is differential. -/
  compat : ∀ a : F, Differential.deriv (algebraMap F carrier a)
    = algebraMap F carrier (Differential.deriv a)

attribute [instance] DiffFieldExt.field DiffFieldExt.ratAlgebra DiffFieldExt.differential
  DiffFieldExt.algebra

variable {F : Type u} [Field F] [Algebra ℚ F] [Differential F]

/-- The trivial extension. -/
def DiffFieldExt.refl : DiffFieldExt F where
  carrier := F
  compat := fun _ => rfl

/-- Extensions compose. -/
def DiffFieldExt.trans (E : DiffFieldExt F) (M : DiffFieldExt E.carrier) : DiffFieldExt F where
  carrier := M.carrier
  algebra := ((algebraMap E.carrier M.carrier).comp (algebraMap F E.carrier)).toAlgebra
  compat := fun a => by
    show Differential.deriv (algebraMap E.carrier M.carrier (algebraMap F E.carrier a))
      = algebraMap E.carrier M.carrier (algebraMap F E.carrier (Differential.deriv a))
    rw [M.compat, E.compat]

instance DiffFieldExt.differentialAlgebra (E : DiffFieldExt F) :
    DifferentialAlgebra F E.carrier := ⟨E.compat⟩

theorem DiffFieldExt.algebraMap_trans (E : DiffFieldExt F) (M : DiffFieldExt E.carrier) (a : F) :
    algebraMap F (E.trans M).carrier a
      = algebraMap E.carrier M.carrier (algebraMap F E.carrier a) := rfl


end

end GaloisForLFunctions.HTGeometry
