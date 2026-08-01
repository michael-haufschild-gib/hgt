import GaloisForLFunctions.RHTower.DeningerSpecZCofiniteRecollement
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Data.Real.Basic

/-!
# The Arakelov boundary sheaf on `Spec ℤ`

The real boundary sheaf assigns the orientation line to every nonempty arithmetic open and the
zero group to the empty open.  Because every nonempty open of `Spec ℤ` contains the generic
point, that prescription is exactly the skyscraper sheaf at the generic point, so it is a sheaf
with identity restrictions between nonempty opens; in particular all its restrictions are
epimorphisms, i.e. it is flasque, and its global sections are the orientation line.

* `deningerArakelovBoundarySheaf` is the sheaf.
* `deningerArakelovBoundarySheaf_isFlasque` is flasqueness.
* `deningerArakelovBoundarySheaf_obj_of_nonempty` and
  `deningerArakelovBoundarySheaf_sections` compute its values.
-/

namespace RHTower

open CategoryTheory TopologicalSpace Opposite

section ArakelovSheaf

/-- The Zariski space of `Spec ℤ` as a bundled topological space. -/
abbrev DeningerSpecZ : TopCat := TopCat.of (PrimeSpectrum ℤ)

noncomputable local instance deningerSpecZGenericDec (U : Opens (PrimeSpectrum ℤ)) :
    Decidable (deningerSpecZGeneric ∈ U) := Classical.dec _

/-- **The Arakelov boundary sheaf.**  The skyscraper at the generic point of `Spec ℤ` with value
the real orientation line. -/
noncomputable def deningerArakelovBoundarySheaf :
    TopCat.Sheaf AddCommGrpCat.{0} DeningerSpecZ :=
  skyscraperSheaf (deningerSpecZGeneric : DeningerSpecZ) (AddCommGrpCat.of ℝ)

/-- **Flasqueness.**  Every restriction map of the Arakelov boundary sheaf is an epimorphism. -/
theorem deningerArakelovBoundarySheaf_isFlasque :
    deningerArakelovBoundarySheaf.IsFlasque :=
  isFlasque_skyscraperSheaf_of_hasZeroObject _ _

/-- On an open containing the generic point the sheaf takes the value of the orientation line. -/
theorem deningerArakelovBoundarySheaf_obj_of_mem {U : Opens (PrimeSpectrum ℤ)}
    (hU : deningerSpecZGeneric ∈ U) :
    deningerArakelovBoundarySheaf.obj.obj (op U) = AddCommGrpCat.of ℝ := by
  simp [deningerArakelovBoundarySheaf, hU]

/-- **Value on the arithmetic opens.**  Every nonempty open of `Spec ℤ` carries the orientation
line, because every nonempty open contains the generic point. -/
theorem deningerArakelovBoundarySheaf_obj_of_nonempty {U : Opens (PrimeSpectrum ℤ)}
    (hU : (U : Set (PrimeSpectrum ℤ)).Nonempty) :
    deningerArakelovBoundarySheaf.obj.obj (op U) = AddCommGrpCat.of ℝ :=
  deningerArakelovBoundarySheaf_obj_of_mem
    (deningerSpecZGeneric_mem_of_isOpen U.isOpen hU)

/-- **Global sections.**  `Γ(Spec ℤ, ℬ)` is the orientation line. -/
theorem deningerArakelovBoundarySheaf_sections :
    deningerArakelovBoundarySheaf.obj.obj (op ⊤) = AddCommGrpCat.of ℝ :=
  deningerArakelovBoundarySheaf_obj_of_mem (by trivial)

/-- The empty open carries the zero group. -/
theorem deningerArakelovBoundarySheaf_obj_empty :
    deningerArakelovBoundarySheaf.obj.obj (op ⊥) = ⊤_ AddCommGrpCat.{0} := by
  have h : deningerSpecZGeneric ∉ (⊥ : Opens (PrimeSpectrum ℤ)) := by simp
  simp [deningerArakelovBoundarySheaf, h]

/-- The orientation line is divisible, hence injective as an abelian group. -/
example : Injective (C := AddCommGrpCat.{0}) (AddCommGrpCat.of ℝ) := inferInstance

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **Injectivity.**  The Arakelov boundary sheaf is an injective object of the category of
abelian sheaves: it is the skyscraper of an injective abelian group, and the skyscraper functor
is right adjoint to the exact stalk functor. -/
instance deningerArakelovBoundarySheaf_injective :
    Injective deningerArakelovBoundarySheaf :=
  Adjunction.map_injective
    (stalkSkyscraperSheafAdjunction (X := DeningerSpecZ) (C := AddCommGrpCat.{0})
      deningerSpecZGeneric) _ inferInstance

/-- The Arakelov boundary sheaf viewed as an object of the sheaf category of the Zariski site,
which is the form in which mathlib states sheaf cohomology. -/
noncomputable def deningerArakelovBoundarySheafSite :
    CategoryTheory.Sheaf (Opens.grothendieckTopology (PrimeSpectrum ℤ)) AddCommGrpCat.{0} :=
  deningerArakelovBoundarySheaf

instance deningerArakelovBoundarySheafSite_injective :
    Injective deningerArakelovBoundarySheafSite :=
  deningerArakelovBoundarySheaf_injective

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **Acyclicity.**  All higher sheaf cohomology of the Arakelov boundary sheaf vanishes; with
`Sheaf.H.equiv₀` and `deningerArakelovBoundarySheaf_sections` this is `RΓ ≃ ℝ(-1)[0]`. -/
theorem deningerArakelovBoundarySheaf_higherCohomology (n : ℕ) :
    Subsingleton (Sheaf.H deningerArakelovBoundarySheafSite (n + 1)) := by
  infer_instance

end ArakelovSheaf

end RHTower
