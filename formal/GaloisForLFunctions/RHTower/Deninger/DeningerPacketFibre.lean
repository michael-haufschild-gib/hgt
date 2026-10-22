import GaloisForLFunctions.RHTower.Deninger.DeningerClassifyingFibration
import GaloisForLFunctions.RHTower.Deninger.DeningerClassifyingFibre
import GaloisForLFunctions.RHTower.Deninger.DeningerBaumslagRationalization

/-!
# The homotopy fibre of the packet's surjection

The packet's surjection of the rationalization of a free group onto a rational vector space induces
a map of classifying spaces which is a Kan fibration, whose fibre over the base point is the
classifying space of the kernel.  That classifying space has one connected component and its
fundamental group is the kernel, so the homotopy fibre is connected with fundamental group the
kernel.

* `deningerBauFreeMap_fibration` : the map of classifying spaces is a fibration.
* `deningerBauFreeMap_fibre` : its fibre is the classifying space of the kernel.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits SSet HomotopicalAlgebra SSet.modelCategoryQuillen

universe u

variable {ι A : Type u} [AddCommGroup A] [Module ℚ A]

/-- **The map of classifying spaces of the packet's surjection is a Kan fibration.** -/
theorem deningerBauFreeMap_fibration (b : ι → A)
    (hb : Submodule.span ℚ (Set.range b) = ⊤) :
    Fibration (deningerClassifyingMap (deningerBauFreeMap b)) :=
  deningerClassifyingMap_fibration (deningerBauFreeMap b) (deningerBauFree_surjective b hb)

/-- **The fibre of the packet's map of classifying spaces is the classifying space of the
kernel.** -/
noncomputable def deningerBauFreeMap_fibre (b : ι → A) :
    IsLimit (nerveFunctor.mapCone (deningerPtKerCone (deningerBauFreeMap b))) :=
  deningerClassifyingFibre_isLimit (deningerBauFreeMap b)

/-- **The homotopy category of that fibre is the one object category of the kernel**, so the fibre
is connected and its fundamental group is the kernel. -/
noncomputable def deningerBauFreeMap_fibre_ho (b : ι → A) :
    SSet.hoFunctor.obj (deningerClassifying (deningerBauFreeMap b).ker) ≅
      Cat.of (DeningerPt (deningerBauFreeMap b).ker) :=
  deningerClassifying_ho (deningerBauFreeMap b).ker

end RHTower
