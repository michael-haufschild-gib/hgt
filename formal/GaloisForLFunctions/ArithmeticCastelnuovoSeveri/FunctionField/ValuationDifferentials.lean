import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerPlaceClassification
import GaloisForLFunctions.HTGeometry.KaehlerAlgHomGenericVanishing

/-!
# Regular differentials at valuation places

The local regular differential space is the image of the valuation ring's
Kähler module in the function field's Kähler module. Intersecting these
images over all proper constant-field places defines global regularity.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The constant algebra structure on a valuation ring containing the constants. -/
@[reducible] def valuationConstantAlgebra
    (W : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ W) : Algebra K W :=
  (valuationConstantHom W hK).toAlgebra

/-- Inclusion of a constant-field valuation ring is an algebra homomorphism. -/
def valuationConstantInclusion
    (W : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ W) :
    letI := valuationConstantAlgebra W hK
    W →ₐ[K] L := by
  letI := valuationConstantAlgebra W hK
  exact { W.subtype with commutes' := fun _ => rfl }

/-- Differentials regular at a valuation ring are the image of its actual Kähler module. -/
def valuationLocalDifferentials
    (W : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ W) :
    Submodule K (KaehlerDifferential K L) := by
  letI := valuationConstantAlgebra W hK
  exact LinearMap.range (algHomKaehlerMap (valuationConstantInclusion W hK))

/-- Globally regular differentials are regular at every proper constant-field valuation ring. -/
def globalRegularDifferentials (K L : Type*) [Field K] [Field L] [Algebra K L] :
    Submodule K (KaehlerDifferential K L) :=
  ⨅ W : ConstantFieldPlaces K L, valuationLocalDifferentials W.val W.property.2

/-- Global regularity is the simultaneous local Kähler-image condition. -/
theorem mem_globalRegularDifferentials_iff (ω : KaehlerDifferential K L) :
    ω ∈ globalRegularDifferentials K L ↔
      ∀ W : ConstantFieldPlaces K L, ω ∈ valuationLocalDifferentials W.val W.property.2 := by
  exact Submodule.mem_iInf

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
