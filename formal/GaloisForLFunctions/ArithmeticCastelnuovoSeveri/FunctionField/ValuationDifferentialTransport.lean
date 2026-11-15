import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.ValuationDifferentials
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.IntrinsicPlaceEquivalences

/-!
# Transport of regular differentials by field isomorphisms

A constant-field isomorphism pulls proper valuation rings back to proper
valuation rings. Functoriality of Kähler differentials transports each
local image, so it transports global regularity.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.HTGeometry
variable {K L L' : Type*} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']

/-- Kähler pullback takes a differential regular on the pulled-back valuation ring to one regular on the original ring. -/
theorem valuationLocalDifferentials_map_equiv
    (σ : L ≃ₐ[K] L') (W : ValuationSubring L')
    (hK : ∀ a : K, algebraMap K L' a ∈ W)
    (ω : KaehlerDifferential K L)
    (hω : ω ∈ valuationLocalDifferentials (W.comap σ.toRingHom)
      (fun a => show σ (algebraMap K L a) ∈ W by rw [σ.commutes]; exact hK a)) :
    algHomKaehlerMap σ.toAlgHom ω ∈ valuationLocalDifferentials W hK := by
  let W' := W.comap σ.toRingHom
  have hK' : ∀ a : K, algebraMap K L a ∈ W' := by
    intro a
    change σ (algebraMap K L a) ∈ W
    rw [σ.commutes]
    exact hK a
  letI := valuationConstantAlgebra W hK
  letI := valuationConstantAlgebra W' hK'
  let f : W' →ₐ[K] W := {
    (valuationComapRingEquiv σ.toRingEquiv W).toRingHom with
    commutes' := fun a => Subtype.ext (σ.commutes a) }
  change ∃ η : KaehlerDifferential K W',
    algHomKaehlerMap (valuationConstantInclusion W' hK') η = ω at hω
  obtain ⟨η, hη⟩ := hω
  change ∃ ξ : KaehlerDifferential K W,
    algHomKaehlerMap (valuationConstantInclusion W hK) ξ = algHomKaehlerMap σ.toAlgHom ω
  refine ⟨algHomKaehlerMap f η, ?_⟩
  rw [← algHomKaehlerMap_comp]
  have hcomp : (valuationConstantInclusion W hK).comp f =
      σ.toAlgHom.comp (valuationConstantInclusion W' hK') := by
    ext x
    rfl
  rw [hcomp, algHomKaehlerMap_comp, hη]

/-- Every constant-field isomorphism transports the intrinsic global regular differential space. -/
theorem globalRegularDifferentials_map_equiv
    (σ : L ≃ₐ[K] L') (ω : KaehlerDifferential K L)
    (hω : ω ∈ globalRegularDifferentials K L) :
    algHomKaehlerMap σ.toAlgHom ω ∈ globalRegularDifferentials K L' := by
  rw [mem_globalRegularDifferentials_iff] at hω ⊢
  intro W
  exact valuationLocalDifferentials_map_equiv σ W.val W.property.2 ω
    (hω (constantFieldPlaceComap σ W))


/-- Every constant automorphism preserves the intrinsic global regular differential space. -/
theorem globalRegularDifferentials_stable_aut
    (σ : L ≃ₐ[K] L) (ω : KaehlerDifferential K L)
    (hω : ω ∈ globalRegularDifferentials K L) :
    algHomKaehlerMap σ.toAlgHom ω ∈ globalRegularDifferentials K L :=
  globalRegularDifferentials_map_equiv σ ω hω

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
