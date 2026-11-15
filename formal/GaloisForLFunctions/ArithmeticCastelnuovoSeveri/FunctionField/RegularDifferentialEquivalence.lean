import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.ValuationDifferentialTransport

/-!
# Field invariance of regular differentials

A constant-field isomorphism transports Kähler differentials and every proper
constant-field valuation ring. Its induced map therefore identifies the spaces
of differentials regular at all places, and preserves their dimensions.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.HTGeometry
variable {K L L' : Type*} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']

private theorem kaehlerMap_inverse (σ : L ≃ₐ[K] L') (ω : KaehlerDifferential K L) :
    algHomKaehlerMap σ.symm.toAlgHom (algHomKaehlerMap σ.toAlgHom ω) = ω := by
  have hω : ω ∈ Submodule.span L (Set.range (KaehlerDifferential.D K L)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hω
  · rintro _ ⟨x, rfl⟩
    rw [algHomKaehlerMap_D, algHomKaehlerMap_D]
    change KaehlerDifferential.D K L (σ.symm (σ x)) = KaehlerDifferential.D K L x
    rw [σ.symm_apply_apply]
  · rw [map_zero, map_zero]
  · intro x y _ _ hx hy
    rw [map_add, map_add, hx, hy]
  · intro a x _ hx
    rw [algHomKaehlerMap_smul, algHomKaehlerMap_smul, hx]
    change σ.symm (σ a) • x = a • x
    rw [σ.symm_apply_apply]

/-- A constant-field isomorphism identifies the intrinsic spaces of regular differentials. -/
def globalRegularDifferentialEquiv (σ : L ≃ₐ[K] L') :
    globalRegularDifferentials K L ≃ₗ[K] globalRegularDifferentials K L' where
  toFun ω := ⟨algHomKaehlerMap σ.toAlgHom ω.val,
    globalRegularDifferentials_map_equiv σ ω.val ω.property⟩
  invFun ω := ⟨algHomKaehlerMap σ.symm.toAlgHom ω.val,
    globalRegularDifferentials_map_equiv σ.symm ω.val ω.property⟩
  left_inv ω := Subtype.ext (kaehlerMap_inverse σ ω.val)
  right_inv ω := Subtype.ext (kaehlerMap_inverse σ.symm ω.val)
  map_add' ω η := Subtype.ext ((algHomKaehlerMap σ.toAlgHom).map_add ω.val η.val)
  map_smul' a ω := Subtype.ext ((algHomKaehlerMap σ.toAlgHom).map_smul a ω.val)

/-- The dimension of global regular differentials is a constant-field isomorphism invariant. -/
theorem globalRegularDifferential_finrank_eq (σ : L ≃ₐ[K] L') :
    Module.finrank K (globalRegularDifferentials K L) =
      Module.finrank K (globalRegularDifferentials K L') :=
  (globalRegularDifferentialEquiv σ).finrank_eq

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
