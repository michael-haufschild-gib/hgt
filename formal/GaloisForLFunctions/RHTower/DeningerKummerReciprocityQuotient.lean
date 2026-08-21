import GaloisForLFunctions.RHTower.DeningerTowerReciprocity
import GaloisForLFunctions.RHTower.DeningerKummerGroupNorm

/-!
# The torsion-free Kummer map into the reciprocity kernel

The product formula gives a map from global units to the kernel of the sum of local logarithmic
currents.  Its kernel is exactly the roots of unity, so it descends to an injective map from the
Kummer quotient `Kˣ / μ(K)`.  This is a local--global separation statement: finite-support local
data in the reciprocity kernel determine the global class modulo its unavoidable torsion.
-/

namespace RHTower

noncomputable section

/-- The logarithmic Kummer map, written multiplicatively so that it descends to the Kummer
quotient. -/
noncomputable def deningerKummerReciprocityMulHom (K : Type*) [Field K] [NumberField K] :
    Kˣ →* Multiplicative (LinearMap.ker (deningerPlaceSum K)) where
  toFun u := Multiplicative.ofAdd (deningerKummerReciprocityHom K (Additive.ofMul u))
  map_one' := by
    apply Multiplicative.toAdd.injective
    exact (deningerKummerReciprocityHom K).map_zero
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    change deningerKummerReciprocityHom K (Additive.ofMul u + Additive.ofMul v) =
      deningerKummerReciprocityHom K (Additive.ofMul u) +
        deningerKummerReciprocityHom K (Additive.ofMul v)
    exact (deningerKummerReciprocityHom K).map_add _ _

/-- The Kummer map factors through the quotient by roots of unity into the product-formula
kernel. -/
noncomputable def deningerKummerReciprocityQuotientHom (K : Type*) [Field K] [NumberField K] :
    deningerKummerGroup K →* Multiplicative (LinearMap.ker (deningerPlaceSum K)) :=
  QuotientGroup.lift (CommGroup.torsion Kˣ) (deningerKummerReciprocityMulHom K) (by
    intro u hu
    apply Multiplicative.toAdd.injective
    apply (deningerKummerReciprocityHom_eq_zero_iff K u).mpr
    exact (deningerUnits_isOfFinOrder_iff (F := K)).mpr ((CommGroup.mem_torsion u).mp hu))

/-- Evaluation of the descended map on a unit representative. -/
theorem deningerKummerReciprocityQuotientHom_mk (K : Type*) [Field K] [NumberField K] (u : Kˣ) :
    deningerKummerReciprocityQuotientHom K (QuotientGroup.mk u) =
      Multiplicative.ofAdd (deningerKummerReciprocityHom K (Additive.ofMul u)) := rfl

/-- The product-formula local current determines a global unit modulo roots of unity. -/
theorem deningerKummerReciprocityQuotientHom_injective (K : Type*) [Field K] [NumberField K] :
    Function.Injective (deningerKummerReciprocityQuotientHom K) := by
  intro x y hxy
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective y
  rw [QuotientGroup.eq_iff_div_mem]
  rw [deningerKummerReciprocityQuotientHom_mk,
    deningerKummerReciprocityQuotientHom_mk] at hxy
  apply (CommGroup.mem_torsion _).mpr
  apply (deningerUnits_isOfFinOrder_iff (F := K)).mp
  apply (deningerKummerReciprocityHom_eq_iff K u v).mp
  apply Multiplicative.toAdd.injective
  exact hxy

/-- The torsion-free Kummer quotient is multiplicatively equivalent to the local currents in the
product-formula kernel that are globally realized. -/
noncomputable def deningerKummerReciprocityQuotientEquivRange (K : Type*) [Field K]
    [NumberField K] : deningerKummerGroup K ≃*
      (MonoidHom.mrange (deningerKummerReciprocityQuotientHom K)) :=
  MulEquiv.ofBijective
    (MonoidHom.mrangeRestrict (deningerKummerReciprocityQuotientHom K))
    ⟨fun _ _ hxy => deningerKummerReciprocityQuotientHom_injective K (congrArg Subtype.val hxy),
      MonoidHom.mrangeRestrict_surjective _⟩

/-- Evaluation of the local--global Kummer equivalence. -/
theorem deningerKummerReciprocityQuotientEquivRange_apply (K : Type*) [Field K] [NumberField K]
    (x : deningerKummerGroup K) : deningerKummerReciprocityQuotientEquivRange K x =
      MonoidHom.mrangeRestrict (deningerKummerReciprocityQuotientHom K) x := rfl

end

end RHTower
