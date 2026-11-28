import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.SmoothParabolicInduction
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.SmoothDualTransport

/-! Multiplying an equivariant function by a character moves
the twist from the induced action to the inducing representation. -/

noncomputable section

namespace Representation

variable {G H V : Type*} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
  (f : H →* G) (ρ : Representation ℂ H V) (χ : G →* ℂˣ)

private def coindScalarTwistEquiv :
    ((coind f ρ).scalarTwist χ).Equiv (coind f (ρ.scalarTwist (χ.comp f))) := by
  let e : coindV f ρ ≃ₗ[ℂ] coindV f (ρ.scalarTwist (χ.comp f)) :=
    { toFun := fun u => ⟨fun x => (χ x : ℂ) • u.val x, fun h x => by
        change (χ (f h * x) : ℂ) • u.val (f h * x) = _
        rw [u.prop h x, scalarTwist_apply, MonoidHom.comp_apply, map_mul, Units.val_mul,
          map_smul, smul_smul]⟩
      invFun := fun u => ⟨fun x => (χ x : ℂ)⁻¹ • u.val x, fun h x => by
        change (χ (f h * x) : ℂ)⁻¹ • u.val (f h * x) = ρ h ((χ x : ℂ)⁻¹ • u.val x)
        have he : (χ (f h * x) : ℂ)⁻¹ = (χ x : ℂ)⁻¹ * (χ (f h) : ℂ)⁻¹ := by
          rw [← Units.val_inv_eq_inv_val, map_mul, mul_inv_rev, Units.val_mul,
            Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
        rw [u.prop h x, scalarTwist_apply, MonoidHom.comp_apply, map_smul, he, smul_smul,
          mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), mul_one]⟩
      left_inv := fun u => Subtype.ext (funext fun x => by
        change (χ x : ℂ)⁻¹ • ((χ x : ℂ) • u.val x) = u.val x
        rw [smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul])
      right_inv := fun u => Subtype.ext (funext fun x => by
        change (χ x : ℂ) • ((χ x : ℂ)⁻¹ • u.val x) = u.val x
        rw [smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul])
      map_add' := fun u w => Subtype.ext (funext fun x => by
        change (χ x : ℂ) • (u.val x + w.val x) = _
        rw [smul_add]
        rfl)
      map_smul' := fun a u => Subtype.ext (funext fun x => by
        change (χ x : ℂ) • (a • u.val x) = a • ((χ x : ℂ) • u.val x)
        exact smul_comm _ _ _) }
  refine Equiv.mk e fun g => LinearMap.ext fun u => Subtype.ext (funext fun x => ?_)
  change (χ x : ℂ) • ((χ g : ℂ) • u.val (x * g)) = (χ (x * g) : ℂ) • u.val (x * g)
  rw [map_mul, Units.val_mul, smul_smul]

variable [TopologicalSpace G] [IsTopologicalGroup G]

def smoothInductionScalarTwistEquiv (hχ : IsOpen (χ.ker : Set G)) :
    (scalarTwist (V := (coind f ρ).smoothVectors) (smoothInduction f ρ) χ).Equiv
      (smoothInduction f (ρ.scalarTwist (χ.comp f))) :=
  (smoothPartScalarTwistEquiv (coind f ρ) χ hχ).symm.trans (coindScalarTwistEquiv f ρ χ).smoothPart

end Representation

#print axioms Representation.smoothInductionScalarTwistEquiv
