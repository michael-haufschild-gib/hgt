import GaloisForLFunctions.RHTower.DeningerMeyerRationalSourceTail
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Rational-function action on the non-finite actual Meyer sector

Every nonzero complex polynomial acts bijectively on the actual source tail.
The universal localization construction therefore equips this same nonzero
space with a compatible rational-function-field action. Its pole divisions
are represented by the canonical finite-defect operators on actual sources.
-/

open Polynomial

namespace RHTower
noncomputable section

abbrev DeningerMeyerRationalTailPolynomialModule :=
  Module.AEval' deningerMeyerRationalTailGenerator

local notation "M" => DeningerMeyerRationalTailPolynomialModule
local notation "ofTail" => Module.AEval'.of deningerMeyerRationalTailGenerator

theorem deningerMeyerRationalTailPolynomial_shift_apply (rho : ℂ) (u : M) :
    (ofTail).symm ((X - C rho : ℂ[X]) • u) =
      deningerMeyerRationalTailShift rho ((ofTail).symm u) := by
  rw [Module.AEval.of_symm_smul, map_sub, aeval_X, aeval_C]
  rfl

theorem deningerMeyerRationalTailPolynomial_shift_bijective (rho : ℂ) :
    Function.Bijective (fun u : M => (X - C rho : ℂ[X]) • u) := by
  constructor
  · intro u v huv
    change (X - C rho : ℂ[X]) • u = (X - C rho : ℂ[X]) • v at huv
    apply (ofTail).symm.injective
    apply (deningerMeyerRationalTailShift_bijective rho).1
    rw [← deningerMeyerRationalTailPolynomial_shift_apply,
      ← deningerMeyerRationalTailPolynomial_shift_apply, huv]
  · intro u
    obtain ⟨v, hv⟩ := (deningerMeyerRationalTailShift_bijective rho).2 ((ofTail).symm u)
    refine ⟨ofTail v, ?_⟩
    apply (ofTail).symm.injective
    rw [deningerMeyerRationalTailPolynomial_shift_apply, (ofTail).symm_apply_apply]
    exact hv

/-- All polynomial denominators are invertible on this actual nonzero quotient. -/
theorem deningerMeyerRationalTailPolynomial_smul_bijective (p : ℂ[X]) (hp : p ≠ 0) :
    Function.Bijective (fun u : M => p • u) := by
  have hprod (L : Multiset ℂ) : Function.Bijective (fun u : M =>
      (L.map (fun rho => X - C rho)).prod • u) := by
    induction L using Multiset.induction_on with
    | empty =>
      constructor
      · intro u v huv
        simpa using huv
      · intro u
        exact ⟨u, by simp⟩
    | @cons rho L ih =>
      have h := (deningerMeyerRationalTailPolynomial_shift_bijective rho).comp ih
      change Function.Bijective (fun u : M =>
        (X - C rho : ℂ[X]) • (L.map (fun tau => X - C tau)).prod • u) at h
      simpa only [Multiset.map_cons, Multiset.prod_cons, mul_smul] using h
  have hc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hconst : Function.Bijective (fun u : M => p.leadingCoeff • u) := by
    constructor
    · intro u v huv
      have h := congrArg (fun w : M => p.leadingCoeff⁻¹ • w) huv
      simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h
    · intro u
      refine ⟨p.leadingCoeff⁻¹ • u, ?_⟩
      change p.leadingCoeff • (p.leadingCoeff⁻¹ • u) = u
      rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  convert hconst.comp (hprod p.roots) using 1
  funext u
  change p • u = p.leadingCoeff • (p.roots.map (fun rho => X - C rho)).prod • u
  conv_lhs => rw [(IsAlgClosed.splits p).eq_prod_roots]
  rw [mul_smul, Module.AEval.C_smul]

instance deningerMeyerRationalTail_isLocalized :
    IsLocalizedModule (nonZeroDivisors ℂ[X]) (LinearMap.id : M →ₗ[ℂ[X]] M) where
  map_units p := by
    rw [Module.End.isUnit_iff]
    change Function.Bijective (fun u : M => p.val • u)
    exact deningerMeyerRationalTailPolynomial_smul_bijective p.val
      (mem_nonZeroDivisors_iff_ne_zero.mp p.property)
  surj u := ⟨(u, 1), by simp⟩
  exists_of_eq h := ⟨1, by simpa using h⟩

/-- The actual tail itself, not a further recipient, is a rational-function vector space. -/
instance deningerMeyerRationalTail_ratFuncModule : Module (RatFunc ℂ) M :=
  IsLocalizedModule.module (nonZeroDivisors ℂ[X]) (LinearMap.id : M →ₗ[ℂ[X]] M)

instance deningerMeyerRationalTail_polynomial_ratFunc_tower :
    IsScalarTower ℂ[X] (RatFunc ℂ) M :=
  IsLocalizedModule.isScalarTower_module (nonZeroDivisors ℂ[X])
    (LinearMap.id : M →ₗ[ℂ[X]] M)

theorem deningerMeyerRationalTail_polynomial_smul (p : ℂ[X]) (u : M) :
    algebraMap ℂ[X] (RatFunc ℂ) p • u = p • u :=
  IsScalarTower.algebraMap_smul (RatFunc ℂ) p u

/-- Arbitrary rational forcing can be divided by arbitrary nonzero polynomial
denominators, with no Xi-zero exclusion. -/
theorem deningerMeyerRationalTail_fraction_equation
    (p q : ℂ[X]) (hq : q ≠ 0) (u : M) :
    q • ((algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q) • u) = p • u := by
  have hq' : algebraMap ℂ[X] (RatFunc ℂ) q ≠ 0 := by
    intro h
    apply hq
    apply IsFractionRing.injective ℂ[X] (RatFunc ℂ)
    simpa using h
  rw [← deningerMeyerRationalTail_polynomial_smul q, smul_smul]
  have heq : algebraMap ℂ[X] (RatFunc ℂ) q *
      (algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q) =
        algebraMap ℂ[X] (RatFunc ℂ) p := by field_simp
  rw [heq, deningerMeyerRationalTail_polynomial_smul]

/-- Rational pole division is represented by an audited actual-source operator
with the full finite resonant packet as its two-sided defect. -/
theorem deningerMeyerRationalTail_inverse_shift_source
    (rho : ℂ) (u : DeningerMeyerArithmeticSource) :
    (1 / algebraMap ℂ[X] (RatFunc ℂ) (X - C rho)) • ofTail (Submodule.Quotient.mk u) =
      ofTail (Submodule.Quotient.mk (deningerMeyerArithmeticWordDivision [rho] u)) := by
  apply (deningerMeyerRationalTailPolynomial_shift_bijective rho).1
  change (X - C rho : ℂ[X]) •
      ((1 / algebraMap ℂ[X] (RatFunc ℂ) (X - C rho)) • ofTail (Submodule.Quotient.mk u)) =
    (X - C rho : ℂ[X]) •
      ofTail (Submodule.Quotient.mk (deningerMeyerArithmeticWordDivision [rho] u))
  have hleft := deningerMeyerRationalTail_fraction_equation 1 (X - C rho)
    (X_sub_C_ne_zero rho) (ofTail (Submodule.Quotient.mk u))
  simp only [map_one, one_smul] at hleft
  rw [hleft]
  apply (ofTail).symm.injective
  rw [deningerMeyerRationalTailPolynomial_shift_apply,
    (ofTail).symm_apply_apply, (ofTail).symm_apply_apply,
    ← deningerMeyerRationalTailResolvent_source]
  exact (deningerMeyerRationalTailResolvent_equation rho (Submodule.Quotient.mk u)).symm

end
end RHTower
