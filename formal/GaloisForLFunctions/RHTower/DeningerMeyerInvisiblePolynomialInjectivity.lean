import GaloisForLFunctions.RHTower.DeningerMeyerInvisibleSourceDivisibility
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Polynomial injectivity of the invisible Meyer sector

The actual causal division theorem makes every shifted invisible generator
surjective. Complex polynomial factorization upgrades this to divisibility by
every nonzero polynomial. Principal ideals then give Baer's extension property.
This is an unconditional property of the actual comparison kernel, not a
spectral-synthesis hypothesis.
-/

open Polynomial

namespace RHTower
noncomputable section

/-- Literal Meyer cohomology with the polynomial action induced by its generator. -/
abbrev DeningerMeyerCohomologyPolynomialModule :=
  Module.AEval' deningerMeyerCohomologyGenerator

/-- The invisible sector with its actual generator action. -/
abbrev DeningerMeyerInvisiblePolynomialModule :=
  Module.AEval' deningerMeyerInvisibleGenerator

theorem deningerMeyerInvisiblePolynomial_shift_surjective (rho : ℂ) :
    Function.Surjective (fun u : DeningerMeyerInvisiblePolynomialModule =>
      (X - C rho : ℂ[X]) • u) := by
  intro u
  obtain ⟨v, hv⟩ := deningerMeyerInvisibleGenerator_shift_surjective rho
    ((Module.AEval'.of deningerMeyerInvisibleGenerator).symm u)
  refine ⟨Module.AEval'.of deningerMeyerInvisibleGenerator v, ?_⟩
  change (X - C rho : ℂ[X]) •
    Module.AEval'.of deningerMeyerInvisibleGenerator v = u
  apply (Module.AEval'.of deningerMeyerInvisibleGenerator).symm.injective
  rw [Module.AEval.of_symm_smul]
  change (aeval deningerMeyerInvisibleGenerator (X - C rho)) v =
    (Module.AEval'.of deningerMeyerInvisibleGenerator).symm u
  rw [map_sub, aeval_X, aeval_C]
  exact hv

/-- Every nonzero polynomial acts surjectively on the actual invisible sector. -/
theorem deningerMeyerInvisiblePolynomial_smul_surjective
    (p : ℂ[X]) (hp : p ≠ 0) :
    Function.Surjective (fun u : DeningerMeyerInvisiblePolynomialModule => p • u) := by
  have hprod (L : Multiset ℂ) : Function.Surjective
      (fun u : DeningerMeyerInvisiblePolynomialModule =>
        (L.map (fun rho => X - C rho)).prod • u) := by
    induction L using Multiset.induction_on with
    | empty => exact fun u => ⟨u, by simp⟩
    | @cons rho L ih =>
        intro u
        obtain ⟨v, hv⟩ := deningerMeyerInvisiblePolynomial_shift_surjective rho u
        obtain ⟨w, hw⟩ := ih v
        refine ⟨w, ?_⟩
        change ((Multiset.map (fun rho => X - C rho) (rho ::ₘ L)).prod) • w = u
        rw [Multiset.map_cons, Multiset.prod_cons, mul_smul]
        rw [show (L.map (fun rho => X - C rho)).prod • w = v from hw]
        exact hv
  intro u
  obtain ⟨v, hv⟩ := hprod p.roots (p.leadingCoeff⁻¹ • u)
  refine ⟨v, ?_⟩
  change p • v = u
  change (p.roots.map (fun rho => X - C rho)).prod • v = p.leadingCoeff⁻¹ • u at hv
  conv_lhs => rw [(IsAlgClosed.splits p).eq_prod_roots]
  rw [mul_smul, hv, Module.AEval.C_smul, smul_smul,
    mul_inv_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hp), one_smul]

/-- Baer's criterion, proved for this polynomial action from actual source division. -/
theorem deningerMeyerInvisiblePolynomial_baer :
    Module.Baer ℂ[X] DeningerMeyerInvisiblePolynomialModule := by
  intro I g
  rcases IsPrincipalIdealRing.principal I with ⟨p, rfl⟩
  obtain rfl | hp := eq_or_ne p 0
  · refine ⟨0, fun q hq => ?_⟩
    rw [Submodule.span_zero_singleton] at hq
    subst hq
    exact (map_zero g).symm
  obtain ⟨v, hv⟩ := deningerMeyerInvisiblePolynomial_smul_surjective p hp
    (g ⟨p, Submodule.subset_span (Set.mem_singleton p)⟩)
  refine ⟨LinearMap.toSpanSingleton ℂ[X] DeningerMeyerInvisiblePolynomialModule v,
    fun q hq => ?_⟩
  obtain ⟨q, rfl⟩ := Submodule.mem_span_singleton.mp hq
  rw [LinearMap.toSpanSingleton_apply]
  change (q * p) • v = g ⟨q * p, hq⟩
  rw [mul_smul, show p • v = g ⟨p, Submodule.subset_span (Set.mem_singleton p)⟩ from hv]
  exact (g.map_smul q ⟨p, Submodule.subset_span (Set.mem_singleton p)⟩).symm

/-- The invisible comparison kernel is injective as a complex-polynomial module. -/
theorem deningerMeyerInvisiblePolynomial_injective :
    Module.Injective ℂ[X] DeningerMeyerInvisiblePolynomialModule :=
  deningerMeyerInvisiblePolynomial_baer.injective

/-- The inclusion remembers the generator action, not merely the vector-space structure. -/
def deningerMeyerInvisiblePolynomialInclusion :
    DeningerMeyerInvisiblePolynomialModule →ₗ[ℂ[X]]
      DeningerMeyerCohomologyPolynomialModule :=
  LinearMap.ofAEval deningerMeyerInvisibleGenerator
    ((Module.AEval'.of deningerMeyerCohomologyGenerator).toLinearMap.comp
      DeningerMeyerInvisible.subtype)
    (fun u => (Module.AEval'.X_smul_of deningerMeyerCohomologyGenerator
      (u : DeningerMeyerStrongLogCohomology)).symm)

end
end RHTower
