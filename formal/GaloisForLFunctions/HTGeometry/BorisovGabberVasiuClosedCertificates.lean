import GaloisForLFunctions.HTGeometry.BorisovGabberVasiuPointFibers
import GaloisForLFunctions.HTGeometry.BorisovGabberVasiuJets
import GaloisForLFunctions.HTGeometry.BorisovGabberVasiuEulerFamily
import GaloisForLFunctions.HTGeometry.BorisovGabberVasiuRationalCore
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Data.ZMod.Basic

/-!
# Fully instantiated certificates for the BGV experiment

The fixed field is the algebraic closure of the field with two elements.
These certificates discharge the ambient field, characteristic, and algebraic
closure conditions of the general applications. They exhibit the local/global
separation, exact stable core, and determinant-one families without proof premises.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- A fixed algebraically closed characteristic-two field for premise-free certificates. -/
abbrev BGVExampleField := AlgebraicClosure (ZMod 2)

/-- One fixed example is formally etale and has exact arc lifting at every order,
while its surjective point map still identifies distinct points. -/
theorem bgv_closed_local_global_separation :
    (bgvPowerMap (R := Polynomial BGVExampleField) 2 Polynomial.X).toRingHom.FormallyEtale ∧
    (∀ n : ℕ, Function.Bijective (etaleArcPullbackMap
      (bgvPowerMap (R := Polynomial BGVExampleField) 2 Polynomial.X).toRingHom
      (truncatedArcAugmentation (R := BGVExampleField) n).toRingHom)) ∧
    Function.Surjective (fun z : BGVExampleField × BGVExampleField =>
      (z.1 + z.2 * z.1 ^ 2, z.2)) ∧
    ¬ Function.Injective (fun z : BGVExampleField × BGVExampleField =>
      (z.1 + z.2 * z.1 ^ 2, z.2)) := by
  exact ⟨bgv_quadraticPlane_formallyEtale,
    fun n => bgvPowerMap_truncatedArc_pullback_bijective 2 Polynomial.X n,
    bgv_quadraticPlane_surjective, bgv_quadraticPlane_not_injective⟩

/-- In a fixed field, finite image stages never stabilize and the exact infinite survivor
is the coefficient field. There are no ambient field hypotheses to discharge. -/
theorem bgv_closed_stable_core_classification :
    stableRangeCore (bgvQuadraticRationalMap (K := BGVExampleField)) = ⊥ ∧
    ∀ n : ℕ,
      Set.range (bgvQuadraticRationalMap ^ n :
        RatFunc BGVExampleField →ₐ[BGVExampleField] RatFunc BGVExampleField) ≠
      Set.range (bgvQuadraticRationalMap ^ (n + 1) :
        RatFunc BGVExampleField →ₐ[BGVExampleField] RatFunc BGVExampleField) :=
  ⟨bgv_quadraticRationalMap_stableCore,
    bgv_quadraticRationalMap_no_finite_stabilization⟩

/-- Every positive finite dimension has a freely parameterized determinant-one family,
with its differential-pullback determinant certificate included. -/
theorem bgv_closed_euler_families (n : ℕ) (g : Polynomial BGVExampleField)
    (L : MvPolynomial (Option (Fin n)) BGVExampleField) :
    let w := L ^ 2 * ∏ j : Option (Fin n), MvPolynomial.X j
    (jacobian BGVExampleField (Option (Fin n))
      (bgvSharedSourceMap (bgvEulerFactors 1 g) w)).det = 1 ∧
    LinearMap.det (pullbackDifferential BGVExampleField (Option (Fin n))
      (bgvSharedSourceMap (bgvEulerFactors 1 g) w)) = 1 :=
  ⟨bgv_eulerFamily_jacobian_one g L, bgv_eulerFamily_pullback_det_one g L⟩

end GaloisForLFunctions.HTGeometry
