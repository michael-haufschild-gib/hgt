/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraBrauerTensorProduct
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisRestrictionOrientation

/-!
# Cyclic-algebra representation through a Galois tower

For a cyclic Galois tower `K ⊆ L ⊆ M`, let `q` record the orientation of the restriction of
the chosen generator of `Gal(M/K)` relative to the chosen generator of `Gal(L/K)`.  The cyclic
algebra over `M/K` with parameter `a ^ (q * [M:L])` acts on

`End_K(M) ⊗[K] (L/K, a)`.

Coefficients in `M` act through their left regular representation on the first factor.  The upper
cyclic generator acts as the tensor product of the upper Galois generator with the `q`th power of
the lower cyclic generator.  The skew relation and parameter-power relation hold exactly, giving
an injective algebra homomorphism because the source cyclic algebra is simple.

This is the induced crossed-product representation underlying Brauer compatibility with genuine
inflation.  The remaining Morita step is to identify its centralizer as a split matrix algebra.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct
open Multiplicative

noncomputable section

variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
  [IsGalois K L] [IsGalois K M]
  [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]

/-- Upper coefficients act by left multiplication on `M` in the first tensor factor. -/
noncomputable def cyclicGaloisAlgebraTowerCoefficientAction (a : K) :
    M →+* (Module.End K M ⊗[K] cyclicGaloisAlgebra K L a) :=
  (Algebra.TensorProduct.includeLeft (R := K) (S := K)
    (A := Module.End K M) (B := cyclicGaloisAlgebra K L a)).toRingHom.comp
    (Algebra.lmul K M).toRingHom

/-- The induced upper cyclic generator: upper Galois action tensored with the orientation power of
the lower cyclic generator. -/
noncomputable def cyclicGaloisAlgebraTowerGeneratorAction (a : K) :
    Module.End K M ⊗[K] cyclicGaloisAlgebra K L a :=
  (cyclicGaloisGenerator K M).toLinearMap ⊗ₜ[K]
    (cyclicGaloisAlgebraX K L a ^ (cyclicGaloisRestrictionOrientation K L M).val)

/-- Powers of the induced generator separate into the Galois-action power and the corresponding
lower cyclic-generator power. -/
theorem cyclicGaloisAlgebraTowerGeneratorAction_pow (a : K) (r : ℕ) :
    cyclicGaloisAlgebraTowerGeneratorAction K L M a ^ r =
      ((cyclicGaloisGenerator K M).toLinearMap ^ r) ⊗ₜ[K]
        (cyclicGaloisAlgebraX K L a ^
          ((cyclicGaloisRestrictionOrientation K L M).val * r)) := by
  rw [cyclicGaloisAlgebraTowerGeneratorAction, cyclicTensorProduct_tmul_pow]
  congr 1
  rw [← pow_mul]

/-- Upper coefficients and the induced generator satisfy every skew commutation relation required
by the cyclic-algebra universal property. -/
theorem cyclicGaloisAlgebraTower_actions_commute
    (a : K) (r : Multiplicative ℕ) (x : M) :
    cyclicGaloisAlgebraTowerCoefficientAction K L M a
          ((cyclicPowerRingAut (cyclicGaloisGenerator K M).toRingEquiv) r x) *
        cyclicPowerMonoidHom (cyclicGaloisAlgebraTowerGeneratorAction K L M a) r =
      cyclicPowerMonoidHom (cyclicGaloisAlgebraTowerGeneratorAction K L M a) r *
        cyclicGaloisAlgebraTowerCoefficientAction K L M a x := by
  change
    ((Algebra.lmul K M
      (((cyclicGaloisGenerator K M).toRingEquiv ^ Multiplicative.toAdd r) x)) ⊗ₜ[K] 1) *
        cyclicGaloisAlgebraTowerGeneratorAction K L M a ^ Multiplicative.toAdd r =
      cyclicGaloisAlgebraTowerGeneratorAction K L M a ^ Multiplicative.toAdd r *
        ((Algebra.lmul K M x) ⊗ₜ[K] 1)
  rw [cyclicGaloisAlgebraTowerGeneratorAction_pow,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, mul_one]
  congr 1
  exact cyclicGaloisAlgebraSplit_actions_commute K M r x

/-- The induced generator has the orientation-corrected inflated parameter
`a ^ (q * [M:L])`. -/
theorem cyclicGaloisAlgebraTowerGeneratorAction_pow_finrank (a : K) :
    cyclicGaloisAlgebraTowerGeneratorAction K L M a ^ Module.finrank K M =
      cyclicGaloisAlgebraTowerCoefficientAction K L M a
        (algebraMap K M
          (a ^ ((cyclicGaloisRestrictionOrientation K L M).val *
            Module.finrank L M))) := by
  rw [cyclicGaloisAlgebraTowerGeneratorAction_pow,
    cyclicGaloisAlgebraSplitGeneratorAction_pow_finrank]
  rw [← Module.finrank_mul_finrank K L M]
  rw [show (cyclicGaloisRestrictionOrientation K L M).val *
      (Module.finrank K L * Module.finrank L M) =
      Module.finrank K L *
        ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M) by
    ac_rfl]
  rw [pow_mul, cyclicGaloisAlgebraX_pow]
  rw [← cyclicGaloisAlgebra_algebraMap_apply]
  rw [← map_pow]
  change (1 : Module.End K M) ⊗ₜ[K]
      cyclicGaloisAlgebraC K L a
        (algebraMap K L
          (a ^ ((cyclicGaloisRestrictionOrientation K L M).val *
            Module.finrank L M))) =
    Algebra.lmul K M
        (algebraMap K M
          (a ^ ((cyclicGaloisRestrictionOrientation K L M).val *
            Module.finrank L M))) ⊗ₜ[K] 1
  rw [← cyclicGaloisAlgebra_algebraMap_apply K L a
    (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M))]
  rw [Algebra.lmul_algebraMap]
  exact (Algebra.TensorProduct.tmul_one_eq_one_tmul
    (A := Module.End K M) (B := cyclicGaloisAlgebra K L a)
    (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M))).symm

/-- Induced crossed-product representation of the orientation-corrected upper cyclic algebra. -/
noncomputable def cyclicGaloisAlgebraTowerRepresentation (a : K) :
    cyclicGaloisAlgebra K M
        (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M)) →+*
      (Module.End K M ⊗[K] cyclicGaloisAlgebra K L a) :=
  cyclicAlgebraLift (cyclicGaloisGenerator K M).toRingEquiv (Module.finrank K M)
    (algebraMap K M
      (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M)))
    (cyclicGaloisAlgebraTowerCoefficientAction K L M a)
    (cyclicGaloisAlgebraTowerGeneratorAction K L M a)
    (cyclicGaloisAlgebraTower_actions_commute K L M a)
    (cyclicGaloisAlgebraTowerGeneratorAction_pow_finrank K L M a)

/-- The tower representation sends upper coefficients to their left regular action. -/
theorem cyclicGaloisAlgebraTowerRepresentation_C (a : K) (x : M) :
    cyclicGaloisAlgebraTowerRepresentation K L M a
        (cyclicGaloisAlgebraC K M
          (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M)) x) =
      (Algebra.lmul K M x) ⊗ₜ[K] 1 := by
  exact cyclicAlgebraLift_C _ _ _ _ _ _ _ x

/-- The tower representation sends the upper cyclic generator to its induced action. -/
theorem cyclicGaloisAlgebraTowerRepresentation_X (a : K) :
    cyclicGaloisAlgebraTowerRepresentation K L M a
        (cyclicGaloisAlgebraX K M
          (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M))) =
      cyclicGaloisAlgebraTowerGeneratorAction K L M a := by
  exact cyclicAlgebraLift_X _ _ _ _ _ _ _

/-- For nonzero lower parameter, the induced upper cyclic-algebra representation is injective. -/
theorem cyclicGaloisAlgebraTowerRepresentation_injective (a : K) (ha : a ≠ 0) :
    Function.Injective (cyclicGaloisAlgebraTowerRepresentation K L M a) := by
  let p := a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M)
  have hp : p ≠ 0 := pow_ne_zero _ ha
  letI : Nontrivial (cyclicGaloisAlgebra K L a) :=
    ⟨0, 1, (cyclicGaloisAlgebra_one_ne_zero K L a).symm⟩
  letI : Nontrivial (Module.End K M) := inferInstance
  letI : Nontrivial (Module.End K M ⊗[K] cyclicGaloisAlgebra K L a) := inferInstance
  letI : IsSimpleRing (cyclicGaloisAlgebra K M p) :=
    isSimpleRing_cyclicGaloisAlgebra_of_nonzero K M p hp
  exact RingHom.injective (cyclicGaloisAlgebraTowerRepresentation K L M a)

/-- The induced crossed-product representation as a base-field algebra homomorphism. -/
noncomputable def cyclicGaloisAlgebraTowerRepresentationAlgHom (a : K) :
    cyclicGaloisAlgebra K M
        (a ^ ((cyclicGaloisRestrictionOrientation K L M).val * Module.finrank L M)) →ₐ[K]
      (Module.End K M ⊗[K] cyclicGaloisAlgebra K L a) :=
  AlgHom.mk' (cyclicGaloisAlgebraTowerRepresentation K L M a) (by
    intro c x
    simp only [Algebra.smul_def, map_mul]
    congr 1
    rw [cyclicGaloisAlgebra_algebraMap_apply,
      cyclicGaloisAlgebraTowerRepresentation_C, Algebra.lmul_algebraMap]
    rfl)

/-- The algebra-hom form of the tower representation is injective. -/
theorem cyclicGaloisAlgebraTowerRepresentationAlgHom_injective (a : K) (ha : a ≠ 0) :
    Function.Injective (cyclicGaloisAlgebraTowerRepresentationAlgHom K L M a) :=
  cyclicGaloisAlgebraTowerRepresentation_injective K L M a ha

end

end GaloisForLFunctions.HTGeometry.ABHN
