/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2NormQuotient
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebra

/-!
# Descent of cyclic algebras along the degree-two norm quotient

For a finite cyclic Galois extension, equality of the base-unit representatives in degree-two
cohomology is exactly equality up to a field norm.  A norm changes the raw cyclic algebra by the
explicit generator rescaling `X ↦ cX`.  Thus the raw cyclic algebra depends, up to `K`-algebra
equivalence, only on its degree-two cohomology parameter.

This remains a statement about raw cyclic algebras.  Identifying their equivalence classes with
the Brauer group additionally requires central simplicity.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open CategoryTheory groupCohomology Rep Rep.FiniteCyclicGroup

attribute [local instance] IsCyclic.commGroup

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]

/-- Two base-field unit representatives determine the same cyclic degree-two cohomology class
exactly when their ratio is a norm from the cyclic extension. -/
theorem cyclicGaloisH2BaseProjection_eq_iff_exists_norm_ratio
    [FiniteDimensional K L] [IsGalois K L] (a b : Additive Kˣ) :
    cyclicGaloisH2BaseProjection K L a = cyclicGaloisH2BaseProjection K L b ↔
      ∃ c : Lˣ, (a.toMul : K) = Algebra.norm K (c : L) * (b.toMul : K) := by
  constructor
  · intro hab
    have hzero : cyclicGaloisH2BaseProjection K L (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    have hmem : a - b ∈ cyclicGaloisH2BaseNormImage K L := by
      rw [cyclicGaloisH2BaseNormImage_eq_ker]
      exact hzero
    obtain ⟨c, hc⟩ := hmem
    refine ⟨c.toMul, ?_⟩
    have hcmul : cyclicGaloisNormUnits K L c.toMul =
        (a - b).toMul := congrArg Additive.toMul hc
    have hval := congrArg Units.val hcmul
    change Algebra.norm K ((c.toMul : Lˣ) : L) =
      (((a - b).toMul : Kˣ) : K) at hval
    rw [show (((a - b).toMul : Kˣ) : K) =
      (a.toMul : K) * (b.toMul : K)⁻¹ by simp [div_eq_mul_inv]] at hval
    rw [hval, mul_assoc, inv_mul_cancel₀ b.toMul.ne_zero, mul_one]
  · rintro ⟨c, hc⟩
    have hunit : (a - b).toMul = cyclicGaloisNormUnits K L c := by
      apply Units.ext
      apply FaithfulSMul.algebraMap_injective K L
      rw [show (((a - b).toMul : Kˣ) : K) =
        (a.toMul : K) * (b.toMul : K)⁻¹ by simp [div_eq_mul_inv]]
      rw [hc]
      rw [mul_assoc, mul_inv_cancel₀ b.toMul.ne_zero, mul_one]
      rfl
    have hmem : a - b ∈ cyclicGaloisH2BaseNormImage K L := by
      refine ⟨Additive.ofMul c, ?_⟩
      apply Additive.toMul.injective
      exact hunit.symm
    have hzero : cyclicGaloisH2BaseProjection K L (a - b) = 0 := by
      rw [cyclicGaloisH2BaseNormImage_eq_ker K L] at hmem
      exact AddMonoidHom.mem_ker.mp hmem
    rw [map_sub, sub_eq_zero] at hzero
    exact hzero

/-- Equal degree-two cohomology parameters yield equivalent raw cyclic Galois algebras over the
base field.  The equivalence is induced by scaling the cyclic generator by a norm witness. -/
theorem cyclicGaloisH2BaseProjection_eq_implies_nonempty_algEquiv
    [FiniteDimensional K L] [IsGalois K L] (a b : Additive Kˣ)
    (h : cyclicGaloisH2BaseProjection K L a = cyclicGaloisH2BaseProjection K L b) :
    Nonempty (cyclicGaloisAlgebra K L (a.toMul : K) ≃ₐ[K]
      cyclicGaloisAlgebra K L (b.toMul : K)) := by
  obtain ⟨c, hc⟩ := (cyclicGaloisH2BaseProjection_eq_iff_exists_norm_ratio K L a b).mp h
  exact ⟨cyclicGaloisAlgebraNormScaleAlgEquiv K L (a.toMul : K) (b.toMul : K) c hc⟩

/-- The base unit selected for a degree-two class represents that class through the direct
base-unit projection. -/
theorem cyclicGaloisH2ClassCyclicAlgebra_baseParameter_projection
    [FiniteDimensional K L] [IsGalois K L] (z : cyclicGaloisH2 K L) :
    cyclicGaloisH2BaseProjection K L
        (Additive.ofMul (cyclicGaloisH2FixedBaseUnit K L
          (cyclicGaloisH2Representative K L z))) = z := by
  rw [cyclicGaloisH2BaseProjection, AddMonoidHom.comp_apply]
  have hrepresentative : cyclicGaloisH2FixedUnitsBaseAddHom K L
      (Additive.ofMul (cyclicGaloisH2FixedBaseUnit K L
        (cyclicGaloisH2Representative K L z))) = cyclicGaloisH2Representative K L z := by
    apply Subtype.ext
    apply Additive.toMul.injective
    change Units.map (algebraMap K L)
      (cyclicGaloisH2FixedBaseUnit K L (cyclicGaloisH2Representative K L z)) =
        cyclicGaloisH2FixedUnit K L (cyclicGaloisH2Representative K L z)
    exact cyclicGaloisH2FixedBaseUnit_map K L (cyclicGaloisH2Representative K L z)
  rw [hrepresentative]
  exact cyclicGaloisH2ClassCyclicAlgebra_projection K L z

/-- Every base-unit representative of a degree-two class yields a raw cyclic algebra equivalent
to the selected algebra for that class.  This removes the representative choice at the level of
raw `K`-algebras. -/
theorem cyclicGaloisH2BaseProjection_eq_class_implies_nonempty_algEquiv
    [FiniteDimensional K L] [IsGalois K L] (a : Additive Kˣ) (z : cyclicGaloisH2 K L)
    (h : cyclicGaloisH2BaseProjection K L a = z) :
    Nonempty (cyclicGaloisAlgebra K L (a.toMul : K) ≃ₐ[K]
      cyclicGaloisH2ClassCyclicAlgebra K L z) := by
  let b : Additive Kˣ := Additive.ofMul
    (cyclicGaloisH2FixedBaseUnit K L (cyclicGaloisH2Representative K L z))
  have hb : cyclicGaloisH2BaseProjection K L b = z :=
    cyclicGaloisH2ClassCyclicAlgebra_baseParameter_projection K L z
  change Nonempty (cyclicGaloisAlgebra K L (a.toMul : K) ≃ₐ[K]
    cyclicGaloisAlgebra K L (b.toMul : K))
  exact cyclicGaloisH2BaseProjection_eq_implies_nonempty_algEquiv K L a b (h.trans hb.symm)

end GaloisForLFunctions.HTGeometry.ABHN
