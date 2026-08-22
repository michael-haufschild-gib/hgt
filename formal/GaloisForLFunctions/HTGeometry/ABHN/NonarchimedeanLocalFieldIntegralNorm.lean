/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldValuationSequence
import GaloisForLFunctions.HTGeometry.ABHN.IntegralNormUnits
import Mathlib.RingTheory.NormTrace

/-!
# Integral norms in finite unramified local lifts

An irreducible residue polynomial gives a finite unramified root algebra over the valuation ring
of a nonarchimedean local field.  Its integral norm restricts to a map of unit groups.  Together
with `IntegralNormUnits`, this supplies the integral-side norm map needed before one proves that
reduction commutes with norm.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

/-- The norm on units of the finite unramified integral root lift associated to an irreducible
residue polynomial. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootIntegralNormUnits
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g) (hg : Irreducible g) :
    Additive (AdjoinRoot f)ˣ →+ Additive (ValuativeRel.valuation K).integerˣ := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  exact integralNormUnits (ValuativeRel.valuation K).integer (AdjoinRoot f)

/-- Norm commutes with passage to the canonical residue fiber of every monic root algebra over a
nonarchimedean local valuation ring.  The left side is the norm after the scalar-extension
identification of the root algebra with the root algebra of its residue polynomial. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_residueFiberNorm
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hfg : f.map (algebraMap (ValuativeRel.valuation K).integer
      (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)) = g)
    (x : AdjoinRoot f) :
    Algebra.norm (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
      (adjoinRootScalarExtensionEquivOfMapEq (ValuativeRel.valuation K).integer
        (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) f g hfg
        ((1 : IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) ⊗ₜ[
          (ValuativeRel.valuation K).integer] x)) =
      algebraMap (ValuativeRel.valuation K).integer
        (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
          (Algebra.norm (ValuativeRel.valuation K).integer x) := by
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  exact adjoinRootScalarExtensionEquivOfMapEq_norm_tmul_one
    (ValuativeRel.valuation K).integer
    (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) f g hfg x

/-- A residue-polynomial equality written using the quotient map is the equality written using
the residue-field algebra map. -/
theorem nonarchimedeanLocalField_residuePolynomial_algebraMap_eq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g) :
    f.map (algebraMap (ValuativeRel.valuation K).integer
      (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)) = g := by
  change f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
    (ValuativeRel.valuation K).integer)) = g
  exact hfg

/-- Coefficientwise reduction from an integral root algebra to its residue root algebra. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootReductionMap
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g) :
    AdjoinRoot f →ₐ[(ValuativeRel.valuation K).integer] AdjoinRoot g :=
  AdjoinRoot.mapAlgHom (Algebra.ofId (ValuativeRel.valuation K).integer
      (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)) f g (by
        change g ∣ f.map (algebraMap (ValuativeRel.valuation K).integer
          (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
        rw [nonarchimedeanLocalField_residuePolynomial_algebraMap_eq K f g hfg])

/-- Coefficientwise root reduction kills every scalar from the base maximal ideal. -/
theorem nonarchimedeanLocalFieldAdjoinRootReductionMap_smul_eq_zero
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (a : (ValuativeRel.valuation K).integer)
    (ha : a ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer)
    (x : AdjoinRoot f) :
    nonarchimedeanLocalFieldAdjoinRootReductionMap K f g hfg (a • x) = 0 := by
  rw [Algebra.smul_def, map_mul]
  rw [(nonarchimedeanLocalFieldAdjoinRootReductionMap K f g hfg).commutes]
  rw [IsScalarTower.algebraMap_apply (ValuativeRel.valuation K).integer
    (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) (AdjoinRoot g)]
  rw [show algebraMap (ValuativeRel.valuation K).integer
      (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) a = 0 by
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact (IsLocalRing.residue_eq_zero_iff a).mpr ha]
  rw [map_zero]
  exact zero_mul _

/-- Reduction onto a residue root algebra is surjective: every residue element has an integral
root-algebra lift. -/
theorem nonarchimedeanLocalFieldAdjoinRootReductionMap_surjective
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g) :
    Function.Surjective (nonarchimedeanLocalFieldAdjoinRootReductionMap K f g hfg) := by
  exact adjoinRoot_map_surjective_of_surjective
    (ValuativeRel.valuation K).integer
    (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
    (algebraMap (ValuativeRel.valuation K).integer
      (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    IsLocalRing.residue_surjective f g (by
      rw [nonarchimedeanLocalField_residuePolynomial_algebraMap_eq K f g hfg])

/-- Reduction on units of an unramified integral root lift. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootReductionUnits
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g) :
    (AdjoinRoot f)ˣ →* (AdjoinRoot g)ˣ :=
  Units.map (nonarchimedeanLocalFieldAdjoinRootReductionMap K f g hfg).toMonoidHom

/-- Every residue root-unit lifts to an integral root-unit. -/
theorem nonarchimedeanLocalFieldAdjoinRootReductionUnits_surjective
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g) (hg : Irreducible g) :
    Function.Surjective (nonarchimedeanLocalFieldAdjoinRootReductionUnits K f g hfg) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : Fact (Irreducible g) := ⟨hg⟩
  letI : Field (AdjoinRoot g) := AdjoinRoot.instField
  let hred := nonarchimedeanLocalFieldAdjoinRootReductionMap_surjective K f g hfg
  let hred' : Function.Surjective
      (nonarchimedeanLocalFieldAdjoinRootReductionMap K f g hfg).toRingHom := hred
  let hlocal : IsLocalHom
      (nonarchimedeanLocalFieldAdjoinRootReductionMap K f g hfg).toRingHom :=
    IsLocalHom.of_surjective _ hred
  exact IsLocalRing.surjective_units_map_of_local_ringHom _ hred' hlocal

/-- Concrete coefficientwise reduction agrees with the canonical scalar-fiber map.  This turns
the tensor-fiber norm formula into a statement about actual reduction of integral classes. -/
theorem nonarchimedeanLocalFieldAdjoinRootReductionMap_eq_residueFiber
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g) (x : AdjoinRoot f) :
    nonarchimedeanLocalFieldAdjoinRootReductionMap K f g hfg x =
      adjoinRootScalarExtensionEquivOfMapEq (ValuativeRel.valuation K).integer
        (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) f g
        (nonarchimedeanLocalField_residuePolynomial_algebraMap_eq K f g hfg)
        ((1 : IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) ⊗ₜ[
          (ValuativeRel.valuation K).integer] x) := by
  let e := adjoinRootScalarExtensionEquivOfMapEq (ValuativeRel.valuation K).integer
    (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) f g
    (nonarchimedeanLocalField_residuePolynomial_algebraMap_eq K f g hfg)
  let psi : AdjoinRoot f →ₐ[(ValuativeRel.valuation K).integer] AdjoinRoot g :=
    e.toAlgHom.restrictScalars (ValuativeRel.valuation K).integer |>.comp
      Algebra.TensorProduct.includeRight
  change nonarchimedeanLocalFieldAdjoinRootReductionMap K f g hfg x = psi x
  have hmap : nonarchimedeanLocalFieldAdjoinRootReductionMap K f g hfg = psi := by
    apply AdjoinRoot.algHom_ext
    simp only [nonarchimedeanLocalFieldAdjoinRootReductionMap, AdjoinRoot.coe_mapAlgHom,
      AdjoinRoot.map_root]
    change AdjoinRoot.root g = e (1 ⊗ₜ[(ValuativeRel.valuation K).integer] AdjoinRoot.root f)
    simpa [e] using
      (adjoinRootScalarExtensionEquivOfMapEq_tmul_one_root
        (ValuativeRel.valuation K).integer
        (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) f g
        (nonarchimedeanLocalField_residuePolynomial_algebraMap_eq K f g hfg)).symm
  exact DFunLike.congr_fun hmap x

/-- The residue-fiber norm formula in the quotient-map presentation used by the existing finite
unramified root-lift construction. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_residueFiberNorm_of_quotientMapEq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (x : AdjoinRoot f) :
    Algebra.norm (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
      (adjoinRootScalarExtensionEquivOfMapEq (ValuativeRel.valuation K).integer
        (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) f g
        (nonarchimedeanLocalField_residuePolynomial_algebraMap_eq K f g hfg)
        ((1 : IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) ⊗ₜ[
          (ValuativeRel.valuation K).integer] x)) =
      algebraMap (ValuativeRel.valuation K).integer
        (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
          (Algebra.norm (ValuativeRel.valuation K).integer x) := by
  exact nonarchimedeanLocalFieldAdjoinRoot_residueFiberNorm K f hf g
    (nonarchimedeanLocalField_residuePolynomial_algebraMap_eq K f g hfg) x

/-- **Integral norm commutes with reduction in every finite unramified root lift.**  The
integral norm of an element of the lifted root algebra, reduced to the base residue field, is
the ordinary norm of its image in the residue root algebra.  This is the norm-compatibility
square needed to pass finite-field norm calculations to unramified local integral models. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_integralNorm_residueFiberNorm
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g) (x : AdjoinRoot f) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
    letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
    letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
      AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    Algebra.norm (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
      (adjoinRootScalarExtensionEquivOfMapEq (ValuativeRel.valuation K).integer
        (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) f g
        (nonarchimedeanLocalField_residuePolynomial_algebraMap_eq K f g hfg)
        ((1 : IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) ⊗ₜ[
          (ValuativeRel.valuation K).integer] x)) =
      algebraMap (ValuativeRel.valuation K).integer
        (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
          (Algebra.intNorm (ValuativeRel.valuation K).integer (AdjoinRoot f) x) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  rw [Algebra.intNorm_eq_norm]
  exact nonarchimedeanLocalFieldAdjoinRoot_residueFiberNorm_of_quotientMapEq K f hf g hfg x

/-- **Integral norm commutes with concrete reduction in every finite unramified root lift.**
This is the actual local norm/reduction square: reduce after taking the integral norm, or reduce
first and take the finite-residue field norm. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_integralNorm_reductionMap
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g) (x : AdjoinRoot f) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
    letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
    letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
      AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    Algebra.norm (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
      (nonarchimedeanLocalFieldAdjoinRootReductionMap K f g hfg x) =
      algebraMap (ValuativeRel.valuation K).integer
        (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
          (Algebra.intNorm (ValuativeRel.valuation K).integer (AdjoinRoot f) x) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  rw [nonarchimedeanLocalFieldAdjoinRootReductionMap_eq_residueFiber K f g hfg x]
  exact nonarchimedeanLocalFieldAdjoinRoot_integralNorm_residueFiberNorm K f hf g hgmonic hfg hg x

/-- **Integral trace commutes with concrete reduction in a finite root lift.**  This is the
linear companion of the norm/reduction square.  It identifies the trace on the finite residue
extension as the first-order map governing principal-unit norm lifting. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_integralTrace_reductionMap
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g) (x : AdjoinRoot f) :
    Algebra.trace (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) (AdjoinRoot g)
      (nonarchimedeanLocalFieldAdjoinRootReductionMap K f g hfg x) =
      algebraMap (ValuativeRel.valuation K).integer
        (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
          (Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x) := by
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  rw [nonarchimedeanLocalFieldAdjoinRootReductionMap_eq_residueFiber K f g hfg x]
  exact adjoinRootScalarExtensionEquivOfMapEq_trace_tmul_one
    (ValuativeRel.valuation K).integer
    (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) f g
    (nonarchimedeanLocalField_residuePolynomial_algebraMap_eq K f g hfg) x

/-- The trace of every finite residue root extension is surjective.  This is the residue-level
linear lifting fact needed for the successive principal-unit norm layers. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_residueTrace_surjective
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic) (hg : Irreducible g) :
    Function.Surjective
      (Algebra.trace (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) (AdjoinRoot g)) := by
  letI : Fact (Irreducible g) := ⟨hg⟩
  letI : Field (AdjoinRoot g) := AdjoinRoot.instField
  letI : Algebra (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
      (AdjoinRoot g) := AdjoinRoot.instAlgebra g
  letI : Module.Finite (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
      (AdjoinRoot g) := hgmonic.finite_adjoinRoot
  letI : Finite (AdjoinRoot g) := Module.finite_of_finite
    (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
  exact Algebra.trace_surjective
    (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) (AdjoinRoot g)

/-- Reduction of the integral trace from a finite unramified root lift is surjective.  Equivalently,
every residue-field first-order target has an integral preimage whose trace realizes it modulo the
maximal ideal. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_integralTrace_reduction_surjective
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g) (hg : Irreducible g) :
    Function.Surjective (fun x : AdjoinRoot f =>
      algebraMap (ValuativeRel.valuation K).integer
        (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
          (Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x)) := by
  intro a
  obtain ⟨y, hy⟩ := nonarchimedeanLocalFieldAdjoinRoot_residueTrace_surjective K g hgmonic hg a
  obtain ⟨x, hx⟩ := nonarchimedeanLocalFieldAdjoinRootReductionMap_surjective K f g hfg y
  refine ⟨x, ?_⟩
  change algebraMap (ValuativeRel.valuation K).integer
    (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
      (Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x) = a
  rw [← nonarchimedeanLocalFieldAdjoinRoot_integralTrace_reductionMap K f hf g hfg x, hx]
  exact hy

/-- **First-order local norm formula.**  For a maximal-ideal perturbation `a • x`, the norm
differs from `1 + a · trace(x)` only by a term in `𝔪²`.  This is the concrete linearization
whose residue trace controls the first principal-unit norm layer. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_norm_one_add_smul_sub_mem_maximalIdeal_sq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (a : (ValuativeRel.valuation K).integer)
    (ha : a ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer)
    (x : AdjoinRoot f) :
    Algebra.norm (ValuativeRel.valuation K).integer (1 + a • x) -
      (1 + Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x * a) ∈
        (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ 2 := by
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  obtain ⟨r, hr⟩ := Algebra.norm_one_add_smul a x
  rw [hr]
  have hrewrite :
      (1 + Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x * a + r * a ^ 2) -
        (1 + Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x * a) = r * a ^ 2 := by
    ring
  rw [hrewrite]
  exact ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ 2).mul_mem_left r
    ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer).pow_mem_pow ha 2)

/-- The first-order local norm formula as equality modulo the square of the maximal ideal. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_norm_one_add_smul_mod_maximalIdeal_sq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (a : (ValuativeRel.valuation K).integer)
    (ha : a ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer)
    (x : AdjoinRoot f) :
    Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ 2)
      (Algebra.norm (ValuativeRel.valuation K).integer (1 + a • x)) =
    Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ 2)
      (1 + Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x * a) := by
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact nonarchimedeanLocalFieldAdjoinRoot_norm_one_add_smul_sub_mem_maximalIdeal_sq K f hf a ha x

/-- **Higher first-order norm formula.**  On a perturbation from `𝔪ⁿ`, with `n > 0`, the norm
is linearized by the trace modulo `𝔪ⁿ⁺¹`. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_norm_one_add_smul_sub_mem_maximalIdeal_pow_succ
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (n : ℕ) (hn : 0 < n)
    (a : (ValuativeRel.valuation K).integer)
    (ha : a ∈ (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ n)
    (x : AdjoinRoot f) :
    Algebra.norm (ValuativeRel.valuation K).integer (1 + a • x) -
      (1 + Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x * a) ∈
        (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1) := by
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  obtain ⟨r, hr⟩ := Algebra.norm_one_add_smul a x
  rw [hr]
  have hrewrite :
      (1 + Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x * a + r * a ^ 2) -
        (1 + Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x * a) = r * a ^ 2 := by
    ring
  rw [hrewrite]
  have hsq : a ^ 2 ∈ (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + n) := by
    rw [pow_two, pow_add]
    exact Ideal.mul_mem_mul ha ha
  have herror : r * a ^ 2 ∈
      (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + n) :=
    ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + n)).mul_mem_left r hsq
  exact Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer)
    (Nat.add_le_add_left (Nat.succ_le_iff.mpr hn) n) herror

/-- **Higher infinitesimal norm lifting.**  Every trace coefficient modulo `𝔪` is attained by a
norm modulo `𝔪ⁿ⁺¹` along any direction from `𝔪ⁿ`, for `n > 0`. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_norm_one_add_smul_exists_sub_mem_maximalIdeal_pow_succ
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g)
    (n : ℕ) (hn : 0 < n)
    (a : (ValuativeRel.valuation K).integer)
    (ha : a ∈ (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ n)
    (b : (ValuativeRel.valuation K).integer) :
    ∃ x : AdjoinRoot f,
      Algebra.norm (ValuativeRel.valuation K).integer (1 + a • x) - (1 + b * a) ∈
        (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1) := by
  obtain ⟨x, hx⟩ := nonarchimedeanLocalFieldAdjoinRoot_integralTrace_reduction_surjective
    K f hf g hgmonic hfg hg
    (algebraMap (ValuativeRel.valuation K).integer
      (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) b)
  refine ⟨x, ?_⟩
  have htrace : Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x - b ∈
      IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer := by
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact hx
  have hnorm := nonarchimedeanLocalFieldAdjoinRoot_norm_one_add_smul_sub_mem_maximalIdeal_pow_succ
    K f hf n hn a ha x
  have htrace' : Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x - b ∈
      (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ 1 := by
    simpa using htrace
  have hlinear' :
      (Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x - b) * a ∈
        (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (1 + n) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul htrace' ha
  have hlinear :
      (Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x - b) * a ∈
        (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1) := by
    simpa [Nat.add_comm] using hlinear'
  have hrewrite :
      Algebra.norm (ValuativeRel.valuation K).integer (1 + a • x) - (1 + b * a) =
        (Algebra.norm (ValuativeRel.valuation K).integer (1 + a • x) -
          (1 + Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x * a)) +
        (Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x - b) * a := by
    ring
  rw [hrewrite]
  exact ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1)).add_mem
    hnorm hlinear

/-- A maximal-ideal perturbation of `1` is a unit in every finite unramified root lift.  This
places the first-order norm formula inside the actual local unit group. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_isUnit_one_add_smul
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g)
    (a : (ValuativeRel.valuation K).integer)
    (ha : a ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer)
    (x : AdjoinRoot f) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    IsUnit (1 + a • x) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  have hmap : algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f) a ∈
      IsLocalRing.maximalIdeal (AdjoinRoot f) :=
    map_nonunit (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) a ha
  have hax : a • x ∈ IsLocalRing.maximalIdeal (AdjoinRoot f) := by
    rw [Algebra.smul_def]
    exact (IsLocalRing.maximalIdeal (AdjoinRoot f)).mul_mem_right x hmap
  exact (IsLocalRing.isUnit_or_isUnit_of_add_one
    (show -(a • x) + (1 + a • x) = 1 by ring)).resolve_left
      (fun hunit => (IsLocalRing.notMem_maximalIdeal.mpr hunit)
        ((IsLocalRing.maximalIdeal (AdjoinRoot f)).neg_mem hax))

/-- **First-order integral-norm formula.**  In a finite unramified root lift, the integral norm
has trace as its linear term on maximal-ideal perturbations.  This is the form compatible with
the existing integral unit-norm homomorphism. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_integralNorm_one_add_smul_sub_mem_maximalIdeal_sq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g)
    (a : (ValuativeRel.valuation K).integer)
    (ha : a ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer)
    (x : AdjoinRoot f) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
    letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
    letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
      AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    Algebra.intNorm (ValuativeRel.valuation K).integer (AdjoinRoot f) (1 + a • x) -
        (1 + Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x * a) ∈
      (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ 2 := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  rw [Algebra.intNorm_eq_norm]
  exact nonarchimedeanLocalFieldAdjoinRoot_norm_one_add_smul_sub_mem_maximalIdeal_sq K f hf a ha x

/-- The first-order integral-norm formula as equality modulo `𝔪²`. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_integralNorm_one_add_smul_mod_maximalIdeal_sq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g)
    (a : (ValuativeRel.valuation K).integer)
    (ha : a ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer)
    (x : AdjoinRoot f) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
    letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
    letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
      AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ 2)
      (Algebra.intNorm (ValuativeRel.valuation K).integer (AdjoinRoot f) (1 + a • x)) =
    Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ 2)
      (1 + Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x * a) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact nonarchimedeanLocalFieldAdjoinRoot_integralNorm_one_add_smul_sub_mem_maximalIdeal_sq
    K f hf g hgmonic hfg hg a ha x

/-- **First infinitesimal norm lifting.**  Every prescribed trace coefficient modulo the maximal
ideal is attained by a norm modulo `𝔪²`: for `a ∈ 𝔪`, the target `1 + a b` is congruent to
`N(1 + a x)` for a suitable `x` in the root lift.  With a uniformizer for `a`, this is precisely
the first principal-unit layer of the unramified local norm map. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_norm_one_add_smul_exists_sub_mem_maximalIdeal_sq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g)
    (a : (ValuativeRel.valuation K).integer)
    (ha : a ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer)
    (b : (ValuativeRel.valuation K).integer) :
    ∃ x : AdjoinRoot f,
      Algebra.norm (ValuativeRel.valuation K).integer (1 + a • x) - (1 + b * a) ∈
        (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ 2 := by
  obtain ⟨x, hx⟩ := nonarchimedeanLocalFieldAdjoinRoot_integralTrace_reduction_surjective
    K f hf g hgmonic hfg hg
    (algebraMap (ValuativeRel.valuation K).integer
      (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) b)
  refine ⟨x, ?_⟩
  have htrace : Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x - b ∈
      IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer := by
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact hx
  have hnorm := nonarchimedeanLocalFieldAdjoinRoot_norm_one_add_smul_sub_mem_maximalIdeal_sq
    K f hf a ha x
  have hlinear :
      (Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x - b) * a ∈
        (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ 2 := by
    simpa [pow_two] using Ideal.mul_mem_mul htrace ha
  have hrewrite :
      Algebra.norm (ValuativeRel.valuation K).integer (1 + a • x) - (1 + b * a) =
        (Algebra.norm (ValuativeRel.valuation K).integer (1 + a • x) -
          (1 + Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x * a)) +
        (Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x - b) * a := by
    ring
  rw [hrewrite]
  exact ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ 2).add_mem hnorm hlinear

/-- The first infinitesimal norm lifting statement as an equality in the `𝔪²` quotient. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_norm_one_add_smul_exists_mod_maximalIdeal_sq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g)
    (a : (ValuativeRel.valuation K).integer)
    (ha : a ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer)
    (b : (ValuativeRel.valuation K).integer) :
    ∃ x : AdjoinRoot f,
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ 2)
        (Algebra.norm (ValuativeRel.valuation K).integer (1 + a • x)) =
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ 2)
        (1 + b * a) := by
  obtain ⟨x, hx⟩ :=
    nonarchimedeanLocalFieldAdjoinRoot_norm_one_add_smul_exists_sub_mem_maximalIdeal_sq
      K f hf g hgmonic hfg hg a ha b
  refine ⟨x, ?_⟩
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact hx

/-- The first infinitesimal lifting result for the integral norm of an unramified root lift. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_integralNorm_one_add_smul_exists_sub_mem_maximalIdeal_sq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g)
    (a : (ValuativeRel.valuation K).integer)
    (ha : a ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer)
    (b : (ValuativeRel.valuation K).integer) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
    letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
    letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
      AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    ∃ x : AdjoinRoot f,
      Algebra.intNorm (ValuativeRel.valuation K).integer (AdjoinRoot f) (1 + a • x) -
        (1 + b * a) ∈ (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ 2 := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  obtain ⟨x, hx⟩ :=
    nonarchimedeanLocalFieldAdjoinRoot_norm_one_add_smul_exists_sub_mem_maximalIdeal_sq
      K f hf g hgmonic hfg hg a ha b
  refine ⟨x, ?_⟩
  rw [Algebra.intNorm_eq_norm]
  exact hx

/-- Integral norm on units followed by reduction to the base residue field. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootIntegralNormReductionUnits
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g) :
    (AdjoinRoot f)ˣ →* (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)ˣ := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  exact (nonarchimedeanLocalFieldReductionUnits K).comp
    (Units.map (Algebra.intNorm (ValuativeRel.valuation K).integer (AdjoinRoot f)))

/-- Multiplicative presentation of the integral unit norm. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootIntegralNormUnitsMul
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g) : (AdjoinRoot f)ˣ →* (ValuativeRel.valuation K).integerˣ where
  toFun b := (nonarchimedeanLocalFieldAdjoinRootIntegralNormUnits K f hf g hgmonic hfg hg
    (Additive.ofMul b)).toMul
  map_one' := by
    apply Additive.toMul.injective
    change nonarchimedeanLocalFieldAdjoinRootIntegralNormUnits K f hf g hgmonic hfg hg
      (Additive.ofMul 1) = Additive.ofMul 1
    exact (nonarchimedeanLocalFieldAdjoinRootIntegralNormUnits K f hf g hgmonic hfg hg).map_zero
  map_mul' b c := by
    apply Additive.toMul.injective
    change nonarchimedeanLocalFieldAdjoinRootIntegralNormUnits K f hf g hgmonic hfg hg
      (Additive.ofMul (b * c)) =
      (nonarchimedeanLocalFieldAdjoinRootIntegralNormUnits K f hf g hgmonic hfg hg
        (Additive.ofMul b)) +
      (nonarchimedeanLocalFieldAdjoinRootIntegralNormUnits K f hf g hgmonic hfg hg
        (Additive.ofMul c))
    change nonarchimedeanLocalFieldAdjoinRootIntegralNormUnits K f hf g hgmonic hfg hg
      (Additive.ofMul b + Additive.ofMul c) = _
    exact (nonarchimedeanLocalFieldAdjoinRootIntegralNormUnits K f hf g hgmonic hfg hg).map_add _ _

/-- **First principal-unit norm layer is surjective.**  Every target `1 + a b` with
`a ∈ 𝔪` is an integral norm of a source unit modulo `𝔪²`.  When `a` is a uniformizer, this is
surjectivity on the full first principal-unit quotient. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_integralNormUnitsMul_one_add_smul_exists_sub_mem_maximalIdeal_sq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g)
    (a : (ValuativeRel.valuation K).integer)
    (ha : a ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer)
    (b : (ValuativeRel.valuation K).integer) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
    letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
    letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
      AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    ∃ u : (AdjoinRoot f)ˣ,
      ((nonarchimedeanLocalFieldAdjoinRootIntegralNormUnitsMul K f hf g hgmonic hfg hg u :
        (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) -
        (1 + b * a) ∈ (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ 2 := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  obtain ⟨x, hx⟩ :=
    nonarchimedeanLocalFieldAdjoinRoot_integralNorm_one_add_smul_exists_sub_mem_maximalIdeal_sq
      K f hf g hgmonic hfg hg a ha b
  have hu : IsUnit (1 + a • x) :=
    nonarchimedeanLocalFieldAdjoinRoot_isUnit_one_add_smul K f hf g hfg hg a ha x
  refine ⟨hu.unit, ?_⟩
  change Algebra.intNorm (ValuativeRel.valuation K).integer (AdjoinRoot f) (1 + a • x) -
    (1 + b * a) ∈ (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ 2
  exact hx

/-- The principal-unit group of the finite unramified root lift. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootPrincipalUnitGroup
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g) : Subgroup (AdjoinRoot f)ˣ :=
  (nonarchimedeanLocalFieldAdjoinRootReductionUnits K f g hfg).ker

/-- The `n`th principal-unit congruence subgroup in a finite unramified root lift. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g) (n : ℕ) : Subgroup (AdjoinRoot f)ˣ := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  exact (Units.map (Ideal.Quotient.mk
    ((IsLocalRing.maximalIdeal (AdjoinRoot f)) ^ n)).toMonoidHom).ker

/-- Membership in a root principal-unit layer is congruence to `1` modulo the corresponding
root maximal-ideal power. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_mem_principalUnitFiltration_iff
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g) (n : ℕ) (u : (AdjoinRoot f)ˣ) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    u ∈ nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg n ↔
      (u : AdjoinRoot f) - 1 ∈ (IsLocalRing.maximalIdeal (AdjoinRoot f)) ^ n := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  simp only [nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration,
    MonoidHom.mem_ker, Units.ext_iff]
  change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (AdjoinRoot f)) ^ n)
    (u : AdjoinRoot f) = 1 ↔ _
  exact Ideal.Quotient.mk_eq_one_iff_sub_mem _

/-- Higher root principal-unit layers are nested. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_principalUnitFiltration_antitone
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    Antitone (nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  intro m n hmn u hu
  rw [nonarchimedeanLocalFieldAdjoinRoot_mem_principalUnitFiltration_iff] at hu ⊢
  exact Ideal.pow_le_pow_right hmn hu

/-- Two root units agree modulo the `n`th maximal-ideal power exactly when their quotient lies
in the `n`th root principal-unit layer. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_unit_div_mem_principalUnitFiltration_iff_sub_mem
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g) (n : ℕ) (u v : (AdjoinRoot f)ˣ) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    u⁻¹ * v ∈ nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg n ↔
      (v : AdjoinRoot f) - (u : AdjoinRoot f) ∈ (IsLocalRing.maximalIdeal (AdjoinRoot f)) ^ n := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  rw [nonarchimedeanLocalFieldAdjoinRoot_mem_principalUnitFiltration_iff]
  constructor
  · intro huv
    have hmul : (u : AdjoinRoot f) * (((u⁻¹ * v : (AdjoinRoot f)ˣ) : AdjoinRoot f) - 1) ∈
        (IsLocalRing.maximalIdeal (AdjoinRoot f)) ^ n :=
      ((IsLocalRing.maximalIdeal (AdjoinRoot f)) ^ n).mul_mem_left _ huv
    convert hmul using 1
    change (u : AdjoinRoot f) * (((u⁻¹ : (AdjoinRoot f)ˣ) : AdjoinRoot f) *
      (v : AdjoinRoot f) - 1) = (v : AdjoinRoot f) - (u : AdjoinRoot f)
    rw [mul_sub, mul_assoc, Units.mul_inv, one_mul, mul_one]
  · intro huv
    have hmul : ((u⁻¹ : (AdjoinRoot f)ˣ) : AdjoinRoot f) *
        ((v : AdjoinRoot f) - (u : AdjoinRoot f)) ∈
        (IsLocalRing.maximalIdeal (AdjoinRoot f)) ^ n :=
      ((IsLocalRing.maximalIdeal (AdjoinRoot f)) ^ n).mul_mem_left _ huv
    convert hmul using 1
    change ((u⁻¹ : (AdjoinRoot f)ˣ) : AdjoinRoot f) * (v : AdjoinRoot f) - 1 =
      ((u⁻¹ : (AdjoinRoot f)ˣ) : AdjoinRoot f) *
        ((v : AdjoinRoot f) - (u : AdjoinRoot f))
    rw [mul_sub, Units.inv_mul]

/-- Every root `Uⁿ` element has a uniformizer-coordinate presentation `1 + πⁿx`, where `π`
is a base uniformizer.  This is the filtration-level content of unramifiedness. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_principalUnitFiltration_uniformizer_factor
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g) (n : ℕ)
    (u : nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg n) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    ∃ π : (ValuativeRel.valuation K).integer, ∃ x : AdjoinRoot f,
      Irreducible π ∧ π ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer ∧
        ((u : (AdjoinRoot f)ˣ) : AdjoinRoot f) = 1 + π ^ n • x := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
    (ValuativeRel.valuation K).integer
  have hπmem : π ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer := by
    rw [hπ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self π
  have hu : ((u : (AdjoinRoot f)ˣ) : AdjoinRoot f) - 1 ∈
      (IsLocalRing.maximalIdeal (AdjoinRoot f)) ^ n :=
    (nonarchimedeanLocalFieldAdjoinRoot_mem_principalUnitFiltration_iff K f hf g hfg hg n
      (u : (AdjoinRoot f)ˣ)).mp u.2
  have hmap := nonarchimedeanLocalFieldAdjoinRoot_map_maximalIdeal K f hf g hfg hg
  rw [← hmap, ← Ideal.map_pow, hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.map_span, Set.image_singleton] at hu
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp hu
  refine ⟨π, x, hπ, hπmem, ?_⟩
  calc
    ((u : (AdjoinRoot f)ˣ) : AdjoinRoot f) =
        1 + (((u : (AdjoinRoot f)ˣ) : AdjoinRoot f) - 1) := by ring
    _ = 1 + (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f) (π ^ n)) * x := by
      rw [← hx, mul_comm x]
    _ = 1 + π ^ n • x := by rw [Algebra.smul_def]

/-- A uniformizer-coordinate perturbation `1 + πⁿx` belongs to the `n`th root principal-unit
layer. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_one_add_uniformizer_pow_mem_principalUnitFiltration
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g) (n : ℕ)
    (π : (ValuativeRel.valuation K).integer)
    (hπ : π ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer)
    (x : AdjoinRoot f) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    ∀ hu : IsUnit (1 + π ^ n • x), hu.unit ∈
      nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg n := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  intro hu
  rw [nonarchimedeanLocalFieldAdjoinRoot_mem_principalUnitFiltration_iff]
  rw [show (hu.unit : AdjoinRoot f) = 1 + π ^ n • x from hu.unit_spec]
  simp only [add_sub_cancel_left]
  rw [Algebra.smul_def]
  have hmap : algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f) π ∈
      IsLocalRing.maximalIdeal (AdjoinRoot f) :=
    map_nonunit (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) π hπ
  have hpow : (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f) π) ^ n ∈
      (IsLocalRing.maximalIdeal (AdjoinRoot f)) ^ n := Ideal.pow_mem_pow hmap n
  simpa only [map_pow] using
    ((IsLocalRing.maximalIdeal (AdjoinRoot f)) ^ n).mul_mem_right x hpow

/-- The unit `1 + a x` is principal in the root lift whenever `a` belongs to the base maximal
ideal. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_one_add_smul_mem_principalUnitGroup
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g)
    (a : (ValuativeRel.valuation K).integer)
    (ha : a ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer)
    (x : AdjoinRoot f) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    ∀ hu : IsUnit (1 + a • x), hu.unit ∈
      nonarchimedeanLocalFieldAdjoinRootPrincipalUnitGroup K f g hfg := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  intro hu
  change nonarchimedeanLocalFieldAdjoinRootReductionUnits K f g hfg hu.unit = 1
  apply Units.ext
  change nonarchimedeanLocalFieldAdjoinRootReductionMap K f g hfg (1 + a • x) = 1
  rw [map_add, map_one, nonarchimedeanLocalFieldAdjoinRootReductionMap_smul_eq_zero K f g hfg a ha x]
  simp

/-- Reduction and the integral norm commute on unit groups. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_integralNormReductionUnits_eq_residueNorm
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g) (b : (AdjoinRoot f)ˣ) :
    nonarchimedeanLocalFieldAdjoinRootIntegralNormReductionUnits K f hf g hgmonic hfg hg b =
      Units.map (Algebra.norm (IsLocalRing.ResidueField
        (ValuativeRel.valuation K).integer))
        (nonarchimedeanLocalFieldAdjoinRootReductionUnits K f g hfg b) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  apply Units.ext
  change algebraMap (ValuativeRel.valuation K).integer
      (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
      (Algebra.intNorm (ValuativeRel.valuation K).integer (AdjoinRoot f) (b : AdjoinRoot f)) =
    Algebra.norm (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
      (nonarchimedeanLocalFieldAdjoinRootReductionMap K f g hfg (b : AdjoinRoot f))
  exact (nonarchimedeanLocalFieldAdjoinRoot_integralNorm_reductionMap
    K f hf g hgmonic hfg hg (b : AdjoinRoot f)).symm

/-- The integral norm takes root principal units to base principal units. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_integralNorm_maps_principalUnitGroup
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g)
    (b : nonarchimedeanLocalFieldAdjoinRootPrincipalUnitGroup K f g hfg) :
    nonarchimedeanLocalFieldAdjoinRootIntegralNormUnitsMul K f hf g hgmonic hfg hg b ∈
      nonarchimedeanLocalFieldPrincipalUnitGroup K := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  change nonarchimedeanLocalFieldReductionUnits K
    (nonarchimedeanLocalFieldAdjoinRootIntegralNormUnitsMul K f hf g hgmonic hfg hg b) = 1
  change nonarchimedeanLocalFieldReductionUnits K
    (Units.map (Algebra.intNorm (ValuativeRel.valuation K).integer (AdjoinRoot f)) b) = 1
  change nonarchimedeanLocalFieldAdjoinRootIntegralNormReductionUnits K f hf g hgmonic hfg hg b = 1
  rw [nonarchimedeanLocalFieldAdjoinRoot_integralNormReductionUnits_eq_residueNorm
    K f hf g hgmonic hfg hg]
  rw [show nonarchimedeanLocalFieldAdjoinRootReductionUnits K f g hfg b = 1 from b.2]
  exact map_one _

/-- Integral norm restricted to principal units in the unramified root lift. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnits
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g) :
    nonarchimedeanLocalFieldAdjoinRootPrincipalUnitGroup K f g hfg →*
      nonarchimedeanLocalFieldPrincipalUnitGroup K := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  exact ((nonarchimedeanLocalFieldAdjoinRootIntegralNormUnitsMul K f hf g hgmonic hfg hg).comp
    (Subgroup.subtype (nonarchimedeanLocalFieldAdjoinRootPrincipalUnitGroup K f g hfg))).codRestrict
    (nonarchimedeanLocalFieldPrincipalUnitGroup K)
    (nonarchimedeanLocalFieldAdjoinRoot_integralNorm_maps_principalUnitGroup
      K f hf g hgmonic hfg hg)

/-- The integral norm preserves every positive principal-unit congruence layer in a finite
unramified root lift. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_integralNormUnits_maps_principalUnitFiltration
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g)
    (n : ℕ) (hn : 0 < n)
    (v : nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg n) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
    letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
    letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
      AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    nonarchimedeanLocalFieldAdjoinRootIntegralNormUnitsMul K f hf g hgmonic hfg hg v ∈
      nonarchimedeanLocalFieldPrincipalUnitFiltration K n := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  obtain ⟨π, x, _, hπmem, hv⟩ :=
    nonarchimedeanLocalFieldAdjoinRoot_principalUnitFiltration_uniformizer_factor
      K f hf g hfg hg n v
  have hπpow : π ^ n ∈ (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ n :=
    Ideal.pow_mem_pow hπmem n
  have hnorm := nonarchimedeanLocalFieldAdjoinRoot_norm_one_add_smul_sub_mem_maximalIdeal_pow_succ
    K f hf n hn (π ^ n) hπpow x
  have herror : Algebra.norm (ValuativeRel.valuation K).integer (1 + π ^ n • x) -
      (1 + Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x * π ^ n) ∈
        (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ n :=
    Ideal.pow_le_pow_right (Nat.le_succ n) hnorm
  have hlinear : Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x * π ^ n ∈
      (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ n :=
    ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ n).mul_mem_left _ hπpow
  rw [nonarchimedeanLocalField_mem_principalUnitFiltration_iff]
  change Algebra.intNorm (ValuativeRel.valuation K).integer (AdjoinRoot f)
      ((v : nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg n) :
        (AdjoinRoot f)ˣ) - 1 ∈
    (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ n
  rw [show (((v : nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg n) :
      (AdjoinRoot f)ˣ) : AdjoinRoot f) = 1 + π ^ n • x from hv]
  rw [Algebra.intNorm_eq_norm]
  have hrewrite : Algebra.norm (ValuativeRel.valuation K).integer (1 + π ^ n • x) - 1 =
      (Algebra.norm (ValuativeRel.valuation K).integer (1 + π ^ n • x) -
        (1 + Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x * π ^ n)) +
        Algebra.trace (ValuativeRel.valuation K).integer (AdjoinRoot f) x * π ^ n := by
    ring
  rw [hrewrite]
  exact ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ n).add_mem herror hlinear

/-- Integral norm restricted to the `n`th principal-unit congruence layers of a finite
unramified root lift. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnitFiltration
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g)
    (n : ℕ) (hn : 0 < n) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
    letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
    letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
      AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg n →*
      nonarchimedeanLocalFieldPrincipalUnitFiltration K n := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  exact ((nonarchimedeanLocalFieldAdjoinRootIntegralNormUnitsMul K f hf g hgmonic hfg hg).comp
    (Subgroup.subtype (nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg n))).codRestrict
    (nonarchimedeanLocalFieldPrincipalUnitFiltration K n)
    (nonarchimedeanLocalFieldAdjoinRoot_integralNormUnits_maps_principalUnitFiltration
      K f hf g hgmonic hfg hg n hn)

/-- The integral norm induced on the successive principal-unit quotients
`U_Bⁿ / U_Bⁿ⁺¹ → U_Aⁿ / U_Aⁿ⁺¹`. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnitGraded
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g)
    (n : ℕ) (hn : 0 < n) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
    letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
    letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
      AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    (nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg n) ⧸
      (nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg (n + 1)).subgroupOf
        (nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg n) →*
      (nonarchimedeanLocalFieldPrincipalUnitFiltration K n) ⧸
        (nonarchimedeanLocalFieldPrincipalUnitFiltration K (n + 1)).subgroupOf
          (nonarchimedeanLocalFieldPrincipalUnitFiltration K n) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  apply QuotientGroup.map
    ((nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg (n + 1)).subgroupOf
      (nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg n))
    ((nonarchimedeanLocalFieldPrincipalUnitFiltration K (n + 1)).subgroupOf
      (nonarchimedeanLocalFieldPrincipalUnitFiltration K n))
    (nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnitFiltration
      K f hf g hgmonic hfg hg n hn)
  intro v hv
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  let v' : nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg (n + 1) :=
    ⟨(v : nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg n), hv⟩
  simpa [nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnitFiltration] using
    (nonarchimedeanLocalFieldAdjoinRoot_integralNormUnits_maps_principalUnitFiltration
      K f hf g hgmonic hfg hg (n + 1) (Nat.succ_pos n) v')

/-- **Principal-unit norm lifting modulo `𝔪²`.**  For every `a ∈ 𝔪` and coefficient `b`, a
source principal unit has norm congruent to `1 + a b` modulo `𝔪²`.  Thus, after choosing a
uniformizer for `a`, the unramified local norm is surjective on its first principal-unit quotient. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_integralNormPrincipalUnits_one_add_smul_exists_sub_mem_maximalIdeal_sq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g)
    (a : (ValuativeRel.valuation K).integer)
    (ha : a ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer)
    (b : (ValuativeRel.valuation K).integer) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
    letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
    letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
      AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    ∃ u : nonarchimedeanLocalFieldAdjoinRootPrincipalUnitGroup K f g hfg,
      ((nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnits K f hf g hgmonic hfg hg u :
        (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) -
        (1 + b * a) ∈ (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ 2 := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  obtain ⟨x, hx⟩ :=
    nonarchimedeanLocalFieldAdjoinRoot_integralNorm_one_add_smul_exists_sub_mem_maximalIdeal_sq
      K f hf g hgmonic hfg hg a ha b
  have hu : IsUnit (1 + a • x) :=
    nonarchimedeanLocalFieldAdjoinRoot_isUnit_one_add_smul K f hf g hfg hg a ha x
  let u : nonarchimedeanLocalFieldAdjoinRootPrincipalUnitGroup K f g hfg :=
    ⟨hu.unit,
      nonarchimedeanLocalFieldAdjoinRoot_one_add_smul_mem_principalUnitGroup
        K f hf g hfg hg a ha x hu⟩
  refine ⟨u, ?_⟩
  change Algebra.intNorm (ValuativeRel.valuation K).integer (AdjoinRoot f) (1 + a • x) -
    (1 + b * a) ∈ (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ 2
  exact hx

/-- **Higher principal-unit norm lifting.**  For every `a ∈ 𝔪ⁿ`, with `n > 0`, and every
coefficient `b`, a source principal unit has norm congruent to `1 + a b` modulo `𝔪ⁿ⁺¹`. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_integralNormPrincipalUnits_one_add_smul_exists_sub_mem_maximalIdeal_pow_succ
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g)
    (n : ℕ) (hn : 0 < n)
    (a : (ValuativeRel.valuation K).integer)
    (ha : a ∈ (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ n)
    (b : (ValuativeRel.valuation K).integer) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
    letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
    letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
      AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    ∃ u : nonarchimedeanLocalFieldAdjoinRootPrincipalUnitGroup K f g hfg,
      ((nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnits K f hf g hgmonic hfg hg u :
        (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) -
        (1 + b * a) ∈ (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  obtain ⟨x, hx⟩ :=
    nonarchimedeanLocalFieldAdjoinRoot_norm_one_add_smul_exists_sub_mem_maximalIdeal_pow_succ
      K f hf g hgmonic hfg hg n hn a ha b
  have haone : a ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer := by
    simpa using Ideal.pow_le_pow_right
      (I := IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer)
      (Nat.succ_le_iff.mpr hn) ha
  have hu : IsUnit (1 + a • x) :=
    nonarchimedeanLocalFieldAdjoinRoot_isUnit_one_add_smul K f hf g hfg hg a haone x
  let u : nonarchimedeanLocalFieldAdjoinRootPrincipalUnitGroup K f g hfg :=
    ⟨hu.unit,
      nonarchimedeanLocalFieldAdjoinRoot_one_add_smul_mem_principalUnitGroup
        K f hf g hfg hg a haone x hu⟩
  refine ⟨u, ?_⟩
  change Algebra.intNorm (ValuativeRel.valuation K).integer (AdjoinRoot f) (1 + a • x) -
    (1 + b * a) ∈ (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1)
  rw [Algebra.intNorm_eq_norm]
  exact hx

/-- **Higher target-layer norm representability.**  Every `Uⁿ` target unit, with `n > 0`, is
congruent modulo `Uⁿ⁺¹` to the norm of a source principal unit.  The witness is constructed as
`1 + πⁿx` for a DVR uniformizer `π`. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_integralNormPrincipalUnits_filtration_exists_mod_maximalIdeal_pow_succ
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g)
    (n : ℕ) (hn : 0 < n)
    (u : nonarchimedeanLocalFieldPrincipalUnitFiltration K n) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
    letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
    letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
      AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    ∃ v : nonarchimedeanLocalFieldAdjoinRootPrincipalUnitGroup K f g hfg,
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1))
        ((nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnits K f hf g hgmonic hfg hg v :
          (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) =
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1))
        ((u : (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  obtain ⟨π, b, _, hπmem, hu⟩ :=
    nonarchimedeanLocalField_principalUnitFiltration_uniformizer_factor K n u
  have hπpow : π ^ n ∈ (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ n :=
    Ideal.pow_mem_pow hπmem n
  obtain ⟨v, hv⟩ :=
    nonarchimedeanLocalFieldAdjoinRoot_integralNormPrincipalUnits_one_add_smul_exists_sub_mem_maximalIdeal_pow_succ
      K f hf g hgmonic hfg hg n hn (π ^ n) hπpow b
  refine ⟨v, ?_⟩
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, hu]
  exact hv

/-- **Higher source-and-target-layer norm representability.** Every target `Uⁿ` class, for
`n > 0`, is represented modulo `Uⁿ⁺¹` by the norm of an actual source `Uⁿ` unit.  This is the
graded lifting step; compatibility of these representatives through all layers remains separate. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_integralNormUnits_filtration_exists_mod_maximalIdeal_pow_succ
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g)
    (n : ℕ) (hn : 0 < n)
    (u : nonarchimedeanLocalFieldPrincipalUnitFiltration K n) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
    letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
    letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
      AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    ∃ v : nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg n,
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1))
        ((nonarchimedeanLocalFieldAdjoinRootIntegralNormUnitsMul K f hf g hgmonic hfg hg v :
          (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) =
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1))
        ((u : (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  obtain ⟨π, b, _, hπmem, hu⟩ :=
    nonarchimedeanLocalField_principalUnitFiltration_uniformizer_factor K n u
  have hπpow : π ^ n ∈ (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ n :=
    Ideal.pow_mem_pow hπmem n
  obtain ⟨x, hx⟩ :=
    nonarchimedeanLocalFieldAdjoinRoot_norm_one_add_smul_exists_sub_mem_maximalIdeal_pow_succ
      K f hf g hgmonic hfg hg n hn (π ^ n) hπpow b
  have hπpowone : π ^ n ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer := by
    simpa using Ideal.pow_le_pow_right
      (I := IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer)
      (Nat.succ_le_iff.mpr hn) hπpow
  have hvunit : IsUnit (1 + π ^ n • x) :=
    nonarchimedeanLocalFieldAdjoinRoot_isUnit_one_add_smul K f hf g hfg hg (π ^ n) hπpowone x
  let v : nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg n :=
    ⟨hvunit.unit,
      nonarchimedeanLocalFieldAdjoinRoot_one_add_uniformizer_pow_mem_principalUnitFiltration
        K f hf g hfg hg n π hπmem x hvunit⟩
  refine ⟨v, ?_⟩
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, hu]
  change Algebra.intNorm (ValuativeRel.valuation K).integer (AdjoinRoot f) (1 + π ^ n • x) -
    (1 + b * π ^ n) ∈ (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1)
  rw [Algebra.intNorm_eq_norm]
  exact hx

/-- The integral norm is surjective on every positive successive principal-unit quotient of a
finite unramified root lift. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_integralNormPrincipalUnitGraded_surjective
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g)
    (n : ℕ) (hn : 0 < n) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
    letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
    letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
      AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    Function.Surjective
      (nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnitGraded
        K f hf g hgmonic hfg hg n hn) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  intro q
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective
    ((nonarchimedeanLocalFieldPrincipalUnitFiltration K (n + 1)).subgroupOf
      (nonarchimedeanLocalFieldPrincipalUnitFiltration K n)) q
  obtain ⟨v, hv⟩ :=
    nonarchimedeanLocalFieldAdjoinRoot_integralNormUnits_filtration_exists_mod_maximalIdeal_pow_succ
      K f hf g hgmonic hfg hg n hn u
  let N := nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnitFiltration
    K f hf g hgmonic hfg hg n hn v
  have hq : Units.map (Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1))).toMonoidHom
      (N : (ValuativeRel.valuation K).integerˣ) =
      Units.map (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1))).toMonoidHom
        (u : (ValuativeRel.valuation K).integerˣ) := by
    apply Units.ext
    change Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1))
        ((N : (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) =
      Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1))
          ((u : (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer)
    simpa [N, nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnitFiltration] using hv
  let z : nonarchimedeanLocalFieldPrincipalUnitFiltration K n := N⁻¹ * u
  have hz : (z : (ValuativeRel.valuation K).integerˣ) ∈
      nonarchimedeanLocalFieldPrincipalUnitFiltration K (n + 1) := by
    change Units.map (Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1))).toMonoidHom
        (z : (ValuativeRel.valuation K).integerˣ) = 1
    change Units.map (Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1))).toMonoidHom
        ((N : (ValuativeRel.valuation K).integerˣ)⁻¹ *
          (u : (ValuativeRel.valuation K).integerˣ)) = 1
    rw [map_mul, map_inv, hq, inv_mul_cancel]
  refine ⟨QuotientGroup.mk'
    ((nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg (n + 1)).subgroupOf
      (nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg n)) v, ?_⟩
  rw [show nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnitGraded
      K f hf g hgmonic hfg hg n hn =
      QuotientGroup.map
        ((nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg (n + 1)).subgroupOf
          (nonarchimedeanLocalFieldAdjoinRootPrincipalUnitFiltration K f hf g hfg hg n))
        ((nonarchimedeanLocalFieldPrincipalUnitFiltration K (n + 1)).subgroupOf
          (nonarchimedeanLocalFieldPrincipalUnitFiltration K n))
        (nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnitFiltration
          K f hf g hgmonic hfg hg n hn) _ from rfl,
    QuotientGroup.map_mk']
  apply (QuotientGroup.mk'_eq_mk'
    ((nonarchimedeanLocalFieldPrincipalUnitFiltration K (n + 1)).subgroupOf
      (nonarchimedeanLocalFieldPrincipalUnitFiltration K n))).mpr
  refine ⟨z, Subgroup.mem_subgroupOf.mpr hz, ?_⟩
  change N * (N⁻¹ * u) = u
  group

/-- **First principal-unit quotient norm surjectivity.**  Every base principal unit is congruent
modulo `𝔪²` to the norm of a source principal unit.  Equivalently, the unramified local
principal-unit norm is surjective on `U¹/U²`. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_integralNormPrincipalUnits_mod_maximalIdeal_sq_surjective
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g)
    (u : nonarchimedeanLocalFieldPrincipalUnitGroup K) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
    letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
    letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
      AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    ∃ v : nonarchimedeanLocalFieldAdjoinRootPrincipalUnitGroup K f g hfg,
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ 2)
        ((nonarchimedeanLocalFieldAdjoinRootIntegralNormPrincipalUnits K f hf g hgmonic hfg hg v :
          (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) =
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ 2)
        ((u : (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  obtain ⟨π, b, _, hπmem, hu⟩ :=
    nonarchimedeanLocalField_principalUnit_uniformizer_factor K u
  obtain ⟨v, hv⟩ :=
    nonarchimedeanLocalFieldAdjoinRoot_integralNormPrincipalUnits_one_add_smul_exists_sub_mem_maximalIdeal_sq
      K f hf g hgmonic hfg hg π hπmem b
  refine ⟨v, ?_⟩
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, hu]
  exact hv

/-- **Norms are surjective modulo principal units in every finite unramified root lift.**
Equivalently, every unit of the base residue field is the reduction of an integral norm of a
unit of the lifted root algebra.  The remaining local-class-field-theory step is norm control
on principal units. -/
theorem nonarchimedeanLocalFieldAdjoinRootIntegralNormReductionUnits_surjective
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g) :
    Function.Surjective
      (nonarchimedeanLocalFieldAdjoinRootIntegralNormReductionUnits
        K f hf g hgmonic hfg hg) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  letI : Fact (Irreducible g) := ⟨hg⟩
  letI : Field (AdjoinRoot g) := AdjoinRoot.instField
  letI : Algebra (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
      (AdjoinRoot g) := AdjoinRoot.instAlgebra g
  letI : Module.Finite (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
      (AdjoinRoot g) := hgmonic.finite_adjoinRoot
  letI : Finite (AdjoinRoot g) := Module.finite_of_finite
    (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
  intro z
  obtain ⟨y, hy⟩ := FiniteField.unitsMap_norm_surjective
    (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) (AdjoinRoot g) z
  obtain ⟨u, hu⟩ :=
    nonarchimedeanLocalFieldAdjoinRootReductionUnits_surjective K f hf g hfg hg y
  refine ⟨u, ?_⟩
  change (nonarchimedeanLocalFieldReductionUnits K)
    (Units.map (Algebra.intNorm (ValuativeRel.valuation K).integer (AdjoinRoot f)) u) = z
  apply Units.ext
  change algebraMap (ValuativeRel.valuation K).integer
    (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
      (Algebra.intNorm (ValuativeRel.valuation K).integer (AdjoinRoot f)
        (u : AdjoinRoot f)) =
      (z : IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
  rw [← nonarchimedeanLocalFieldAdjoinRoot_integralNorm_reductionMap
    K f hf g hgmonic hfg hg (u : AdjoinRoot f)]
  have huval := congrArg Units.val hu
  change nonarchimedeanLocalFieldAdjoinRootReductionMap K f g hfg (u : AdjoinRoot f) =
    (y : AdjoinRoot g) at huval
  rw [huval]
  have hyval := congrArg Units.val hy
  change Algebra.norm (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
    (y : AdjoinRoot g) =
      (z : IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) at hyval
  exact hyval

/-- **Every unramified integral unit is a norm times a principal unit.**  Thus the entire
unramified local norm obstruction is confined to the principal-unit group; residue units create
no obstruction. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_unit_eq_integralNorm_mul_principalUnit
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g) (a : (ValuativeRel.valuation K).integerˣ) :
    ∃ b : (AdjoinRoot f)ˣ, ∃ p : (ValuativeRel.valuation K).integerˣ,
      nonarchimedeanLocalFieldReductionUnits K p = 1 ∧
      a =
        (nonarchimedeanLocalFieldAdjoinRootIntegralNormUnits K f hf g hgmonic hfg hg
          (Additive.ofMul b)).toMul * p := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  obtain ⟨b, hb⟩ :=
    nonarchimedeanLocalFieldAdjoinRootIntegralNormReductionUnits_surjective
      K f hf g hgmonic hfg hg (nonarchimedeanLocalFieldReductionUnits K a)
  let n : (ValuativeRel.valuation K).integerˣ :=
    (nonarchimedeanLocalFieldAdjoinRootIntegralNormUnits K f hf g hgmonic hfg hg
      (Additive.ofMul b)).toMul
  let p : (ValuativeRel.valuation K).integerˣ := n⁻¹ * a
  have hn : nonarchimedeanLocalFieldReductionUnits K n =
      nonarchimedeanLocalFieldReductionUnits K a := by
    change nonarchimedeanLocalFieldReductionUnits K
      (Units.map (Algebra.intNorm (ValuativeRel.valuation K).integer (AdjoinRoot f)) b) =
        nonarchimedeanLocalFieldReductionUnits K a
    exact hb
  refine ⟨b, p, ?_, ?_⟩
  · change nonarchimedeanLocalFieldReductionUnits K (n⁻¹ * a) = 1
    rw [map_mul, map_inv, hn, inv_mul_cancel]
  · change a = n * (n⁻¹ * a)
    group

/-- The principal-unit norm condition is sufficient for full unramified unit-norm surjectivity.
The residue-unit quotient condition is already discharged by
`nonarchimedeanLocalFieldAdjoinRootIntegralNormReductionUnits_surjective`; this theorem isolates
the sole remaining local-class-field-theory input. -/
theorem nonarchimedeanLocalFieldAdjoinRootIntegralNormUnits_surjective_of_principalKernel
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (f : Polynomial (ValuativeRel.valuation K).integer) (hf : f.Monic)
    (g : Polynomial (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer))
    (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (ValuativeRel.valuation K).integer)) = g)
    (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
    letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
    letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
      AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    (∀ a : (ValuativeRel.valuation K).integerˣ,
      nonarchimedeanLocalFieldReductionUnits K a = 1 →
      ∃ b : (AdjoinRoot f)ˣ,
        nonarchimedeanLocalFieldAdjoinRootReductionUnits K f g hfg b = 1 ∧
          Units.map (Algebra.intNorm (ValuativeRel.valuation K).integer (AdjoinRoot f)) b = a) →
    Function.Surjective
      (Units.map (Algebra.intNorm (ValuativeRel.valuation K).integer (AdjoinRoot f))) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap (ValuativeRel.valuation K).integer (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Module.Free (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite (ValuativeRel.valuation K).integer (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree (ValuativeRel.valuation K).integer (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  intro hprincipal
  letI : Fact (Irreducible g) := ⟨hg⟩
  letI : Field (AdjoinRoot g) := AdjoinRoot.instField
  letI : Algebra (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
      (AdjoinRoot g) := AdjoinRoot.instAlgebra g
  letI : Module.Finite (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
      (AdjoinRoot g) := hgmonic.finite_adjoinRoot
  letI : Finite (AdjoinRoot g) := Module.finite_of_finite
    (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
  apply monoidHom_surjective_of_surjective_mod_kernel
    (AdjoinRoot f)ˣ (ValuativeRel.valuation K).integerˣ (AdjoinRoot g)ˣ
    (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)ˣ
    (Units.map (Algebra.intNorm (ValuativeRel.valuation K).integer (AdjoinRoot f)))
    (nonarchimedeanLocalFieldAdjoinRootReductionUnits K f g hfg)
    (nonarchimedeanLocalFieldReductionUnits K)
    (Units.map (Algebra.norm
      (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)))
  · ext u
    change algebraMap (ValuativeRel.valuation K).integer
      (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
        (Algebra.intNorm (ValuativeRel.valuation K).integer (AdjoinRoot f)
          (u : AdjoinRoot f)) =
      Algebra.norm (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)
        (nonarchimedeanLocalFieldAdjoinRootReductionMap K f g hfg (u : AdjoinRoot f))
    exact (nonarchimedeanLocalFieldAdjoinRoot_integralNorm_reductionMap
      K f hf g hgmonic hfg hg (u : AdjoinRoot f)).symm
  · exact nonarchimedeanLocalFieldAdjoinRootReductionUnits_surjective K f hf g hfg hg
  · exact FiniteField.unitsMap_norm_surjective
      (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) (AdjoinRoot g)
  · exact hprincipal

end GaloisForLFunctions.HTGeometry.ABHN
