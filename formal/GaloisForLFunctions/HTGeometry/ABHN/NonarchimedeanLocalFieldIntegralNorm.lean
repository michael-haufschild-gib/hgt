/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldValuationSequence
import GaloisForLFunctions.HTGeometry.ABHN.IntegralNormUnits

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
