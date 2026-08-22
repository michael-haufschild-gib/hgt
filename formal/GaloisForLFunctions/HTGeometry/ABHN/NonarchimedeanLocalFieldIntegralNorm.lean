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

end GaloisForLFunctions.HTGeometry.ABHN
