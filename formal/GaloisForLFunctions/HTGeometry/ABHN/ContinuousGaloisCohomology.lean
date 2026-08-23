/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Rep.Basic
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2NormQuotient
import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldCohomology

/-!
# Continuous Galois cohomology input for local class field theory

This module equips the units of an arbitrary Galois extension with their discrete topology and
packages the natural Galois action as a continuous representation.  For algebraic extensions, the
stabilizer of every unit is open in the Krull topology.  Thus the degree-two continuous cohomology
object used by local class field theory is available in the corpus without assuming a reciprocity
map or a Brauer comparison.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

attribute [local instance] IsCyclic.commGroup

/-- The unit group of a field, viewed additively and with the discrete topology used in continuous
Galois cohomology. -/
def DiscreteGaloisUnits (L : Type*) [Field L] := Additive Lˣ

instance (L : Type*) [Field L] : AddCommGroup (DiscreteGaloisUnits L) :=
  inferInstanceAs (AddCommGroup (Additive Lˣ))

instance (L : Type*) [Field L] : Module ℤ (DiscreteGaloisUnits L) :=
  inferInstanceAs (Module ℤ (Additive Lˣ))

instance (L : Type*) [Field L] : TopologicalSpace (DiscreteGaloisUnits L) := ⊥

instance (L : Type*) [Field L] : DiscreteTopology (DiscreteGaloisUnits L) := ⟨rfl⟩

instance (L : Type*) [Field L] : IsTopologicalAddGroup (DiscreteGaloisUnits L) := inferInstance

/-- The natural Galois action on discretely topologized units, as a continuous representation.
Continuity of each endomorphism is automatic from the discrete source topology. -/
noncomputable def continuousGaloisUnitsRepresentation
    (K L : Type*) [Field K] [Field L] [Algebra K L] :
    ContRepresentation ℤ (Gal(L/K)) (DiscreteGaloisUnits L) :=
  ContRepresentation.ofMonoidHom
    { toFun := fun g =>
        ContinuousLinearMap.mk ((Rep.ofAlgebraAutOnUnits K L).ρ g)
          continuous_of_discreteTopology
      map_one' := by ext; rfl
      map_mul' := by intro g h; ext; rfl }

/-- Forgetting topology from the continuous unit representation recovers the usual unit Galois
representation. -/
theorem continuousGaloisUnitsRepresentation_toRepresentation_eq
    (K L : Type*) [Field K] [Field L] [Algebra K L] :
    (continuousGaloisUnitsRepresentation K L).toRepresentation =
      (Rep.ofAlgebraAutOnUnits K L).ρ := rfl

/-- Continuous cohomology of the discrete unit Galois module. -/
noncomputable abbrev continuousGaloisUnitCohomology (n : ℕ)
    (K L : Type*) [Field K] [Field L] [Algebra K L] : TopModuleCat ℤ :=
  continuousCohomology n (TopRep.of (continuousGaloisUnitsRepresentation K L))

/-- Degree-two continuous Galois cohomology of the discrete unit module.  This is the cohomological
term that a future local Brauer comparison must identify with the Brauer group. -/
noncomputable abbrev continuousGaloisH2
    (K L : Type*) [Field K] [Field L] [Algebra K L] : TopModuleCat ℤ :=
  continuousGaloisUnitCohomology 2 K L

/-- Degree-two continuous cohomology of the absolute Galois group acting on separable-closure
units.  This is the cohomological source in the local Brauer comparison. -/
noncomputable abbrev absoluteGaloisH2 (K : Type*) [Field K] : TopModuleCat ℤ :=
  continuousGaloisH2 K (SeparableClosure K)

/-- For an algebraic extension, every unit has an open stabilizer in the Krull-topological Galois
group.  This is the smoothness condition for the discrete unit Galois module. -/
theorem isOpen_continuousGaloisUnits_stabilizer {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsIntegral K L] (x : DiscreteGaloisUnits L) :
    IsOpen {g : Gal(L/K) | continuousGaloisUnitsRepresentation K L g x = x} := by
  let y : L := ((Additive.toMul x : Lˣ) : L)
  have hy := stabilizer_isOpen_of_isIntegral (K := K) (L := L) y
  change IsOpen {g : Gal(L/K) | g • (Additive.toMul x) = Additive.toMul x}
  rw [show {g : Gal(L/K) | g • (Additive.toMul x) = Additive.toMul x} =
    MulAction.stabilizer Gal(L/K) y by
      ext g
      change g • (Additive.toMul x) = Additive.toMul x ↔ g y = y
      exact Units.ext_iff]
  exact hy

/-- In particular, the discrete unit module is smooth for every Galois extension. -/
theorem isOpen_continuousGaloisUnits_stabilizer_of_isGalois
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (x : DiscreteGaloisUnits L) :
    IsOpen {g : Gal(L/K) | continuousGaloisUnitsRepresentation K L g x = x} :=
  isOpen_continuousGaloisUnits_stabilizer x

/-- Every element of the discrete unit module has open stabilizer under the absolute Galois group.
This supplies the standard smooth-module condition at the precise cohomological source of local
class field theory. -/
theorem isOpen_absoluteGaloisUnits_stabilizer (K : Type*) [Field K]
    (x : DiscreteGaloisUnits (SeparableClosure K)) :
    IsOpen {g : Gal(SeparableClosure K/K) |
      continuousGaloisUnitsRepresentation K (SeparableClosure K) g x = x} :=
  isOpen_continuousGaloisUnits_stabilizer_of_isGalois x

/-- The units fixed by an arbitrary finite or infinite Galois group are exactly the units from the
base field.  This is the usual degree-zero Galois-cohomology calculation on units. -/
theorem galoisUnits_fixed_iff_range {K L : Type*} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (u : Lˣ) :
    (∀ g : Gal(L/K), g u = u) ↔ ∃ v : Kˣ, Units.map (algebraMap K L) v = u := by
  constructor
  · intro hu
    obtain ⟨x, hx⟩ :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (K := L) (u : L)).mpr hu
    have hxne : x ≠ 0 := by
      intro hxzero
      apply u.ne_zero
      calc
        (u : L) = algebraMap K L x := hx.symm
        _ = 0 := by rw [hxzero, map_zero]
    refine ⟨Units.mk0 x hxne, ?_⟩
    apply Units.ext
    exact hx
  · rintro ⟨v, rfl⟩ g
    change g (algebraMap K L (v : K)) = algebraMap K L (v : K)
    exact g.commutes _

/-- The invariant submodule of the continuous discrete-unit representation consists precisely of
base-field units.  Together with `ContinuousCohomology.zeroIso`, this gives the expected
degree-zero continuous Galois cohomology calculation. -/
theorem continuousGaloisUnitsRepresentation_mem_invariants_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (x : DiscreteGaloisUnits L) :
    x ∈ (TopRep.of (continuousGaloisUnitsRepresentation K L)).ρ.invariants ↔
      ∃ v : Kˣ, Units.map (algebraMap K L) v = (Additive.toMul x : Lˣ) := by
  rw [ContRepresentation.mem_invariants]
  constructor
  · intro hx
    apply (galoisUnits_fixed_iff_range (Additive.toMul x : Lˣ)).mp
    intro g
    have h := hx g
    change Additive.ofMul (Units.map g.toMonoidHom (Additive.toMul x : Lˣ)) = x at h
    have hu := congrArg Additive.toMul h
    change Units.map g.toMonoidHom (Additive.toMul x : Lˣ) = Additive.toMul x at hu
    exact congrArg Units.val hu
  · intro hx g
    apply Additive.toMul.injective
    change Units.map g.toMonoidHom (Additive.toMul x : Lˣ) = Additive.toMul x
    apply Units.ext
    exact ((galoisUnits_fixed_iff_range (Additive.toMul x : Lˣ)).mpr hx) g

/-- The base-field units, embedded into the extension, as an additive map onto the invariant
submodule of the discrete unit Galois representation. -/
noncomputable def galoisUnitsInvariantAddHom
    (K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    Additive Kˣ →+ (TopRep.of (continuousGaloisUnitsRepresentation K L)).ρ.invariants where
  toFun := fun v => ⟨Additive.ofMul (Units.map (algebraMap K L) (Additive.toMul v)), by
    rw [ContRepresentation.mem_invariants]
    intro g
    apply Additive.toMul.injective
    change Units.map g.toMonoidHom (Units.map (algebraMap K L) (Additive.toMul v)) =
      Units.map (algebraMap K L) (Additive.toMul v)
    apply Units.ext
    exact g.commutes _⟩
  map_zero' := by
    apply Subtype.ext
    apply Additive.toMul.injective
    change Units.map (algebraMap K L).toMonoidHom (1 : Kˣ) = 1
    exact map_one _
  map_add' := by
    intro x y
    apply Subtype.ext
    apply Additive.toMul.injective
    change Units.map (algebraMap K L).toMonoidHom ((Additive.toMul x) * (Additive.toMul y)) =
      Units.map (algebraMap K L).toMonoidHom (Additive.toMul x) *
        Units.map (algebraMap K L).toMonoidHom (Additive.toMul y)
    exact map_mul _ _ _

/-- The base-field-unit map into continuous Galois invariants is injective. -/
theorem galoisUnitsInvariantAddHom_injective
    (K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    Function.Injective (galoisUnitsInvariantAddHom K L) := by
  intro x y hxy
  apply Additive.toMul.injective
  have hval := congrArg Subtype.val hxy
  have hu := congrArg Additive.toMul hval
  change Units.map (algebraMap K L).toMonoidHom (Additive.toMul x) =
    Units.map (algebraMap K L).toMonoidHom (Additive.toMul y) at hu
  apply Units.ext
  apply FaithfulSMul.algebraMap_injective K L
  exact congrArg Units.val hu

/-- Every invariant of the continuous discrete-unit representation comes from a base-field unit. -/
theorem galoisUnitsInvariantAddHom_surjective
    (K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    Function.Surjective (galoisUnitsInvariantAddHom K L) := by
  intro x
  obtain ⟨v, hv⟩ :=
    (continuousGaloisUnitsRepresentation_mem_invariants_iff (K := K) (L := L) x).mp x.property
  refine ⟨Additive.ofMul v, ?_⟩
  apply Subtype.ext
  apply Additive.toMul.injective
  change Units.map (algebraMap K L).toMonoidHom v =
    Additive.toMul (x : DiscreteGaloisUnits L)
  exact hv

/-- The Galois-invariant discrete units of `L` are additively equivalent to the base-field units.
The forward map is scalar extension of units, and its inverse is Galois descent. -/
noncomputable def galoisUnitsInvariantAddEquiv
    (K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    Additive Kˣ ≃+ (TopRep.of (continuousGaloisUnitsRepresentation K L)).ρ.invariants :=
  AddEquiv.ofBijective (galoisUnitsInvariantAddHom K L)
    ⟨galoisUnitsInvariantAddHom_injective K L,
      galoisUnitsInvariantAddHom_surjective K L⟩

/-- **Continuous Galois `H⁰` on units.** The degree-zero continuous cohomology of the discrete
unit Galois module is the additive unit group of the base field. -/
noncomputable def continuousGaloisH0UnitsAddEquiv
    (K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    continuousGaloisUnitCohomology 0 K L ≃+ Additive Kˣ :=
  ((ContinuousCohomology.zeroIso
      (TopRep.of (continuousGaloisUnitsRepresentation K L))).toContinuousLinearEquiv.toLinearEquiv
    |>.toAddEquiv).trans (galoisUnitsInvariantAddEquiv K L).symm

/-- For small-universe Galois extensions, continuous and ordinary Galois cohomology agree in
degree zero on units.  This compares the new continuous local-class-field-theory input with the
ordinary finite-cyclic cohomology already used by cyclic algebras.  The analogous comparison in
degree two remains the substantive missing bridge. -/
noncomputable def continuousGaloisH0UnitsToGroupGaloisH0AddEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L] :
    continuousGaloisUnitCohomology 0 K L ≃+
      groupCohomology (Rep.ofAlgebraAutOnUnits K L) 0 :=
  ((ContinuousCohomology.zeroIso
      (TopRep.of (continuousGaloisUnitsRepresentation K L))).toContinuousLinearEquiv.toLinearEquiv
    |>.toAddEquiv).trans
    (((groupCohomology.H0Iso (Rep.ofAlgebraAutOnUnits K L)).toLinearEquiv.toAddEquiv).symm)

/-- For a finite field extension, Krull's topology on the Galois group is discrete.  Therefore
continuous maps out of the Galois group are exactly unrestricted functions.  Iterating this
equivalence is the cochain-level input still needed to compare finite continuous and ordinary
Galois cohomology in degree two. -/
noncomputable def continuousMapFromFiniteGaloisEquiv
    (K L X : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [TopologicalSpace X] :
    C(Gal(L/K), X) ≃ (Gal(L/K) → X) where
  toFun := fun f => f
  invFun := fun f => ⟨f, continuous_of_discreteTopology⟩
  left_inv := by intro f; ext g; rfl
  right_inv := by intro f; rfl

/-- Evaluation is unchanged by forgetting continuity from finite Galois cochains. -/
theorem continuousMapFromFiniteGaloisEquiv_apply
    (K L X : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [TopologicalSpace X] (f : C(Gal(L/K), X)) (g : Gal(L/K)) :
    continuousMapFromFiniteGaloisEquiv K L X f g = f g := rfl

/-- The two nested continuous-map spaces occurring in low-degree cochains over a finite Galois
group are the ordinary spaces of functions of two Galois variables. -/
noncomputable def continuousMapFromFiniteGaloisTwoEquiv
    (K L X : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [TopologicalSpace X] :
    C(Gal(L/K), C(Gal(L/K), X)) ≃ (Gal(L/K) → Gal(L/K) → X) where
  toFun := fun f g h => f g h
  invFun := fun f => ⟨fun g => ⟨fun h => f g h, continuous_of_discreteTopology⟩,
    continuous_of_discreteTopology⟩
  left_inv := by intro f; ext g h; rfl
  right_inv := by intro f; rfl

/-- The three nested continuous-map spaces needed to describe the degree-two differential over a
finite Galois group are the ordinary ternary function space. -/
noncomputable def continuousMapFromFiniteGaloisThreeEquiv
    (K L X : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [TopologicalSpace X] :
    C(Gal(L/K), C(Gal(L/K), C(Gal(L/K), X))) ≃
      (Gal(L/K) → Gal(L/K) → Gal(L/K) → X) where
  toFun := fun f g h i => f g h i
  invFun := fun f => ⟨fun g => ⟨fun h => ⟨fun i => f g h i,
    continuous_of_discreteTopology⟩, continuous_of_discreteTopology⟩,
    continuous_of_discreteTopology⟩
  left_inv := by intro f; ext g h i; rfl
  right_inv := by intro f; rfl

/-- Turn an ordinary one-cochain into an invariant homogeneous continuous one-cochain.  The
formula is the standard homogenization `f ↦ ((g,h) ↦ g • f(g⁻¹h))`. -/
noncomputable def finiteGaloisDegreeOneInhomogeneousToHomogeneous
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (f : Gal(L/K) → DiscreteGaloisUnits L) :
    (TopRep.homogeneousCochains (TopRep.of (continuousGaloisUnitsRepresentation K L))).X 1 :=
  ⟨⟨fun g => ⟨fun h => continuousGaloisUnitsRepresentation K L g
      (f (g⁻¹ * h)), continuous_of_discreteTopology⟩,
    continuous_of_discreteTopology⟩, by
      rw [ContRepresentation.mem_invariants]
      intro a
      ext b c
      simp only [TopRep.resolutionX, TopRep.resolution'X,
        ContRepresentation.coind₁_apply_apply]
      change (continuousGaloisUnitsRepresentation K L a)
        ((continuousGaloisUnitsRepresentation K L (a⁻¹ * b))
          (f ((a⁻¹ * b)⁻¹ * (a⁻¹ * c)))) =
        (continuousGaloisUnitsRepresentation K L b) (f (b⁻¹ * c))
      rw [← mul_apply_eq_comp, ← map_mul]
      congr 1
      group⟩

/-- Evaluate a homogeneous degree-one cochain with first coordinate one to recover its ordinary
inhomogeneous cochain. -/
noncomputable def finiteGaloisDegreeOneHomogeneousToInhomogeneous
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    (TopRep.homogeneousCochains (TopRep.of (continuousGaloisUnitsRepresentation K L))).X 1 →
      (Gal(L/K) → DiscreteGaloisUnits L) := fun F h => F.1 1 h

theorem finiteGaloisDegreeOneHomogeneousToInhomogeneous_comp_inhomogeneousToHomogeneous
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (f : Gal(L/K) → DiscreteGaloisUnits L) :
    finiteGaloisDegreeOneHomogeneousToInhomogeneous K L
      (finiteGaloisDegreeOneInhomogeneousToHomogeneous K L f) = f := by
  funext h
  simp [finiteGaloisDegreeOneHomogeneousToInhomogeneous,
    finiteGaloisDegreeOneInhomogeneousToHomogeneous]

theorem finiteGaloisDegreeOneInhomogeneousToHomogeneous_comp_homogeneousToInhomogeneous
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (F : (TopRep.homogeneousCochains
      (TopRep.of (continuousGaloisUnitsRepresentation K L))).X 1) :
    finiteGaloisDegreeOneInhomogeneousToHomogeneous K L
      (finiteGaloisDegreeOneHomogeneousToInhomogeneous K L F) = F := by
  apply Subtype.ext
  ext g h
  change (continuousGaloisUnitsRepresentation K L g)
      (F.1 1 (g⁻¹ * h)) = F.1 g h
  have hF := DFunLike.ext_iff.1 (DFunLike.ext_iff.1 (F.property g) g) h
  change (continuousGaloisUnitsRepresentation K L g)
      (F.1 (g⁻¹ * g) (g⁻¹ * h)) = F.1 g h at hF
  simpa using hF

/-- The degree-one homogeneous continuous cochains of a finite Galois group are canonically the
ordinary inhomogeneous one-cochains. -/
noncomputable def finiteGaloisDegreeOneHomogeneousCochainAddEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    (TopRep.homogeneousCochains (TopRep.of (continuousGaloisUnitsRepresentation K L))).X 1 ≃+
      (Gal(L/K) → DiscreteGaloisUnits L) :=
  AddEquiv.ofBijective (show
    (TopRep.homogeneousCochains (TopRep.of (continuousGaloisUnitsRepresentation K L))).X 1 →+
      (Gal(L/K) → DiscreteGaloisUnits L) from
    { toFun := finiteGaloisDegreeOneHomogeneousToInhomogeneous K L
      map_zero' := by ext; rfl
      map_add' := by intro x y; ext; rfl })
    ⟨by
      intro x y hxy
      rw [← finiteGaloisDegreeOneInhomogeneousToHomogeneous_comp_homogeneousToInhomogeneous K L x,
        ← finiteGaloisDegreeOneInhomogeneousToHomogeneous_comp_homogeneousToInhomogeneous K L y]
      exact congrArg (finiteGaloisDegreeOneInhomogeneousToHomogeneous K L) hxy,
      by
        intro f
        refine ⟨finiteGaloisDegreeOneInhomogeneousToHomogeneous K L f, ?_⟩
        exact finiteGaloisDegreeOneHomogeneousToInhomogeneous_comp_inhomogeneousToHomogeneous
          K L _⟩

/-- Turn an ordinary degree-two cochain into an invariant homogeneous continuous cochain. -/
noncomputable def finiteGaloisDegreeTwoInhomogeneousToHomogeneous
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (f : Gal(L/K) → Gal(L/K) → DiscreteGaloisUnits L) :
    (TopRep.homogeneousCochains (TopRep.of (continuousGaloisUnitsRepresentation K L))).X 2 :=
  ⟨⟨fun g => ⟨fun h => ⟨fun i => continuousGaloisUnitsRepresentation K L g
      (f (g⁻¹ * h) (h⁻¹ * i)), continuous_of_discreteTopology⟩,
    continuous_of_discreteTopology⟩, continuous_of_discreteTopology⟩, by
      rw [ContRepresentation.mem_invariants]
      intro a
      ext b c d
      simp only [TopRep.resolutionX, TopRep.resolution'X,
        ContRepresentation.coind₁_apply_apply]
      change (continuousGaloisUnitsRepresentation K L a)
        ((continuousGaloisUnitsRepresentation K L (a⁻¹ * b))
          (f ((a⁻¹ * b)⁻¹ * (a⁻¹ * c)) ((a⁻¹ * c)⁻¹ * (a⁻¹ * d)))) =
        (continuousGaloisUnitsRepresentation K L b) (f (b⁻¹ * c) (c⁻¹ * d))
      rw [← mul_apply_eq_comp, ← map_mul]
      congr 1 <;> group⟩

/-- Evaluate a homogeneous degree-two cochain with first coordinate one. -/
noncomputable def finiteGaloisDegreeTwoHomogeneousToInhomogeneous
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    (TopRep.homogeneousCochains (TopRep.of (continuousGaloisUnitsRepresentation K L))).X 2 →
      (Gal(L/K) → Gal(L/K) → DiscreteGaloisUnits L) := fun F h i => F.1 1 h (h * i)

theorem finiteGaloisDegreeTwoHomogeneousToInhomogeneous_comp_inhomogeneousToHomogeneous
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (f : Gal(L/K) → Gal(L/K) → DiscreteGaloisUnits L) :
    finiteGaloisDegreeTwoHomogeneousToInhomogeneous K L
      (finiteGaloisDegreeTwoInhomogeneousToHomogeneous K L f) = f := by
  funext h i
  simp [finiteGaloisDegreeTwoHomogeneousToInhomogeneous,
    finiteGaloisDegreeTwoInhomogeneousToHomogeneous]

theorem finiteGaloisDegreeTwoInhomogeneousToHomogeneous_comp_homogeneousToInhomogeneous
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (F : (TopRep.homogeneousCochains
      (TopRep.of (continuousGaloisUnitsRepresentation K L))).X 2) :
    finiteGaloisDegreeTwoInhomogeneousToHomogeneous K L
      (finiteGaloisDegreeTwoHomogeneousToInhomogeneous K L F) = F := by
  apply Subtype.ext
  ext g h i
  change (continuousGaloisUnitsRepresentation K L g)
      (F.1 1 (g⁻¹ * h) ((g⁻¹ * h) * (h⁻¹ * i))) = F.1 g h i
  have hF := DFunLike.ext_iff.1
    (DFunLike.ext_iff.1 (DFunLike.ext_iff.1 (F.property g) g) h) i
  change (continuousGaloisUnitsRepresentation K L g)
      (F.1 (g⁻¹ * g) (g⁻¹ * h) (g⁻¹ * i)) = F.1 g h i at hF
  convert hF using 1; group

/-- The degree-two homogeneous continuous cochains of a finite Galois group are canonically the
ordinary inhomogeneous two-cochains. -/
noncomputable def finiteGaloisDegreeTwoHomogeneousCochainAddEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    (TopRep.homogeneousCochains (TopRep.of (continuousGaloisUnitsRepresentation K L))).X 2 ≃+
      (Gal(L/K) → Gal(L/K) → DiscreteGaloisUnits L) :=
  AddEquiv.ofBijective (show
    (TopRep.homogeneousCochains (TopRep.of (continuousGaloisUnitsRepresentation K L))).X 2 →+
      (Gal(L/K) → Gal(L/K) → DiscreteGaloisUnits L) from
    { toFun := finiteGaloisDegreeTwoHomogeneousToInhomogeneous K L
      map_zero' := by ext; rfl
      map_add' := by intro x y; ext; rfl })
    ⟨by
      intro x y hxy
      rw [← finiteGaloisDegreeTwoInhomogeneousToHomogeneous_comp_homogeneousToInhomogeneous K L x,
        ← finiteGaloisDegreeTwoInhomogeneousToHomogeneous_comp_homogeneousToInhomogeneous K L y]
      exact congrArg (finiteGaloisDegreeTwoInhomogeneousToHomogeneous K L) hxy,
      by
        intro f
        refine ⟨finiteGaloisDegreeTwoInhomogeneousToHomogeneous K L f, ?_⟩
        exact finiteGaloisDegreeTwoHomogeneousToInhomogeneous_comp_inhomogeneousToHomogeneous
          K L _⟩

/-- Turn an ordinary degree-three cochain into an invariant homogeneous continuous cochain. -/
noncomputable def finiteGaloisDegreeThreeInhomogeneousToHomogeneous
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (f : Gal(L/K) → Gal(L/K) → Gal(L/K) → DiscreteGaloisUnits L) :
    (TopRep.homogeneousCochains (TopRep.of (continuousGaloisUnitsRepresentation K L))).X 3 :=
  ⟨⟨fun g => ⟨fun h => ⟨fun i => ⟨fun j => continuousGaloisUnitsRepresentation K L g
      (f (g⁻¹ * h) (h⁻¹ * i) (i⁻¹ * j)), continuous_of_discreteTopology⟩,
    continuous_of_discreteTopology⟩, continuous_of_discreteTopology⟩,
    continuous_of_discreteTopology⟩, by
      rw [ContRepresentation.mem_invariants]
      intro a
      ext b c d e
      simp only [TopRep.resolutionX, TopRep.resolution'X,
        ContRepresentation.coind₁_apply_apply]
      change (continuousGaloisUnitsRepresentation K L a)
        ((continuousGaloisUnitsRepresentation K L (a⁻¹ * b))
          (f ((a⁻¹ * b)⁻¹ * (a⁻¹ * c)) ((a⁻¹ * c)⁻¹ * (a⁻¹ * d))
            ((a⁻¹ * d)⁻¹ * (a⁻¹ * e)))) =
        (continuousGaloisUnitsRepresentation K L b) (f (b⁻¹ * c) (c⁻¹ * d) (d⁻¹ * e))
      rw [← mul_apply_eq_comp, ← map_mul]
      congr 1 <;> group⟩

/-- Evaluate a homogeneous degree-three cochain with first coordinate one. -/
noncomputable def finiteGaloisDegreeThreeHomogeneousToInhomogeneous
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    (TopRep.homogeneousCochains (TopRep.of (continuousGaloisUnitsRepresentation K L))).X 3 →
      (Gal(L/K) → Gal(L/K) → Gal(L/K) → DiscreteGaloisUnits L) :=
  fun F h i j => F.1 1 h (h * i) (h * i * j)

theorem finiteGaloisDegreeThreeHomogeneousToInhomogeneous_comp_inhomogeneousToHomogeneous
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (f : Gal(L/K) → Gal(L/K) → Gal(L/K) → DiscreteGaloisUnits L) :
    finiteGaloisDegreeThreeHomogeneousToInhomogeneous K L
      (finiteGaloisDegreeThreeInhomogeneousToHomogeneous K L f) = f := by
  funext h i j
  change (continuousGaloisUnitsRepresentation K L 1)
    (f (1⁻¹ * h) (h⁻¹ * (h * i)) ((h * i)⁻¹ * (h * i * j))) = f h i j
  simp only [map_one, one_apply_eq_self, inv_one, one_mul]
  congr 1 <;> group

theorem finiteGaloisDegreeThreeInhomogeneousToHomogeneous_comp_homogeneousToInhomogeneous
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (F : (TopRep.homogeneousCochains
      (TopRep.of (continuousGaloisUnitsRepresentation K L))).X 3) :
    finiteGaloisDegreeThreeInhomogeneousToHomogeneous K L
      (finiteGaloisDegreeThreeHomogeneousToInhomogeneous K L F) = F := by
  apply Subtype.ext
  ext g h i j
  change (continuousGaloisUnitsRepresentation K L g)
      (F.1 1 (g⁻¹ * h) ((g⁻¹ * h) * (h⁻¹ * i))
        ((g⁻¹ * h) * (h⁻¹ * i) * (i⁻¹ * j))) = F.1 g h i j
  have hF := DFunLike.ext_iff.1
    (DFunLike.ext_iff.1 (DFunLike.ext_iff.1 (DFunLike.ext_iff.1 (F.property g) g) h) i) j
  change (continuousGaloisUnitsRepresentation K L g)
      (F.1 (g⁻¹ * g) (g⁻¹ * h) (g⁻¹ * i) (g⁻¹ * j)) = F.1 g h i j at hF
  convert hF using 1; group

/-- The degree-three homogeneous continuous cochains of a finite Galois group are canonically
the ordinary inhomogeneous three-cochains. -/
noncomputable def finiteGaloisDegreeThreeHomogeneousCochainAddEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    (TopRep.homogeneousCochains (TopRep.of (continuousGaloisUnitsRepresentation K L))).X 3 ≃+
      (Gal(L/K) → Gal(L/K) → Gal(L/K) → DiscreteGaloisUnits L) :=
  AddEquiv.ofBijective (show
    (TopRep.homogeneousCochains (TopRep.of (continuousGaloisUnitsRepresentation K L))).X 3 →+
      (Gal(L/K) → Gal(L/K) → Gal(L/K) → DiscreteGaloisUnits L) from
    { toFun := finiteGaloisDegreeThreeHomogeneousToInhomogeneous K L
      map_zero' := by ext; rfl
      map_add' := by intro x y; ext; rfl })
    ⟨by
      intro x y hxy
      rw [← finiteGaloisDegreeThreeInhomogeneousToHomogeneous_comp_homogeneousToInhomogeneous K L x,
        ← finiteGaloisDegreeThreeInhomogeneousToHomogeneous_comp_homogeneousToInhomogeneous K L y]
      exact congrArg (finiteGaloisDegreeThreeInhomogeneousToHomogeneous K L) hxy,
      by
        intro f
        refine ⟨finiteGaloisDegreeThreeInhomogeneousToHomogeneous K L f, ?_⟩
        exact finiteGaloisDegreeThreeHomogeneousToInhomogeneous_comp_inhomogeneousToHomogeneous
          K L _⟩

/-- Under normalized degree-one and degree-two cochain coordinates, the continuous homogeneous
differential is the ordinary inhomogeneous Galois differential `d₁₂`. -/
theorem finiteGaloisDegreeOneDifferentialCompatibility
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (F : (TopRep.homogeneousCochains
      (TopRep.of (continuousGaloisUnitsRepresentation K L))).X 1) :
    finiteGaloisDegreeTwoHomogeneousToInhomogeneous K L
      ((TopRep.homogeneousCochains
        (TopRep.of (continuousGaloisUnitsRepresentation K L))).d 1 2 F) =
      fun g h => (continuousGaloisUnitsRepresentation K L g)
          (finiteGaloisDegreeOneHomogeneousToInhomogeneous K L F h) -
        finiteGaloisDegreeOneHomogeneousToInhomogeneous K L F (g * h) +
          finiteGaloisDegreeOneHomogeneousToInhomogeneous K L F g := by
  funext g h
  change (((TopRep.homogeneousCochains
    (TopRep.of (continuousGaloisUnitsRepresentation K L))).d 1 2 F).1 1 g (g * h)) =
    (continuousGaloisUnitsRepresentation K L g) (F.1 1 h) - F.1 1 (g * h) + F.1 1 g
  rw [TopRep.homogeneousCochains.d_apply]
  change F.1 g (g * h) - (F.1 1 (g * h) - F.1 1 g) =
    (continuousGaloisUnitsRepresentation K L g) (F.1 1 h) - F.1 1 (g * h) + F.1 1 g
  have hF := DFunLike.ext_iff.1 (DFunLike.ext_iff.1 (F.property g) g) (g * h)
  change (continuousGaloisUnitsRepresentation K L g)
    (F.1 (g⁻¹ * g) (g⁻¹ * (g * h))) = F.1 g (g * h) at hF
  have hF' : (continuousGaloisUnitsRepresentation K L g) (F.1 1 h) = F.1 g (g * h) := by
    simpa using hF
  rw [← hF']
  abel

/-- Under normalized degree-two and degree-three cochain coordinates, the continuous homogeneous
differential is the ordinary inhomogeneous Galois differential `d₂₃`. -/
theorem finiteGaloisDegreeTwoDifferentialCompatibility
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (F : (TopRep.homogeneousCochains
      (TopRep.of (continuousGaloisUnitsRepresentation K L))).X 2) :
    finiteGaloisDegreeThreeHomogeneousToInhomogeneous K L
      ((TopRep.homogeneousCochains
        (TopRep.of (continuousGaloisUnitsRepresentation K L))).d 2 3 F) =
      fun g h i => (continuousGaloisUnitsRepresentation K L g)
          (finiteGaloisDegreeTwoHomogeneousToInhomogeneous K L F h i) -
        finiteGaloisDegreeTwoHomogeneousToInhomogeneous K L F (g * h) i +
          finiteGaloisDegreeTwoHomogeneousToInhomogeneous K L F g (h * i) -
            finiteGaloisDegreeTwoHomogeneousToInhomogeneous K L F g h := by
  funext g h i
  change (((TopRep.homogeneousCochains
    (TopRep.of (continuousGaloisUnitsRepresentation K L))).d 2 3 F).1 1 g (g * h) (g * h * i)) =
    (continuousGaloisUnitsRepresentation K L g) (F.1 1 h (h * i)) -
      F.1 1 (g * h) ((g * h) * i) + F.1 1 g (g * (h * i)) - F.1 1 g (g * h)
  rw [TopRep.homogeneousCochains.d_apply]
  simp only [TopRep.d_succ, TopRep.d_zero, TopRep.hom_sub, TopRep.hom_ofHom,
    ContIntertwiningMap.sub_apply, ContRepresentation.coind₁ι_toFun,
    ContRepresentation.coind₁Map_toFun, ContinuousMap.sub_apply,
    ContinuousMap.const_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  have hF := DFunLike.ext_iff.1
    (DFunLike.ext_iff.1 (DFunLike.ext_iff.1 (F.property g) g) (g * h)) (g * h * i)
  have hF' : (continuousGaloisUnitsRepresentation K L g) (F.1 1 h (h * i)) =
      F.1 g (g * h) (g * h * i) := by
    simp only [ContRepresentation.coind₁_apply_apply] at hF
    convert hF using 1; group
  have h_assoc : g * (h * i) = g * h * i := by group
  rw [h_assoc, ← hF']
  abel

/-- The first component of the finite continuous cochain complex, after forgetting topology,
is the ordinary one-cochain module. -/
noncomputable def finiteGaloisDegreeOneCochainModuleIso
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    (((TopRep.homogeneousCochains
      (TopRep.of (continuousGaloisUnitsRepresentation K L))).sc' 1 2 3).map
        (CategoryTheory.forget₂ (TopModuleCat ℤ) (ModuleCat ℤ))).X₁ ≅
      ModuleCat.of ℤ (Gal(L/K) → DiscreteGaloisUnits L) :=
  (finiteGaloisDegreeOneHomogeneousCochainAddEquiv K L).toIntLinearEquiv.toModuleIso

/-- The second component of the finite continuous cochain complex, after forgetting topology,
is the ordinary curried two-cochain module. -/
noncomputable def finiteGaloisDegreeTwoCochainModuleIso
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    (((TopRep.homogeneousCochains
      (TopRep.of (continuousGaloisUnitsRepresentation K L))).sc' 1 2 3).map
        (CategoryTheory.forget₂ (TopModuleCat ℤ) (ModuleCat ℤ))).X₂ ≅
      ModuleCat.of ℤ (Gal(L/K) → Gal(L/K) → DiscreteGaloisUnits L) :=
  (finiteGaloisDegreeTwoHomogeneousCochainAddEquiv K L).toIntLinearEquiv.toModuleIso

/-- The third component of the finite continuous cochain complex, after forgetting topology,
is the ordinary curried three-cochain module. -/
noncomputable def finiteGaloisDegreeThreeCochainModuleIso
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    (((TopRep.homogeneousCochains
      (TopRep.of (continuousGaloisUnitsRepresentation K L))).sc' 1 2 3).map
        (CategoryTheory.forget₂ (TopModuleCat ℤ) (ModuleCat ℤ))).X₃ ≅
      ModuleCat.of ℤ (Gal(L/K) → Gal(L/K) → Gal(L/K) → DiscreteGaloisUnits L) :=
  (finiteGaloisDegreeThreeHomogeneousCochainAddEquiv K L).toIntLinearEquiv.toModuleIso

/-- Currying identifies the usual binary-product two-cochain module with the curried form
used by the finite continuous comparison. -/
noncomputable def finiteGaloisCurryTwoCochainModuleIso
    (K L : Type) [Field K] [Field L] [Algebra K L] :
    ModuleCat.of ℤ (Gal(L/K) × Gal(L/K) → DiscreteGaloisUnits L) ≅
      ModuleCat.of ℤ (Gal(L/K) → Gal(L/K) → DiscreteGaloisUnits L) :=
  ({ toFun := fun f g h => f (g, h)
     invFun := fun f gh => f gh.1 gh.2
     left_inv := by intro f; funext gh; rfl
     right_inv := by intro f; funext g h; rfl
     map_add' := by intro f g; funext x y; rfl } :
    (Gal(L/K) × Gal(L/K) → DiscreteGaloisUnits L) ≃+
      (Gal(L/K) → Gal(L/K) → DiscreteGaloisUnits L)).toIntLinearEquiv.toModuleIso

/-- Currying identifies the usual ternary-product three-cochain module with the curried form
used by the finite continuous comparison. -/
noncomputable def finiteGaloisCurryThreeCochainModuleIso
    (K L : Type) [Field K] [Field L] [Algebra K L] :
    ModuleCat.of ℤ (Gal(L/K) × Gal(L/K) × Gal(L/K) → DiscreteGaloisUnits L) ≅
      ModuleCat.of ℤ (Gal(L/K) → Gal(L/K) → Gal(L/K) → DiscreteGaloisUnits L) :=
  ({ toFun := fun f g h i => f (g, h, i)
     invFun := fun f ghi => f ghi.1 ghi.2.1 ghi.2.2
     left_inv := by intro f; funext ghi; rfl
     right_inv := by intro f; funext g h i; rfl
     map_add' := by intro f g; funext x y z; rfl } :
    (Gal(L/K) × Gal(L/K) × Gal(L/K) → DiscreteGaloisUnits L) ≃+
      (Gal(L/K) → Gal(L/K) → Gal(L/K) → DiscreteGaloisUnits L)).toIntLinearEquiv.toModuleIso

/-- In degrees one through three, finite continuous unit cochains become the ordinary
inhomogeneous Galois cochain complex after topology is forgotten. -/
noncomputable def finiteGaloisContinuousToOrdinaryH2ShortComplexIso
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    ((TopRep.homogeneousCochains
      (TopRep.of (continuousGaloisUnitsRepresentation K L))).sc' 1 2 3).map
        (CategoryTheory.forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)) ≅
      groupCohomology.shortComplexH2 (Rep.ofAlgebraAutOnUnits K L) :=
  CategoryTheory.ShortComplex.isoMk
    (finiteGaloisDegreeOneCochainModuleIso K L)
    (finiteGaloisDegreeTwoCochainModuleIso K L ≪≫
      (finiteGaloisCurryTwoCochainModuleIso K L).symm)
    (finiteGaloisDegreeThreeCochainModuleIso K L ≪≫
      (finiteGaloisCurryThreeCochainModuleIso K L).symm)
    (by
      ext F
      funext gh
      rcases gh with ⟨g, h⟩
      change (continuousGaloisUnitsRepresentation K L g)
          (finiteGaloisDegreeOneHomogeneousToInhomogeneous K L F h) -
          finiteGaloisDegreeOneHomogeneousToInhomogeneous K L F (g * h) +
          finiteGaloisDegreeOneHomogeneousToInhomogeneous K L F g =
        finiteGaloisDegreeTwoHomogeneousToInhomogeneous K L
          ((TopRep.homogeneousCochains
            (TopRep.of (continuousGaloisUnitsRepresentation K L))).d 1 2 F) g h
      exact (congrFun (congrFun
        (finiteGaloisDegreeOneDifferentialCompatibility K L F) g) h).symm)
    (by
      ext F
      funext ghi
      rcases ghi with ⟨g, h, i⟩
      change (continuousGaloisUnitsRepresentation K L g)
          (finiteGaloisDegreeTwoHomogeneousToInhomogeneous K L F h i) -
          finiteGaloisDegreeTwoHomogeneousToInhomogeneous K L F (g * h) i +
          finiteGaloisDegreeTwoHomogeneousToInhomogeneous K L F g (h * i) -
          finiteGaloisDegreeTwoHomogeneousToInhomogeneous K L F g h =
        finiteGaloisDegreeThreeHomogeneousToInhomogeneous K L
          ((TopRep.homogeneousCochains
            (TopRep.of (continuousGaloisUnitsRepresentation K L))).d 2 3 F) g h i
      exact (congrFun (congrFun (congrFun
        (finiteGaloisDegreeTwoDifferentialCompatibility K L F) g) h) i).symm)

/-- For a finite field extension, continuous degree-two unit cohomology agrees with ordinary
degree-two Galois cohomology.  This closes the finite-level comparison required before passing to
the absolute Galois group in the local class-field-theory bridge. -/
noncomputable def finiteGaloisContinuousH2ToOrdinaryH2ModuleIso
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    (CategoryTheory.forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).obj
      (continuousGaloisUnitCohomology 2 K L) ≅
      groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 :=
  (CategoryTheory.forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).mapIso
    ((HomologicalComplex.homologyFunctorIso' (TopModuleCat ℤ) (ComplexShape.up ℕ) 1 2 3
      (by simp) (by simp)).app
        (TopRep.homogeneousCochains
          (TopRep.of (continuousGaloisUnitsRepresentation K L)))) ≪≫
    (((TopRep.homogeneousCochains
      (TopRep.of (continuousGaloisUnitsRepresentation K L))).sc' 1 2 3).mapHomologyIso
        (CategoryTheory.forget₂ (TopModuleCat ℤ) (ModuleCat ℤ))).symm ≪≫
    CategoryTheory.ShortComplex.homologyMapIso
      (finiteGaloisContinuousToOrdinaryH2ShortComplexIso K L) ≪≫
    (CategoryTheory.ShortComplex.homologyMapIso
      (groupCohomology.isoShortComplexH2 (Rep.ofAlgebraAutOnUnits K L))).symm

/-- The underlying additive groups in finite continuous and ordinary degree-two unit Galois
cohomology are canonically equivalent. -/
noncomputable def finiteGaloisContinuousH2ToOrdinaryH2AddEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    continuousGaloisUnitCohomology 2 K L ≃+
      groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 :=
  (finiteGaloisContinuousH2ToOrdinaryH2ModuleIso K L).toLinearEquiv.toAddEquiv

/-- Continuous degree-two unit Galois cohomology of a finite cyclic Galois extension is
annihilated by the extension degree.  This is the continuous counterpart of the cyclic norm
quotient denominator bound, before any Brauer--cohomology comparison. -/
theorem finiteGaloisContinuousH2_finrank_nsmul_eq_zero
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]
    [FiniteDimensional K L] [IsGalois K L]
    (z : continuousGaloisUnitCohomology 2 K L) :
    Module.finrank K L • z = 0 := by
  apply (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).injective
  rw [map_nsmul, map_zero]
  exact cyclicGaloisH2_finrank_nsmul_eq_zero K L
    (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z)

/-- Continuous degree-two unit cohomology of every finite-field extension vanishes.  This is the
finite-residue term of the local class-field-theory sequence, before any lifting through a
valuation ring is used. -/
theorem finiteField_continuousGaloisH2_eq_zero {K L : Type} [Field K] [Field L]
    [Algebra K L] [Finite L] (z : continuousGaloisUnitCohomology 2 K L) : z = 0 := by
  apply (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).injective
  rw [(finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).map_zero]
  exact finiteField_H2_eq_zero
    (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z)

/-- Continuous degree-two unit cohomology of a finite-field extension is subsingleton. -/
theorem finiteField_continuousGaloisH2_subsingleton {K L : Type} [Field K] [Field L]
    [Algebra K L] [Finite L] : Subsingleton (continuousGaloisUnitCohomology 2 K L) where
  allEq x y := (finiteField_continuousGaloisH2_eq_zero x).trans
    (finiteField_continuousGaloisH2_eq_zero y).symm

end GaloisForLFunctions.HTGeometry.ABHN
