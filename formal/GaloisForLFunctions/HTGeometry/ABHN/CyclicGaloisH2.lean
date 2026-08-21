import GaloisForLFunctions.HTGeometry.ABHN.CyclicHilbert90

/-!
# Degree-two cohomology of cyclic Galois extensions

For a finite cyclic Galois extension, Mathlib's periodic resolution presents degree-two Galois
cohomology of units as generator-fixed units modulo norm images.  This file exposes that result in
the field-theoretic language used by cyclic algebras.

This is one input for the cyclic-algebra route to local invariants.  It does not identify this
cohomology group with a Brauer group and does not construct local reciprocity.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open CategoryTheory groupCohomology Rep Rep.FiniteCyclicGroup

attribute [local instance] IsCyclic.commGroup

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]

/-- A chosen generator of a cyclic Galois group. -/
noncomputable def cyclicGaloisGenerator : Gal(L/K) :=
  (IsCyclic.exists_generator (α := Gal(L/K))).choose

/-- The chosen Galois automorphism generates the Galois group. -/
theorem cyclicGaloisGenerator_spec :
    ∀ sigma : Gal(L/K), sigma ∈ Subgroup.zpowers (cyclicGaloisGenerator K L) :=
  (IsCyclic.exists_generator (α := Gal(L/K))).choose_spec

section H2

variable [FiniteDimensional K L]

/-- The quotient map from units fixed by a cyclic generator to degree-two Galois cohomology. -/
noncomputable def cyclicGaloisH2Projection :
    LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).applyAsHom (cyclicGaloisGenerator K L) -
        𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap →+
      groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 :=
  (Rep.FiniteCyclicGroup.groupCohomologyπEven
    (Rep.ofAlgebraAutOnUnits K L) (cyclicGaloisGenerator K L)
      (cyclicGaloisGenerator_spec K L) 2 even_two).hom.toAddMonoidHom

/-- Every degree-two Galois cohomology class of cyclic units has a generator-fixed-unit
representative. -/
theorem cyclicGaloisH2Projection_surjective :
    Function.Surjective (cyclicGaloisH2Projection K L) :=
  (ModuleCat.epi_iff_surjective
    (Rep.FiniteCyclicGroup.groupCohomologyπEven
      (Rep.ofAlgebraAutOnUnits K L) (cyclicGaloisGenerator K L)
        (cyclicGaloisGenerator_spec K L) 2 even_two)).mp inferInstance

/-- A generator-fixed unit represents zero in degree-two Galois cohomology precisely when it is
a norm. -/
theorem cyclicGaloisH2Projection_eq_zero_iff
    (x : LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).applyAsHom (cyclicGaloisGenerator K L) -
        𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap) :
    cyclicGaloisH2Projection K L x = 0 ↔
      x.1 ∈ LinearMap.range (Rep.ofAlgebraAutOnUnits K L).norm.hom.toLinearMap :=
  Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff
    (Rep.ofAlgebraAutOnUnits K L) (cyclicGaloisGenerator K L)
      (cyclicGaloisGenerator_spec K L) 2 even_two x

/-- Two generator-fixed units represent the same degree-two Galois cohomology class precisely
when their quotient in additive notation is a norm. -/
theorem cyclicGaloisH2Projection_eq_iff
    (x y : LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).applyAsHom (cyclicGaloisGenerator K L) -
        𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap) :
    cyclicGaloisH2Projection K L x = cyclicGaloisH2Projection K L y ↔
      x.1 - y.1 ∈ LinearMap.range (Rep.ofAlgebraAutOnUnits K L).norm.hom.toLinearMap :=
  Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_iff
    (Rep.ofAlgebraAutOnUnits K L) (cyclicGaloisGenerator K L)
      (cyclicGaloisGenerator_spec K L) 2 even_two x y

/-- The subgroup of generator-fixed units that are norms. -/
noncomputable def cyclicGaloisH2NormImage :
    AddSubgroup (LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).applyAsHom (cyclicGaloisGenerator K L) -
        𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap) where
  carrier := {x | x.1 ∈ LinearMap.range (Rep.ofAlgebraAutOnUnits K L).norm.hom.toLinearMap}
  zero_mem' := by
    exact ⟨0, map_zero _⟩
  add_mem' := by
    intro x y hx hy
    exact (LinearMap.range (Rep.ofAlgebraAutOnUnits K L).norm.hom.toLinearMap).add_mem hx hy
  neg_mem' := by
    intro x hx
    exact (LinearMap.range (Rep.ofAlgebraAutOnUnits K L).norm.hom.toLinearMap).neg_mem hx

/-- Within generator-fixed units, the norm-image subgroup is exactly the kernel of the degree-two
cohomology projection. -/
theorem cyclicGaloisH2NormImage_eq_ker :
    cyclicGaloisH2NormImage K L = (cyclicGaloisH2Projection K L).ker := by
  ext x
  rw [AddMonoidHom.mem_ker]
  exact (cyclicGaloisH2Projection_eq_zero_iff K L x).symm

/-- Generator-fixed units, their norm-image subgroup, and degree-two Galois cohomology are exact. -/
theorem cyclicGaloisH2NormImage_exact :
    Function.Exact (cyclicGaloisH2NormImage K L).subtype (cyclicGaloisH2Projection K L) := by
  intro x
  change x ∈ (cyclicGaloisH2Projection K L).ker ↔ _
  rw [← cyclicGaloisH2NormImage_eq_ker K L]
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.property

/-- The quotient of generator-fixed units by norm images is degree-two Galois cohomology. -/
noncomputable def cyclicGaloisH2NormQuotientEquiv :
    (LinearMap.ker
      ((Rep.ofAlgebraAutOnUnits K L).applyAsHom (cyclicGaloisGenerator K L) -
        𝟙 (Rep.ofAlgebraAutOnUnits K L)).hom.toLinearMap) ⧸
      cyclicGaloisH2NormImage K L ≃+
      groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 :=
  (QuotientAddGroup.quotientAddEquivOfEq (cyclicGaloisH2NormImage_eq_ker K L)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (cyclicGaloisH2Projection K L)
      (cyclicGaloisH2Projection_surjective K L))

end H2

end GaloisForLFunctions.HTGeometry.ABHN
