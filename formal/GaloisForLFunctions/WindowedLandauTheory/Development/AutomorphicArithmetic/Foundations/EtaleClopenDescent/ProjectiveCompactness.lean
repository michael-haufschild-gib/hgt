import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Projective space and quasi-compactness of closed projective subschemes. -/

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace UpperTheory.Cb

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Projective `N`-space over the base ring, with its polynomial grading. -/
abbrev PSpace (R : Type u) [CommRing R] (N : ℕ) : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)

def PSpace.str (R : Type u) [CommRing R] (N : ℕ) : PSpace R N ⟶ Spec (.of R) :=
  Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom
    (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)))

/-- A projective morphism to the affine base with a closed immersion into projective space. -/
def IsProjOver {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) : Prop :=
  ∃ (N : ℕ) (i : X ⟶ PSpace R N), IsClosedImmersion i ∧ i ≫ PSpace.str R N = f

/-- Finite generation over the degree-zero ring makes the relative Proj quasi-compact. -/
theorem pspace_compact (R : Type u) [CommRing R] (N : ℕ) : CompactSpace (PSpace R N) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R
  haveI : IsScalarTower R (𝒜 0) (MvPolynomial (Fin (N + 1)) R) :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := ↥(𝒜 0))
      (A := MvPolynomial (Fin (N + 1)) R) (fun _ => rfl)
  haveI : Algebra.FiniteType (𝒜 0) (MvPolynomial (Fin (N + 1)) R) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R _ _
  exact QuasiCompact.compactSpace_of_compactSpace (Proj.toSpecZero 𝒜)

theorem IsProjOver.compactSpace {R : Type u} [CommRing R] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of R)} (hf : IsProjOver f) : CompactSpace X := by
  obtain ⟨N, i, hi, -⟩ := hf
  letI := hi
  haveI := pspace_compact R N
  exact QuasiCompact.compactSpace_of_compactSpace i

theorem IsProjOver.isSeparated {R : Type u} [CommRing R] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of R)} (hf : IsProjOver f) : X.IsSeparated := by
  obtain ⟨N, i, hi, -⟩ := hf
  letI := hi
  constructor
  rw [← Limits.terminal.comp_from i]
  infer_instance

theorem IsProjOver.restrict_clopen {R : Type u} [CommRing R] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of R)} (hf : IsProjOver f) (U : X.Opens) (hU : IsClosed (U : Set X)) :
    IsProjOver (U.ι ≫ f) := by
  obtain ⟨N, i, hi, rfl⟩ := hf
  letI := hi
  haveI : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι (by simpa using hU)
  exact ⟨N, U.ι ≫ i, inferInstance, Category.assoc _ _ _⟩

end UpperTheory.Cb
