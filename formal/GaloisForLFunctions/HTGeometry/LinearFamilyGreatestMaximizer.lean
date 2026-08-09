import GaloisForLFunctions.HTGeometry.LinearFamilyDefectSupermodularity

/-!
# The canonical greatest defect maximizer

Supermodularity of linear-family deficiency makes the set of defect maximizers a lattice with a
largest element, and that element is unique.  It is therefore a function of the family alone, and
every statement conditioned on "let `U` be the greatest maximizer" can be read as a statement about
this one subspace.

The two defining properties are recorded separately, so a hypothesis of either shape is discharged
by naming the family.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {𝕜 X Y J : Type*} [DivisionRing 𝕜]
  [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
  [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y]

/-- The greatest subspace maximizing the deficiency of a linear-map family. -/
def linearFamilyGreatestMaximizer (A : J → X →ₗ[𝕜] Y) : Submodule 𝕜 X :=
  (existsUnique_linearFamilyDefect_greatestMaximizer A).choose

theorem linearFamilyGreatestMaximizer_spec (A : J → X →ₗ[𝕜] Y) :
    (∀ V : Submodule 𝕜 X,
        linearFamilyDefect A V ≤ linearFamilyDefect A (linearFamilyGreatestMaximizer A)) ∧
      ∀ V : Submodule 𝕜 X,
        linearFamilyDefect A V = linearFamilyDefect A (linearFamilyGreatestMaximizer A) →
          V ≤ linearFamilyGreatestMaximizer A :=
  (existsUnique_linearFamilyDefect_greatestMaximizer A).choose_spec.1

/-- **The canonical maximizer maximizes.** -/
theorem linearFamilyDefect_le_greatestMaximizer (A : J → X →ₗ[𝕜] Y) (V : Submodule 𝕜 X) :
    linearFamilyDefect A V ≤ linearFamilyDefect A (linearFamilyGreatestMaximizer A) :=
  (linearFamilyGreatestMaximizer_spec A).1 V

/-- **The canonical maximizer is greatest.**  This is the shape every conditional two-replica
statement assumes. -/
theorem le_linearFamilyGreatestMaximizer (A : J → X →ₗ[𝕜] Y) (V : Submodule 𝕜 X)
    (h : linearFamilyDefect A V = linearFamilyDefect A (linearFamilyGreatestMaximizer A)) :
    V ≤ linearFamilyGreatestMaximizer A :=
  (linearFamilyGreatestMaximizer_spec A).2 V h

/-- **The canonical maximizer is the only subspace with both properties.** -/
theorem eq_linearFamilyGreatestMaximizer (A : J → X →ₗ[𝕜] Y) (U : Submodule 𝕜 X)
    (hmax : ∀ V : Submodule 𝕜 X, linearFamilyDefect A V ≤ linearFamilyDefect A U)
    (hgreatest : ∀ V : Submodule 𝕜 X,
      linearFamilyDefect A V = linearFamilyDefect A U → V ≤ U) :
    U = linearFamilyGreatestMaximizer A :=
  (existsUnique_linearFamilyDefect_greatestMaximizer A).choose_spec.2 U ⟨hmax, hgreatest⟩

/-- The all-subspaces Hall condition is the vanishing of the canonical maximizer's deficiency. -/
theorem linearFamilyHall_iff_greatestMaximizer_defect_eq_zero (A : J → X →ₗ[𝕜] Y) :
    LinearFamilyHall A ↔ linearFamilyDefect A (linearFamilyGreatestMaximizer A) = 0 :=
  linearFamilyHall_iff_maximizer_defect_eq_zero A _ (linearFamilyDefect_le_greatestMaximizer A)

/-- **Every deficiency-preserving automorphism fixes the canonical maximizer.** -/
theorem linearFamilyGreatestMaximizer_map_eq_of_invariant (A : J → X →ₗ[𝕜] Y) (g : X ≃ₗ[𝕜] X)
    (hinvariant : ∀ V : Submodule 𝕜 X,
      linearFamilyDefect A (V.map (g : X →ₗ[𝕜] X)) = linearFamilyDefect A V) :
    (linearFamilyGreatestMaximizer A).map (g : X →ₗ[𝕜] X) = linearFamilyGreatestMaximizer A :=
  linearFamilyDefect_greatestMaximizer_map_eq_of_invariant A (linearFamilyGreatestMaximizer A) g
    (le_linearFamilyGreatestMaximizer A) hinvariant

/-- **Every simultaneous covariance of the family fixes the canonical maximizer.** -/
theorem linearFamilyGreatestMaximizer_map_eq_of_covariant (A : J → X →ₗ[𝕜] Y)
    (gX : X ≃ₗ[𝕜] X) (gY : Y ≃ₗ[𝕜] Y) (σ : J ≃ J)
    (hcov : ∀ j, (A (σ j)).comp (gX : X →ₗ[𝕜] X) = (gY : Y →ₗ[𝕜] Y).comp (A j)) :
    (linearFamilyGreatestMaximizer A).map (gX : X →ₗ[𝕜] X) = linearFamilyGreatestMaximizer A :=
  linearFamilyDefect_greatestMaximizer_map_eq_of_covariant A (linearFamilyGreatestMaximizer A)
    gX gY σ (le_linearFamilyGreatestMaximizer A) hcov

end

section SpanCovariant

variable {𝕜 X Y J : Type*} [Field 𝕜]
  [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]
  [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y]

/-- **Every span-preserving symmetry fixes the canonical maximizer.**  This covers continuous
mixing of the generators, not only permutations of them. -/
theorem linearFamilyGreatestMaximizer_map_eq_of_spanCovariant (A : J → X →ₗ[𝕜] Y)
    (gX : X ≃ₗ[𝕜] X) (gY : Y ≃ₗ[𝕜] Y)
    (hforward : ∀ j,
      (((gY : Y →ₗ[𝕜] Y).comp (A j)).comp (gX.symm : X →ₗ[𝕜] X)) ∈ linearFamilyOperatorSpan A)
    (hbackward : ∀ j,
      (((gY.symm : Y →ₗ[𝕜] Y).comp (A j)).comp (gX : X →ₗ[𝕜] X)) ∈ linearFamilyOperatorSpan A) :
    (linearFamilyGreatestMaximizer A).map (gX : X →ₗ[𝕜] X) = linearFamilyGreatestMaximizer A :=
  linearFamilyDefect_greatestMaximizer_map_eq_of_spanCovariant A
    (linearFamilyGreatestMaximizer A) gX gY (le_linearFamilyGreatestMaximizer A)
    hforward hbackward

end SpanCovariant

end GaloisForLFunctions.HTGeometry
