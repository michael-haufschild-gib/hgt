import GaloisForLFunctions.HTGeometry.FiniteSpecialUnitarySimplyConnected
import GaloisForLFunctions.HTGeometry.SphereSimplyConnected
import GaloisForLFunctions.HTGeometry.TorusChartFundamentalGroup

/-!
# Global phases and logarithms on special-unitary groups and spheres

Circle-valued continuous functions on finite special-unitary groups and on
real spheres of dimension at least two have unique real phases after fixing
one phase value. Nonvanishing complex-valued functions on these domains
have continuous complex logarithms. Simple connectivity and local path
connectedness are proved for the domains, not supplied as premises.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem existsUnique_circlePhase {X : Type*} [TopologicalSpace X]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (f : C(X, Circle)) (x : X) :
    ∃! g : C(X, ℝ), g x = (f x : ℂ).arg ∧ Circle.exp ∘ g = f :=
  Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f x
    (f x : ℂ).arg (Circle.exp_arg (f x))

private theorem exists_complexLog {X : Type*} [TopologicalSpace X]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (f : C(X, Units ℂ)) (x : X) :
    ∃ g : C(X, ℂ), ∀ y, Complex.exp (g y) = (f y : ℂ) := by
  obtain ⟨z, hz⟩ := complexExpUnits_isAddQuotientCoveringMap.toIsQuotientMap.surjective (f x)
  obtain ⟨g, ⟨_, hg⟩, _⟩ :=
    complexExpUnits_isAddQuotientCoveringMap.isCoveringMap.existsUnique_continuousMap_lifts
      f x z hz
  refine ⟨g, fun y => ?_⟩
  have h := congrArg (fun u : Units ℂ =>
    ((unitsHomeomorphNeZero (G₀ := ℂ)) u : ℂ)) (congrFun hg y)
  simp only [complexExpUnits, Function.comp_apply, Homeomorph.apply_symm_apply] at h
  change Complex.exp (g y) = (f y : ℂ) at h
  exact h

/-- Every circle-valued function on a finite special-unitary group admits
a unique global phase with the principal value prescribed at the identity. -/
theorem finiteSpecialUnitary_existsUnique_phase
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : C(Matrix.specialUnitaryGroup ι ℂ, Circle)) :
    ∃! g : C(Matrix.specialUnitaryGroup ι ℂ, ℝ),
      g 1 = (f 1 : ℂ).arg ∧ Circle.exp ∘ g = f :=
  existsUnique_circlePhase f 1

/-- Every nonvanishing complex-valued continuous function on a finite
special-unitary group has a continuous logarithm. -/
theorem finiteSpecialUnitary_exists_complexLog
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : C(Matrix.specialUnitaryGroup ι ℂ, Units ℂ)) :
    ∃ g : C(Matrix.specialUnitaryGroup ι ℂ, ℂ),
      ∀ S, Complex.exp (g S) = (f S : ℂ) :=
  exists_complexLog f 1

/-- Circle-valued functions on a real sphere of dimension at least two admit
a unique global phase once the principal phase is prescribed at one point. -/
theorem realSphere_existsUnique_phase (n : ℕ)
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1, Circle))
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1) :
    ∃! g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1, ℝ),
      g x = (f x : ℂ).arg ∧ Circle.exp ∘ g = f :=
  existsUnique_circlePhase f x

/-- Nonvanishing complex-valued functions on a real sphere of dimension at
least two have continuous logarithms. -/
theorem realSphere_exists_complexLog (n : ℕ)
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1, Units ℂ)) :
    ∃ g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1, ℂ),
      ∀ x, Complex.exp (g x) = (f x : ℂ) :=
  exists_complexLog f ⟨EuclideanSpace.single 0 1, by simp⟩

end

end GaloisForLFunctions.HTGeometry
