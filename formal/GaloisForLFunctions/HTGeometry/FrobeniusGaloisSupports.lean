import GaloisForLFunctions.HTGeometry.FrobeniusGaloisObservation
import GaloisForLFunctions.HTGeometry.TailQuotientSeparationLaw
import GaloisForLFunctions.HTGeometry.SignedCancellationQuotient

/-!
# Coordinate cylinders and signed cancellation as Frobenius properties

The fixed points and saturation laws of arXiv:2609.09529, Proposition 3.13,
apply to coordinate restriction and to the finite signed-mass observation.
-/
namespace GaloisForLFunctions.HTGeometry
open FrobeniusGalois

/-- Observation of precisely a prescribed support of a record. -/
def supportObservation {I A : Type*} (E : Set I) (u : I → A) : E → A :=
  fun i => u i.1

/-- The possibility closure of a record is its existing coordinate cylinder. -/
theorem supportObservation_upper_singleton {I A : Type*} (E : Set I) (u : I → A) :
    upper (supportObservation E) {u} = {v | CoordinatesAgreeOn E v u} := by
  ext v
  constructor
  · rintro ⟨w, hw, he⟩ i hi
    have hw' : w = u := hw
    rw [hw'] at he
    exact (congrFun he ⟨i, hi⟩).symm
  · intro h
    refine ⟨u, rfl, ?_⟩
    funext i
    exact (h i.1 i.2).symm

/-- A coordinate cylinder is simultaneously a certain and a possible property. -/
theorem supportCylinder_fixed {I A : Type*} (E : Set I) (u : I → A) :
    lower (supportObservation E) {v | CoordinatesAgreeOn E v u} =
      {v | CoordinatesAgreeOn E v u} ∧
    upper (supportObservation E) {v | CoordinatesAgreeOn E v u} =
      {v | CoordinatesAgreeOn E v u} := by
  rw [← supportObservation_upper_singleton, lower_upper, upper_idempotent]
  exact ⟨rfl, rfl⟩

/-- Existential support completion obeys the meet-Frobenius law. -/
theorem supportObservation_frobenius {I A : Type*} (E : Set I) (S T : Set (I → A)) :
    upper (supportObservation E) (S ∩ upper (supportObservation E) T) =
      upper (supportObservation E) S ∩ upper (supportObservation E) T :=
  upper_inter_upper _ S T

/-- Finite-horizon observation is coordinate restriction to an initial interval. -/
theorem finitePrefix_frobenius_singleton {A : Type*} (N : ℕ) (u : ℕ → A) :
    upper (supportObservation {n | n ≤ N}) {u} = {v | FinitePrefixAgree N v u} := by
  rw [supportObservation_upper_singleton]
  ext v
  simp [CoordinatesAgreeOn, FinitePrefixAgree]

/-- The observation retaining the total signed mass in each quotient fiber. -/
noncomputable def signedMassObservation {P K : Type*} [Fintype P] [DecidableEq K]
    (q : P → K) (mu : P → ℝ) : K → ℝ :=
  fun k => _root_.HTGeometry.finiteSignedFiberMass mu q k

/-- Possible zero signed masses are exactly the sources annihilating every quotient readout. -/
theorem signedMassObservation_upper_zero {P K : Type*}
    [Fintype P] [Fintype K] [DecidableEq K] (q : P → K) :
    upper (signedMassObservation q) {0} =
      {mu | ∀ f : K → ℝ, _root_.HTGeometry.finiteSignedFunctional mu
        (_root_.HTGeometry.finiteQuotientObservable q f) = 0} := by
  ext mu
  simp only [Set.mem_setOf_eq]
  rw [_root_.HTGeometry.finiteSignedFunctional_annihilates_quotient_iff]
  have hz : signedMassObservation q (0 : P → ℝ) = 0 := by
    funext k
    simp [signedMassObservation, _root_.HTGeometry.finiteSignedFiberMass]
  constructor
  · rintro ⟨nu, hn, he⟩ k
    have hn' : nu = 0 := hn
    rw [hn', hz] at he
    exact (congrFun he k).symm
  · intro h
    refine ⟨0, rfl, ?_⟩
    rw [hz]
    funext k
    exact (h k).symm

/-- Signed cancellation is itself a fixed observable property. -/
theorem signedCancellation_frobenius_fixed {P K : Type*}
    [Fintype P] [Fintype K] [DecidableEq K] (q : P → K) :
    lower (signedMassObservation q)
      {mu | ∀ f : K → ℝ, _root_.HTGeometry.finiteSignedFunctional mu
        (_root_.HTGeometry.finiteQuotientObservable q f) = 0} =
      {mu | ∀ f : K → ℝ, _root_.HTGeometry.finiteSignedFunctional mu
        (_root_.HTGeometry.finiteQuotientObservable q f) = 0} := by
  rw [← signedMassObservation_upper_zero, lower_upper]

end GaloisForLFunctions.HTGeometry
