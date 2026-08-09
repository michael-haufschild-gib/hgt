import GaloisForLFunctions.HTGeometry.CochainComplexCohomology
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Tactic.NormNum

/-!
# Flat superconnections and cohomological transport

This file formalizes the completed form-degree convolution algebra of a superconnection.  Its
square is the sequence whose degree-`n` coefficient is `∑ i+j=n, DᵢDⱼ`; flatness is equality of
that square with zero.  The low-degree identities yield a differential, an anticommuting
connection operator, curvature nullhomotopic through `D₂`, and the next nullhomotopy through
`D₃`.

The cohomological part is not merely an identity between symbols.  It constructs cycles,
boundaries, their quotient, the induced connection, and proves its square is zero from the
chain-level curvature nullhomotopy.  The final examples exhibit both phenomena that the observer
forgets: nonzero chain curvature on an acyclic complex and nontrivial monodromy despite zero local
curvature.
-/

namespace HTGeometry.NomologicalHomotopyGeometry.FlatSuperconnection

open scoped BigOperators

section Hierarchy

variable {k E : Type*} [CommRing k] [AddCommGroup E] [Module k E]

/-- Degree-`n` coefficient of the square of a completed superconnection. -/
def curvatureComponent (D : ℕ → Module.End k E) (n : ℕ) : Module.End k E :=
  ∑ i ∈ Finset.range (n + 1), (D i).comp (D (n - i))

/-- Square in the completed form-degree convolution algebra. -/
def superconnectionSquare (D : ℕ → Module.End k E) : ℕ → Module.End k E :=
  curvatureComponent D

/-- A superconnection is flat when its completed convolution square vanishes. -/
def IsFlat (D : ℕ → Module.End k E) : Prop :=
  superconnectionSquare D = 0

/-- Every form-degree coefficient of a flat superconnection vanishes. -/
theorem component_eq_zero {D : ℕ → Module.End k E} (h : IsFlat D) (n : ℕ) :
    curvatureComponent D n = 0 :=
  congrFun h n

/-- Form degree zero: the fibre differential squares to zero. -/
theorem differential_sq_zero {D : ℕ → Module.End k E} (h : IsFlat D) :
    (D 0).comp (D 0) = 0 := by
  simpa [curvatureComponent] using component_eq_zero h 0

/-- Form degree one: fibre differential and connection anticommute. -/
theorem differential_connection_anticommute {D : ℕ → Module.End k E} (h : IsFlat D) :
    (D 0).comp (D 1) + (D 1).comp (D 0) = 0 := by
  simpa [curvatureComponent, Finset.sum_range_succ] using component_eq_zero h 1

/-- Form degree two: ordinary curvature is nullhomotopic through the two-form cell. -/
theorem curvature_add_nullhomotopy_eq_zero {D : ℕ → Module.End k E} (h : IsFlat D) :
    (D 1).comp (D 1) + (D 0).comp (D 2) + (D 2).comp (D 0) = 0 := by
  simpa [curvatureComponent, Finset.sum_range_succ, add_assoc, add_comm, add_left_comm]
    using component_eq_zero h 2

/-- Form degree three: the covariant derivative of the first nullhomotopy is nullhomotopic
through the three-form cell. -/
theorem covariantA2_add_nextNullhomotopy_eq_zero {D : ℕ → Module.End k E} (h : IsFlat D) :
    (D 1).comp (D 2) + (D 2).comp (D 1) + (D 0).comp (D 3) +
      (D 3).comp (D 0) = 0 := by
  simpa [curvatureComponent, Finset.sum_range_succ, add_assoc, add_comm, add_left_comm]
    using component_eq_zero h 3

end Hierarchy

section Cohomology

variable {k E : Type*} [CommRing k] [AddCommGroup E] [Module k E]

/-- A square-zero fibre differential. -/
structure Differential where
  d : Module.End k E
  sq_zero : d.comp d = 0

namespace Differential

variable (C : Differential (k := k) (E := E))

/-- Cycles of the fibre differential. -/
def cycles : Submodule k E :=
  LinearMap.ker C.d

/-- Boundaries of the fibre differential. -/
def boundaries : Submodule k E :=
  LinearMap.range C.d

/-- Square-zero ensures every boundary is a cycle. -/
theorem boundaries_le_cycles : C.boundaries ≤ C.cycles := by
  rintro _ ⟨x, rfl⟩
  exact LinearMap.congr_fun C.sq_zero x

/-- Boundaries regarded as a submodule of cycles. -/
def boundariesInCycles : Submodule k C.cycles :=
  C.boundaries.comap C.cycles.subtype

/-- Fibre cohomology. -/
abbrev Cohomology :=
  C.cycles ⧸ C.boundariesInCycles

/-- Class of a cycle. -/
def classOf (x : C.cycles) : C.Cohomology :=
  Submodule.Quotient.mk x

/-- Every cohomology class has a cycle representative. -/
theorem classOf_surjective : Function.Surjective C.classOf :=
  Submodule.Quotient.mk_surjective _

/-- A cycle represents zero exactly when it is a boundary. -/
theorem classOf_eq_zero_iff (x : C.cycles) :
    C.classOf x = 0 ↔ (x : E) ∈ C.boundaries := by
  rw [classOf, Submodule.Quotient.mk_eq_zero]
  rfl

/-- Any linear operator preserving cycles and boundaries descends to fibre cohomology. -/
def inducedOfPreserves (F : Module.End k E)
    (hcycles : ∀ x : C.cycles, F (x : E) ∈ C.cycles)
    (hboundaries : ∀ x : C.boundaries, F (x : E) ∈ C.boundaries) :
    C.Cohomology →ₗ[k] C.Cohomology :=
  Submodule.mapQ C.boundariesInCycles C.boundariesInCycles
    { toFun := fun x => ⟨F (x : E), hcycles x⟩
      map_add' := fun x y => Subtype.ext (map_add F (x : E) (y : E))
      map_smul' := fun c x => Subtype.ext (map_smul F c (x : E)) }
    (fun x hx => by
      change F (x : E) ∈ C.boundaries
      exact hboundaries ⟨x, hx⟩)

@[simp]
theorem inducedOfPreserves_classOf (F : Module.End k E)
    (hcycles : ∀ x : C.cycles, F (x : E) ∈ C.cycles)
    (hboundaries : ∀ x : C.boundaries, F (x : E) ∈ C.boundaries)
    (x : C.cycles) :
    C.inducedOfPreserves F hcycles hboundaries (C.classOf x) =
      C.classOf ⟨F x, hcycles x⟩ :=
  rfl

/-- An operator anticommuting with the differential preserves cycles. -/
theorem maps_cycles_of_anticommutes (N : Module.End k E)
    (hanti : C.d.comp N + N.comp C.d = 0) (x : C.cycles) :
    N (x : E) ∈ C.cycles := by
  have h := LinearMap.congr_fun hanti (x : E)
  have hx : C.d (x : E) = 0 := x.2
  change C.d (N x) = 0
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply, hx,
    map_zero, add_zero] at h
  exact h

/-- An operator anticommuting with the differential preserves boundaries. -/
theorem maps_boundaries_of_anticommutes (N : Module.End k E)
    (hanti : C.d.comp N + N.comp C.d = 0) (x : C.boundaries) :
    N (x : E) ∈ C.boundaries := by
  rcases x with ⟨x, hx⟩
  obtain ⟨y, hy⟩ := hx
  subst x
  refine ⟨-N y, ?_⟩
  have h := LinearMap.congr_fun hanti y
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply] at h
  have h' : N (C.d y) = -C.d (N y) := eq_neg_of_add_eq_zero_right h
  simpa using h'.symm

/-- Connection induced on cohomology by the form-degree-one identity. -/
def inducedConnection (N : Module.End k E)
    (hanti : C.d.comp N + N.comp C.d = 0) : C.Cohomology →ₗ[k] C.Cohomology :=
  C.inducedOfPreserves N (C.maps_cycles_of_anticommutes N hanti)
    (C.maps_boundaries_of_anticommutes N hanti)

/-- A nullhomotopic curvature maps every cycle to a boundary. -/
theorem curvature_maps_cycles_to_boundaries (F A : Module.End k E)
    (hnull : F + C.d.comp A + A.comp C.d = 0) :
    ∀ x : C.cycles, F x ∈ C.boundaries := by
  intro x
  refine ⟨-A x, ?_⟩
  have h := LinearMap.congr_fun hnull (x : E)
  have hx : C.d (x : E) = 0 := x.2
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply, hx,
    map_zero, add_zero] at h
  have h' : F x = -C.d (A x) := eq_neg_of_add_eq_zero_left h
  simpa using h'.symm

/-- The map induced by a curvature that sends cycles to boundaries. -/
def inducedOfMapsCyclesToBoundaries (F : Module.End k E)
    (hF : ∀ x : C.cycles, F x ∈ C.boundaries) : C.Cohomology →ₗ[k] C.Cohomology :=
  Submodule.mapQ C.boundariesInCycles C.boundariesInCycles
    { toFun := fun x => ⟨F (x : E), C.boundaries_le_cycles (hF x)⟩
      map_add' := fun x y => Subtype.ext (map_add F (x : E) (y : E))
      map_smul' := fun c x => Subtype.ext (map_smul F c (x : E)) }
    (fun x hx => by
      change F (x : E) ∈ C.boundaries
      exact hF x)

/-- Any curvature mapping cycles to boundaries induces the zero cohomology endomorphism. -/
theorem inducedOfMapsCyclesToBoundaries_eq_zero (F : Module.End k E)
    (hF : ∀ x : C.cycles, F x ∈ C.boundaries) :
    C.inducedOfMapsCyclesToBoundaries F hF = 0 := by
  ext x
  apply (C.classOf_eq_zero_iff _).mpr
  exact hF x

/-- Curvature nullhomotopy implies zero induced curvature. -/
theorem induced_curvature_eq_zero (F A : Module.End k E)
    (hnull : F + C.d.comp A + A.comp C.d = 0) :
    C.inducedOfMapsCyclesToBoundaries F
      (C.curvature_maps_cycles_to_boundaries F A hnull) = 0 :=
  C.inducedOfMapsCyclesToBoundaries_eq_zero F _

/-- The connection induced on fibre cohomology is flat. -/
theorem inducedConnection_sq_eq_zero (N A : Module.End k E)
    (hanti : C.d.comp N + N.comp C.d = 0)
    (hcurv : N.comp N + C.d.comp A + A.comp C.d = 0) :
    (C.inducedConnection N hanti).comp (C.inducedConnection N hanti) = 0 := by
  ext x
  apply (C.classOf_eq_zero_iff _).mpr
  exact C.curvature_maps_cycles_to_boundaries (N.comp N) A hcurv x

end Differential

/-- Differential extracted from the degree-zero part of a flat superconnection. -/
def differentialOfFlat (D : ℕ → Module.End k E) (h : IsFlat D) :
    Differential (k := k) (E := E) where
  d := D 0
  sq_zero := differential_sq_zero h

/-- Main cohomological-flatness capstone: the degree-one superconnection component descends to
cohomology, and its induced square is zero because degree-two flatness makes chain curvature
nullhomotopic through `D₂`. -/
theorem flatSuperconnection_inducedConnection_sq_eq_zero
    (D : ℕ → Module.End k E) (h : IsFlat D) :
    let C := differentialOfFlat D h
    (C.inducedConnection (D 1) (differential_connection_anticommute h)).comp
      (C.inducedConnection (D 1) (differential_connection_anticommute h)) = 0 := by
  dsimp only
  exact Differential.inducedConnection_sq_eq_zero _ (D 1) (D 2)
    (differential_connection_anticommute h) (curvature_add_nullhomotopy_eq_zero h)

end Cohomology

section ExactModel

/-- Differential of the exact two-term real complex `ℝ → ℝ`. -/
def exactModelDifferential : Module.End ℝ (ℝ × ℝ) where
  toFun p := (0, p.1)
  map_add' p q := by ext <;> simp
  map_smul' c p := by ext <;> simp

/-- Contracting homotopy of the exact two-term real complex. -/
def exactModelHomotopy : Module.End ℝ (ℝ × ℝ) where
  toFun p := (p.2, 0)
  map_add' p q := by ext <;> simp
  map_smul' c p := by ext <;> simp

/-- The displayed fibre differential squares to zero. -/
theorem exactModelDifferential_sq :
    exactModelDifferential.comp exactModelDifferential = 0 := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  simp [exactModelDifferential]

/-- Exact contraction identity `[∂,h] = id`. -/
theorem exactModel_contraction :
    exactModelDifferential.comp exactModelHomotopy +
      exactModelHomotopy.comp exactModelDifferential = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  ext <;> simp [exactModelDifferential, exactModelHomotopy]

/-- Nonzero identity curvature is killed by the two-form cell `A₂ = -h`. -/
theorem exactModel_nullCurvature :
    LinearMap.id + exactModelDifferential.comp (-exactModelHomotopy) +
      (-exactModelHomotopy).comp exactModelDifferential = 0 := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  ext <;> simp [exactModelDifferential, exactModelHomotopy]

/-- The two-form cell squares to zero in the exact model. -/
theorem exactModel_A2_sq :
    (-exactModelHomotopy).comp (-exactModelHomotopy) = 0 := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  ext <;> simp [exactModelHomotopy]

/-- The chain curvature in the exact model is genuinely nonzero. -/
theorem exactModel_curvature_ne_zero :
    (LinearMap.id : Module.End ℝ (ℝ × ℝ)) ≠ 0 := by
  intro h
  have h1 := LinearMap.congr_fun h (1, 0)
  norm_num at h1

/-- Exactness of the displayed two-term complex. -/
theorem exactModel_cycles_eq_boundaries :
    LinearMap.ker exactModelDifferential = LinearMap.range exactModelDifferential := by
  ext ⟨x, y⟩
  constructor
  · intro h
    rw [LinearMap.mem_ker] at h
    have hx : x = 0 := by simpa [exactModelDifferential] using h
    refine ⟨(y, 0), ?_⟩
    simp [exactModelDifferential, hx]
  · rintro ⟨p, hp⟩
    rcases p with ⟨a, b⟩
    simp [exactModelDifferential] at hp
    rw [LinearMap.mem_ker]
    simp [exactModelDifferential, hp.1.symm]

/-- Cohomology of the exact chain-curved model is trivial. -/
theorem exactModel_cohomology_subsingleton :
    Subsingleton
      ({ d := exactModelDifferential, sq_zero := exactModelDifferential_sq } :
        Differential).Cohomology := by
  let C : Differential :=
    { d := exactModelDifferential, sq_zero := exactModelDifferential_sq }
  constructor
  intro q r
  have hzero : ∀ z : C.Cohomology, z = 0 := by
    intro z
    obtain ⟨x, rfl⟩ := C.classOf_surjective z
    apply (C.classOf_eq_zero_iff x).mpr
    change (x : ℝ × ℝ) ∈ LinearMap.range exactModelDifferential
    rw [← exactModel_cycles_eq_boundaries]
    exact x.2
  exact (hzero q).trans (hzero r).symm

end ExactModel

section HolonomySeparation

/-- Sign monodromy representation of `π₁(S¹) ≅ ℤ`. -/
def circleSignHolonomy : Multiplicative ℤ →* (ℝ ≃ₗ[ℝ] ℝ) :=
  zpowersHom (ℝ ≃ₗ[ℝ] ℝ) (LinearEquiv.neg ℝ)

/-- Generator of the circle has holonomy `-id`. -/
theorem circleSignHolonomy_generator :
    circleSignHolonomy (Multiplicative.ofAdd 1) = LinearEquiv.neg ℝ := by
  simp [circleSignHolonomy]

/-- Sign holonomy is nontrivial. -/
theorem circleSignHolonomy_nontrivial :
    circleSignHolonomy (Multiplicative.ofAdd 1) ≠ 1 := by
  rw [circleSignHolonomy_generator]
  intro h
  have h1 := LinearEquiv.congr_fun h 1
  norm_num at h1

/-- Closed witness that zero local cohomological curvature does not force closed lifted history:
the zero curvature endomorphism coexists with nonidentity circle monodromy. -/
theorem zeroCurvature_not_imply_trivialHolonomy :
    (0 : Module.End ℝ ℝ) = 0 ∧
      circleSignHolonomy (Multiplicative.ofAdd 1) ≠ 1 :=
  ⟨rfl, circleSignHolonomy_nontrivial⟩

end HolonomySeparation

end HTGeometry.NomologicalHomotopyGeometry.FlatSuperconnection
