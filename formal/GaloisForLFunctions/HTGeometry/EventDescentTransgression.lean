import GaloisForLFunctions.HTGeometry.EventSecondOrderSoldering

/-!
# Endpoint stories and event-descent transgression

This file proves two unconditional algebraic results used to delimit the actuality research
program:

* group-valued edge comparisons come from one endpoint-indexed family exactly when every
  comparison triangle has trivial holonomy;
* the discrepancy between the seam defect of a two-step event path and that of a direct event
  edge is exactly the covariant defect of their triangle mismatch.

These results are elementary cocycle reconstruction and a covariant Leibniz identity. No quantum
event, spacetime, force, gauge group, gravitational dynamics, or physical interpretation is
assumed.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

section EndpointStory

variable {X G : Type*} [Group G]

/-- Closed triangular comparison associated with group-valued event-edge data. -/
def completionTriangleHolonomy (τ : X → X → G) (x y z : X) : G :=
  τ x y * τ y z * (τ x z)⁻¹

/-- Edge comparisons are relative values of one endpoint-indexed family. -/
def HasEndpointStory (τ : X → X → G) : Prop :=
  ∃ U : X → G, ∀ x y, τ x y = (U x)⁻¹ * U y

/-- Every two-step comparison agrees with the corresponding direct comparison. -/
def HasFlatTriangles (τ : X → X → G) : Prop :=
  ∀ x y z, τ x y * τ y z = τ x z

/--
Endpoint-story reconstruction: on a nonempty event set, group-valued comparisons are a global
coboundary exactly when all comparison triangles compose strictly.
-/
theorem hasEndpointStory_iff_hasFlatTriangles [Nonempty X] (τ : X → X → G) :
    HasEndpointStory τ ↔ HasFlatTriangles τ := by
  constructor
  · rintro ⟨U, hU⟩ x y z
    rw [hU x y, hU y z, hU x z]
    group
  · intro hτ
    let b : X := Classical.choice (inferInstance : Nonempty X)
    refine ⟨fun x => τ b x, ?_⟩
    intro x y
    have hxy := hτ b x y
    calc
      τ x y = (τ b x)⁻¹ * (τ b x * τ x y) := by group
      _ = (τ b x)⁻¹ * τ b y := by rw [hxy]

/-- Endpoint representability is equivalent to identity holonomy on every triangle. -/
theorem hasEndpointStory_iff_triangleHolonomy_eq_one [Nonempty X]
    (τ : X → X → G) :
    HasEndpointStory τ ↔
      ∀ x y z, completionTriangleHolonomy τ x y z = 1 := by
  rw [hasEndpointStory_iff_hasFlatTriangles]
  constructor
  · intro h x y z
    rw [completionTriangleHolonomy, h x y z]
    simp
  · intro h x y z
    have hxyz := h x y z
    rw [completionTriangleHolonomy] at hxyz
    exact mul_inv_eq_one.mp hxyz

/-- Failure of every endpoint story has a nontrivial triangular witness, and conversely. -/
theorem noEndpointStory_iff_exists_nontrivial_triangle [Nonempty X]
    (τ : X → X → G) :
    ¬ HasEndpointStory τ ↔
      ∃ x y z, completionTriangleHolonomy τ x y z ≠ 1 := by
  rw [hasEndpointStory_iff_triangleHolonomy_eq_one]
  simp

end EndpointStory

section SeamCurvature

variable {R K I C : Type*}
variable [CommRing R]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup I] [Module R I]
variable [AddCommGroup C] [Module R C]

/-- Failure of an event seam to intertwine the laws at its two endpoints. -/
def eventSeamDefect
    (a : Module.End R K) (p : Module.End R C) (η : C →ₗ[R] K) :
    C →ₗ[R] K :=
  a.comp η - η.comp p

/-- Failure of a two-step event comparison to equal a supplied direct comparison. -/
def eventTriangleDefect
    (b : I →ₗ[R] K) (r : C →ₗ[R] I) (η : C →ₗ[R] K) :
    C →ₗ[R] K :=
  b.comp r - η

/--
Discrete descent Bianchi identity. The discrepancy between the seam defects of a two-step path
and a direct edge is the covariant defect of their triangle mismatch.
-/
theorem eventSeam_triangleDefect_bianchi
    (a : Module.End R K) (d : Module.End R I) (p : Module.End R C)
    (b : I →ₗ[R] K) (r : C →ₗ[R] I) (η : C →ₗ[R] K) :
    (eventSeamDefect a d b).comp r +
          b.comp (eventSeamDefect d p r) -
        eventSeamDefect a p η =
      eventSeamDefect a p (eventTriangleDefect b r η) := by
  ext x
  simp [eventSeamDefect, eventTriangleDefect]
  abel

/-- On a flat event triangle, seam defects obey the exact covariant composition rule. -/
theorem eventSeam_compose_of_triangle_flat
    (a : Module.End R K) (d : Module.End R I) (p : Module.End R C)
    (b : I →ₗ[R] K) (r : C →ₗ[R] I) (η : C →ₗ[R] K)
    (hflat : b.comp r = η) :
    (eventSeamDefect a d b).comp r +
        b.comp (eventSeamDefect d p r) =
      eventSeamDefect a p η := by
  subst η
  ext x
  simp [eventSeamDefect]

/-- Covariantly constant component seams have a covariantly constant composite seam. -/
theorem eventSeam_comp_parallel
    (a : Module.End R K) (d : Module.End R I) (p : Module.End R C)
    (b : I →ₗ[R] K) (r : C →ₗ[R] I)
    (hb : eventSeamDefect a d b = 0)
    (hr : eventSeamDefect d p r = 0) :
    eventSeamDefect a p (b.comp r) = 0 := by
  have h := eventSeam_compose_of_triangle_flat a d p b r (b.comp r) rfl
  simpa [hb, hr] using h.symm

end SeamCurvature

end GaloisForLFunctions.HTGeometry
