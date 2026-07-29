import Mathlib.Tactic

/-!
# Connection descent across a noninvertible event

Let `T : M → N` be a linear event map. Source and target endomorphisms are called parallel across
`T` when `B (T x) = T (A x)`. This file proves the pointwise algebra behind connection and
curvature descent:

* parallel transport preserves `ker T` and `range T`;
* commutators of parallel endomorphisms remain parallel;
* for the split event `K × I → C × I`, `(k, i) ↦ (0, i)`, the endomorphisms on `K` and `C`
  are completely independent while the endomorphism on `I` is transmitted;
* an invertible parallel bridge, unlike a noninvertible one, conjugates the full source
  endomorphism to the target.

These are unconditional linear-algebra statements. Endomorphism commutators are only the
pointwise algebraic skeleton of curvature. No connection on a manifold and no identification with
weak, colour, electromagnetic, or gravitational fields is assumed.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R M N K I C : Type*}
variable [CommRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup I] [Module R I]
variable [AddCommGroup C] [Module R C]

/-- Pointwise compatibility of source and target endomorphisms with an event map. -/
def EventParallel
    (T : M →ₗ[R] N) (A : Module.End R M) (B : Module.End R N) : Prop :=
  ∀ x, B (T x) = T (A x)

/-- A parallel event map makes its kernel invariant under the source endomorphism. -/
theorem EventParallel.mapsTo_ker
    {T : M →ₗ[R] N} {A : Module.End R M} {B : Module.End R N}
    (h : EventParallel T A B) {x : M} (hx : x ∈ LinearMap.ker T) :
    A x ∈ LinearMap.ker T := by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [← h x, hx, map_zero]

/-- A parallel event map makes its range invariant under the target endomorphism. -/
theorem EventParallel.mapsTo_range
    {T : M →ₗ[R] N} {A : Module.End R M} {B : Module.End R N}
    (h : EventParallel T A B) {y : N} (hy : y ∈ LinearMap.range T) :
    B y ∈ LinearMap.range T := by
  rcases hy with ⟨x, rfl⟩
  exact ⟨A x, (h x).symm⟩

/-- Commutator of two endomorphisms, the pointwise algebraic curvature bracket. -/
def endCommutator (A₁ A₂ : Module.End R M) : Module.End R M :=
  A₁.comp A₂ - A₂.comp A₁

/-- Curvature brackets continue to intertwine across a parallel event map. -/
theorem EventParallel.commutator
    {T : M →ₗ[R] N}
    {A₁ A₂ : Module.End R M} {B₁ B₂ : Module.End R N}
    (h₁ : EventParallel T A₁ B₁) (h₂ : EventParallel T A₂ B₂) :
    EventParallel T (endCommutator A₁ A₂) (endCommutator B₁ B₂) := by
  intro x
  simp only [endCommutator, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  rw [h₂ x, h₁ (A₂ x), h₁ x, h₂ (A₁ x)]

/-- Canonical split event: it kills the incoming sector and transmits the common sector. -/
def splitEventMap : (K × I) →ₗ[R] (C × I) where
  toFun x := (0, x.2)
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

/-- Block endomorphism on the source of the split event. -/
def splitSourceEnd
    (A_K : Module.End R K) (A_I : Module.End R I) :
    Module.End R (K × I) where
  toFun x := (A_K x.1, A_I x.2)
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

/-- Block endomorphism on the target of the split event. -/
def splitTargetEnd
    (B_C : Module.End R C) (A_I : Module.End R I) :
    Module.End R (C × I) where
  toFun x := (B_C x.1, A_I x.2)
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

/--
The split event is parallel for arbitrary kernel and cokernel endomorphisms; only the transmitted
endomorphism is shared.
-/
theorem splitEventMap_parallel
    (A_K : Module.End R K) (A_I : Module.End R I) (B_C : Module.End R C) :
    EventParallel (splitEventMap (R := R) (K := K) (I := I) (C := C))
      (splitSourceEnd A_K A_I) (splitTargetEnd B_C A_I) := by
  rintro ⟨k, i⟩
  ext <;> simp [splitEventMap, splitSourceEnd, splitTargetEnd]

/-- The killed sector is exactly the kernel of the split event. -/
theorem mem_splitEventMap_ker_iff (x : K × I) :
    x ∈ LinearMap.ker (splitEventMap (R := R) (K := K) (I := I) (C := C)) ↔
      x.2 = 0 := by
  rw [LinearMap.mem_ker]
  simp [splitEventMap]

/-- The transmitted sector is exactly the range of the split event. -/
theorem mem_splitEventMap_range_iff (y : C × I) :
    y ∈ LinearMap.range (splitEventMap (R := R) (K := K) (I := I) (C := C)) ↔
      y.1 = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    simpa [splitEventMap] using (congrArg Prod.fst hx).symm
  · intro hy
    refine ⟨(0, y.2), ?_⟩
    ext <;> simp [splitEventMap, hy]

/-- Canonical reporter from the split event's target to its outgoing sector. -/
def splitCokernelProjection : (C × I) →ₗ[R] C where
  toFun y := y.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Canonical zero-transmitted-sector representative of an outgoing class. -/
def splitCokernelSection : C →ₗ[R] (C × I) where
  toFun c := (c, 0)
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

/-- Projection onto the outgoing sector has the canonical section `(c, 0)`. -/
@[simp]
theorem splitCokernelProjection_section (c : C) :
    splitCokernelProjection (R := R) (I := I) (C := C)
        (splitCokernelSection (R := R) (I := I) (C := C) c) = c := by
  rfl

/-- Projection onto the outgoing sector is surjective. -/
theorem splitCokernelProjection_surjective :
    Function.Surjective (splitCokernelProjection (R := R) (I := I) (C := C)) := by
  intro c
  exact ⟨splitCokernelSection (R := R) (I := I) (C := C) c, rfl⟩

/--
The transmitted sector is exactly what the outgoing reporter erases. This is the algebraic
statement that makes the outgoing sector the canonical cokernel reporter, not a chosen
four-dimensional complement.
-/
theorem splitCokernelProjection_ker_eq_range :
    LinearMap.ker (splitCokernelProjection (R := R) (I := I) (C := C)) =
      LinearMap.range (splitEventMap (R := R) (K := K) (I := I) (C := C)) := by
  ext y
  rw [mem_splitEventMap_range_iff]
  simp [splitCokernelProjection]

/--
First-isomorphism realization of the split event's cokernel: target vectors modulo the
transmitted sector are canonically linearly equivalent to the outgoing sector.
-/
noncomputable def splitEventCokernelEquiv :
    ((C × I) ⧸ LinearMap.range
      (splitEventMap (R := R) (K := K) (I := I) (C := C))) ≃ₗ[R] C :=
  (Submodule.quotEquivOfEq _ _
    (splitCokernelProjection_ker_eq_range
      (R := R) (K := K) (I := I) (C := C)).symm).trans
    ((splitCokernelProjection (R := R) (I := I) (C := C)).quotKerEquivOfSurjective
      (splitCokernelProjection_surjective (R := R) (I := I) (C := C)))

/-- The canonical cokernel equivalence sends a target class to its outgoing component. -/
@[simp]
theorem splitEventCokernelEquiv_mk (y : C × I) :
    splitEventCokernelEquiv (R := R) (K := K) (I := I) (C := C)
        (Submodule.Quotient.mk y) = y.1 := by
  rfl

/--
Two target representatives determine the same outgoing event exactly when their difference was
transmitted by the incoming event.
-/
theorem splitCokernelProjection_eq_iff_sub_mem_range (y z : C × I) :
    splitCokernelProjection (R := R) (I := I) (C := C) y =
        splitCokernelProjection (R := R) (I := I) (C := C) z ↔
      y - z ∈ LinearMap.range
        (splitEventMap (R := R) (K := K) (I := I) (C := C)) := by
  rw [mem_splitEventMap_range_iff]
  simp [splitCokernelProjection, sub_eq_zero]

/--
An invertible parallel bridge locks the target endomorphism to the conjugate of the source
endomorphism.
-/
theorem parallel_equiv_forces_target
    (η : M ≃ₗ[R] N) (A : Module.End R M) (B : Module.End R N)
    (h : EventParallel η.toLinearMap A B) :
    B = η.toLinearMap.comp (A.comp η.symm.toLinearMap) := by
  ext y
  obtain ⟨x, rfl⟩ := η.surjective y
  simpa using h x

end GaloisForLFunctions.HTGeometry
