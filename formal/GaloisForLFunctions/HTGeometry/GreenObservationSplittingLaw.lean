import GaloisForLFunctions.HTGeometry.OrientationTraceFactorizationLaw

/-!
# Green primary--secondary observation law

Suppose a source admits a split Green identity

`boundary (lift z) + inclusion (trace z) = z`.

Then every linear observation has a canonical and unique decomposition into:

* a primary part carried by the absolute orientation trace; and
* a secondary part carried by the Green primitive of the boundary channel.

The secondary term vanishes exactly when the observer is boundary-blind,
hence exactly when it descends through the orientation trace.  This sharpens
orientation--trace factorization: every observer, not only a regular one, is
classified, and information beyond orientation is precisely a secondary
Green transgression.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R A1 A2 O W : Type*}
variable [Field R]
variable [AddCommGroup A1] [Module R A1]
variable [AddCommGroup A2] [Module R A2]
variable [AddCommGroup O] [Module R O]
variable [AddCommGroup W] [Module R W]

/-- Absolute primary observation obtained by compressing to orientation. -/
def greenObservationPrimary
    (trace : A2 →ₗ[R] O)
    (inclusion : O →ₗ[R] A2)
    (F : A2 →ₗ[R] W) :
    A2 →ₗ[R] W :=
  (F.comp inclusion).comp trace

/-- Relative secondary observation obtained by applying the observer to the
boundary of the canonical Green primitive. -/
def greenObservationSecondary
    (boundary : A1 →ₗ[R] A2)
    (lift : A2 →ₗ[R] A1)
    (F : A2 →ₗ[R] W) :
    A2 →ₗ[R] W :=
  (F.comp boundary).comp lift

/--
**Green primary--secondary splitting.** Every linear observer is exactly its
orientation compression plus its boundary Green transgression.
-/
theorem greenObservation_primary_add_secondary
    (boundary : A1 →ₗ[R] A2)
    (trace : A2 →ₗ[R] O)
    (inclusion : O →ₗ[R] A2)
    (lift : A2 →ₗ[R] A1)
    (hdecomposition :
      ∀ z, boundary (lift z) + inclusion (trace z) = z)
    (F : A2 →ₗ[R] W) :
    greenObservationPrimary trace inclusion F +
        greenObservationSecondary boundary lift F =
      F := by
  apply LinearMap.ext
  intro z
  simp only [greenObservationPrimary, greenObservationSecondary,
    LinearMap.add_apply, LinearMap.comp_apply]
  have hz := congrArg F (hdecomposition z)
  rw [map_add] at hz
  rw [add_comm]
  exact hz

/-- The primary observation annihilates every boundary. -/
theorem greenObservationPrimary_boundary
    (boundary : A1 →ₗ[R] A2)
    (trace : A2 →ₗ[R] O)
    (inclusion : O →ₗ[R] A2)
    (hboundary : ∀ x, trace (boundary x) = 0)
    (F : A2 →ₗ[R] W)
    (x : A1) :
    greenObservationPrimary trace inclusion F (boundary x) = 0 := by
  simp [greenObservationPrimary, hboundary]

/-- The secondary observation annihilates the absolute orientation
representatives. -/
theorem greenObservationSecondary_inclusion
    (boundary : A1 →ₗ[R] A2)
    (trace : A2 →ₗ[R] O)
    (inclusion : O →ₗ[R] A2)
    (lift : A2 →ₗ[R] A1)
    (hdecomposition :
      ∀ z, boundary (lift z) + inclusion (trace z) = z)
    (hsection : ∀ o, trace (inclusion o) = o)
    (F : A2 →ₗ[R] W)
    (o : O) :
    greenObservationSecondary boundary lift F (inclusion o) = 0 := by
  have ho := congrArg F (hdecomposition (inclusion o))
  rw [map_add, hsection] at ho
  have hb :
      F (boundary (lift (inclusion o))) = 0 :=
    add_eq_right.mp ho
  simpa [greenObservationSecondary] using hb

/--
The secondary transgression is zero exactly when the original observer is
boundary-blind.
-/
theorem greenObservationSecondary_eq_zero_iff_boundaryBlind
    (boundary : A1 →ₗ[R] A2)
    (trace : A2 →ₗ[R] O)
    (inclusion : O →ₗ[R] A2)
    (lift : A2 →ₗ[R] A1)
    (hdecomposition :
      ∀ z, boundary (lift z) + inclusion (trace z) = z)
    (hboundary : ∀ x, trace (boundary x) = 0)
    (F : A2 →ₗ[R] W) :
    greenObservationSecondary boundary lift F = 0 ↔
      ∀ x, F (boundary x) = 0 := by
  constructor
  · intro hzero x
    have hx := congrArg F (hdecomposition (boundary x))
    rw [map_add, hboundary, map_zero, map_zero, add_zero] at hx
    have hlift := LinearMap.congr_fun hzero (boundary x)
    simp only [greenObservationSecondary, LinearMap.comp_apply,
      LinearMap.zero_apply] at hlift
    exact hx.symm.trans hlift
  · intro hF
    apply LinearMap.ext
    intro z
    simp only [greenObservationSecondary, LinearMap.comp_apply,
      LinearMap.zero_apply]
    exact hF (lift z)

/--
The primary--secondary split is canonical.  If `F = P + S`, the proposed
primary part kills boundaries, and the proposed secondary part kills the
orientation inclusion, then both parts are forced to be the Green split.
-/
theorem greenObservation_primary_secondary_unique
    (boundary : A1 →ₗ[R] A2)
    (trace : A2 →ₗ[R] O)
    (inclusion : O →ₗ[R] A2)
    (lift : A2 →ₗ[R] A1)
    (hdecomposition :
      ∀ z, boundary (lift z) + inclusion (trace z) = z)
    (F P S : A2 →ₗ[R] W)
    (hF : P + S = F)
    (hP : ∀ x, P (boundary x) = 0)
    (hS : ∀ o, S (inclusion o) = 0) :
    P = greenObservationPrimary trace inclusion F ∧
      S = greenObservationSecondary boundary lift F := by
  have hP' : P = greenObservationPrimary trace inclusion F := by
    apply LinearMap.ext
    intro z
    have hz := congrArg P (hdecomposition z)
    rw [map_add, hP, zero_add] at hz
    have hFi := LinearMap.congr_fun hF (inclusion (trace z))
    rw [LinearMap.add_apply, hS, add_zero] at hFi
    simp only [greenObservationPrimary, LinearMap.comp_apply]
    exact hz.symm.trans hFi
  refine ⟨hP', ?_⟩
  apply LinearMap.ext
  intro z
  have hz := congrArg S (hdecomposition z)
  rw [map_add, hS, add_zero] at hz
  have hFb := LinearMap.congr_fun hF (boundary (lift z))
  rw [LinearMap.add_apply, hP, zero_add] at hFb
  simp only [greenObservationSecondary, LinearMap.comp_apply]
  exact hz.symm.trans hFb

/--
Complete classification: an observer descends uniquely through orientation
exactly when its secondary Green transgression vanishes.
-/
theorem greenObservation_traceFactorization_iff_secondary_eq_zero
    (boundary : A1 →ₗ[R] A2)
    (trace : A2 →ₗ[R] O)
    (inclusion : O →ₗ[R] A2)
    (lift : A2 →ₗ[R] A1)
    (hdecomposition :
      ∀ z, boundary (lift z) + inclusion (trace z) = z)
    (hboundary : ∀ x, trace (boundary x) = 0)
    (hsection : ∀ o, trace (inclusion o) = o)
    (F : A2 →ₗ[R] W) :
    greenObservationSecondary boundary lift F = 0 ↔
      ∃! phi : O →ₗ[R] W, F = phi.comp trace := by
  rw [greenObservationSecondary_eq_zero_iff_boundaryBlind
    boundary trace inclusion lift hdecomposition hboundary F]
  exact orientationTrace_factorization_unique_iff
    boundary trace inclusion lift hdecomposition hboundary hsection F

end

end GaloisForLFunctions.HTGeometry
