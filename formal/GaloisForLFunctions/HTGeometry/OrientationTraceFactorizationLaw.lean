import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Orientation--trace factorization

Suppose a top cochain has a Green decomposition

`boundary (lift z) + inclusion (trace z) = z`,

the trace kills boundaries, and the inclusion is a section of the trace.
Then every linear consumer which ignores boundaries factors uniquely through
the orientation trace.  Conversely, every trace factor ignores boundaries.

Thus the orientation trace is not merely one invariant: it is the complete
regular invariant of the contracted top source.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R A1 A2 O W : Type*}
variable [Field R]
variable [AddCommGroup A1] [Module R A1]
variable [AddCommGroup A2] [Module R A2]
variable [AddCommGroup O] [Module R O]
variable [AddCommGroup W] [Module R W]

/--
**Orientation--trace factorization law.**  A consumer annihilates every
boundary exactly when it factors uniquely through the orientation trace.
-/
theorem orientationTrace_factorization_unique_iff
    (boundary : A1 →ₗ[R] A2)
    (trace : A2 →ₗ[R] O)
    (inclusion : O →ₗ[R] A2)
    (lift : A2 →ₗ[R] A1)
    (hdecomposition :
      ∀ z, boundary (lift z) + inclusion (trace z) = z)
    (hboundary : ∀ x, trace (boundary x) = 0)
    (hsection : ∀ o, trace (inclusion o) = o)
    (F : A2 →ₗ[R] W) :
    (∀ x, F (boundary x) = 0) ↔
      ∃! phi : O →ₗ[R] W, F = phi.comp trace := by
  constructor
  · intro hF
    refine ⟨F.comp inclusion, ?_, ?_⟩
    · apply LinearMap.ext
      intro z
      have hz := congrArg F (hdecomposition z)
      rw [map_add, hF, zero_add] at hz
      simpa [LinearMap.comp_apply] using hz.symm
    · intro phi hphi
      apply LinearMap.ext
      intro o
      have ho := LinearMap.congr_fun hphi (inclusion o)
      simpa [LinearMap.comp_apply, hsection o] using ho.symm
  · rintro ⟨phi, hphi, -⟩
    intro x
    rw [LinearMap.congr_fun hphi (boundary x),
      LinearMap.comp_apply, hboundary x, map_zero]

/--
Information beyond the orientation trace is exactly boundary sensitivity.
There is no third regular channel.
-/
theorem orientationTrace_nonfactorization_iff_detects_boundary
    (boundary : A1 →ₗ[R] A2)
    (trace : A2 →ₗ[R] O)
    (inclusion : O →ₗ[R] A2)
    (lift : A2 →ₗ[R] A1)
    (hdecomposition :
      ∀ z, boundary (lift z) + inclusion (trace z) = z)
    (hboundary : ∀ x, trace (boundary x) = 0)
    (hsection : ∀ o, trace (inclusion o) = o)
    (F : A2 →ₗ[R] W) :
    (¬ ∃ phi : O →ₗ[R] W, F = phi.comp trace) ↔
      ∃ x, F (boundary x) ≠ 0 := by
  classical
  have hunique :=
    orientationTrace_factorization_unique_iff
      boundary trace inclusion lift
      hdecomposition hboundary hsection F
  constructor
  · intro hnon
    by_contra hdetect
    push Not at hdetect
    obtain ⟨phi, hphi, -⟩ := hunique.mp hdetect
    exact hnon ⟨phi, hphi⟩
  · rintro ⟨x, hx⟩ ⟨phi, hphi⟩
    have hzero :
        F (boundary x) = 0 := by
      rw [LinearMap.congr_fun hphi (boundary x),
        LinearMap.comp_apply, hboundary x, map_zero]
    exact hx hzero

end

end GaloisForLFunctions.HTGeometry
