import Mathlib

/-!
# Cyclic--paracyclic boundary-defect law

A cyclic source rotation squares to the identity, whereas a paracyclic target
rotation may square to scalar monodromy.  For an arbitrary linear landing, its
equivariance defect has an exact two-step factorization: the target monodromy
defect of the landing is the sum of two transported equivariance defects.

Consequently strict equivariance is not the only useful consumer.  It is
enough for the equivariance defect to land in a target-rotation-stable boundary
submodule, provided the landed atom survives modulo that boundary.  A retained
boundary class then forces trivial target monodromy.  Conversely, away from
trivial monodromy every strict cyclic-to-paracyclic landing is the zero map.

No topology, positivity, finite-dimensionality, or arithmetic hypothesis is
used.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

variable {S V : Type*}
variable [AddCommGroup S] [Module ℂ S]
variable [AddCommGroup V] [Module ℂ V]

/-- Failure of a landing to intertwine source and target rotations. -/
def cyclicParacyclicEquivarianceDefect
    (sourceRotate : S →ₗ[ℂ] S)
    (targetRotate : V →ₗ[ℂ] V)
    (land : S →ₗ[ℂ] V) : S →ₗ[ℂ] V :=
  targetRotate.comp land - land.comp sourceRotate

@[simp]
theorem cyclicParacyclicEquivarianceDefect_apply
    (sourceRotate : S →ₗ[ℂ] S)
    (targetRotate : V →ₗ[ℂ] V)
    (land : S →ₗ[ℂ] V) (x : S) :
    cyclicParacyclicEquivarianceDefect sourceRotate targetRotate land x =
      targetRotate (land x) - land (sourceRotate x) := by
  rfl

/--
**Two-step boundary-defect factorization.**  The difference between the two
rotation squares is exactly the sum of the equivariance defect transported
once on the target and once on the source.
-/
theorem cyclicParacyclicEquivarianceDefect_twoStep
    (sourceRotate : S →ₗ[ℂ] S)
    (targetRotate : V →ₗ[ℂ] V)
    (land : S →ₗ[ℂ] V) :
    targetRotate.comp
          (cyclicParacyclicEquivarianceDefect sourceRotate targetRotate land) +
        (cyclicParacyclicEquivarianceDefect sourceRotate targetRotate land).comp
          sourceRotate =
      (targetRotate.comp targetRotate).comp land -
        land.comp (sourceRotate.comp sourceRotate) := by
  ext x
  simp [cyclicParacyclicEquivarianceDefect]

/-- Pointwise form of the two-step boundary-defect factorization. -/
theorem cyclicParacyclicEquivarianceDefect_twoStep_apply
    (sourceRotate : S →ₗ[ℂ] S)
    (targetRotate : V →ₗ[ℂ] V)
    (land : S →ₗ[ℂ] V) (x : S) :
    targetRotate
          (cyclicParacyclicEquivarianceDefect sourceRotate targetRotate land x) +
        cyclicParacyclicEquivarianceDefect sourceRotate targetRotate land
          (sourceRotate x) =
      targetRotate (targetRotate (land x)) -
        land (sourceRotate (sourceRotate x)) := by
  exact LinearMap.congr_fun
    (cyclicParacyclicEquivarianceDefect_twoStep sourceRotate targetRotate land) x

/--
**Retained boundary-class rigidity.**  Strict equivariance may be weakened to
equivariance modulo a rotation-stable boundary submodule.  If one landed atom
is nonzero in the resulting quotient, target scalar monodromy is trivial.
-/
theorem retainedCyclicClass_forces_monodromy_one
    (sourceRotate : S →ₗ[ℂ] S)
    (targetRotate : V →ₗ[ℂ] V)
    (land : S →ₗ[ℂ] V)
    (boundary : Submodule ℂ V)
    (delta : ℂ)
    (hsource : ∀ x, sourceRotate (sourceRotate x) = x)
    (htarget : ∀ y, targetRotate (targetRotate y) = delta • y)
    (hboundary : ∀ y ∈ boundary, targetRotate y ∈ boundary)
    (hdefect : ∀ x,
      cyclicParacyclicEquivarianceDefect sourceRotate targetRotate land x ∈ boundary)
    {x : S} (hretained : land x ∉ boundary) :
    delta = 1 := by
  have hstep := cyclicParacyclicEquivarianceDefect_twoStep_apply
    sourceRotate targetRotate land x
  rw [hsource, htarget] at hstep
  have hmem : (delta - 1) • land x ∈ boundary := by
    rw [sub_smul, one_smul, ← hstep]
    exact boundary.add_mem
      (hboundary _ (hdefect x))
      (hdefect (sourceRotate x))
  by_contra hdelta
  have hsub : delta - 1 ≠ 0 := sub_ne_zero.mpr hdelta
  apply hretained
  have hinv : land x = (delta - 1)⁻¹ • ((delta - 1) • land x) := by
    rw [smul_smul, inv_mul_cancel₀ hsub, one_smul]
  rw [hinv]
  exact boundary.smul_mem _ hmem

/--
**Strict-operator obstruction.**  Away from trivial monodromy, every strict
single-valued cyclic-to-paracyclic linear landing is identically zero.  This
is algebraic, so unboundedness or a finer topology cannot evade it while the
landing remains a single-valued strict intertwiner on its source domain.
-/
theorem strictCyclicParacyclicLanding_eq_zero_of_monodromy_ne_one
    (sourceRotate : S →ₗ[ℂ] S)
    (targetRotate : V →ₗ[ℂ] V)
    (land : S →ₗ[ℂ] V)
    (delta : ℂ)
    (hsource : ∀ x, sourceRotate (sourceRotate x) = x)
    (htarget : ∀ y, targetRotate (targetRotate y) = delta • y)
    (hintertwine : targetRotate.comp land = land.comp sourceRotate)
    (hdelta : delta ≠ 1) :
    land = 0 := by
  apply LinearMap.ext
  intro x
  by_contra hx
  apply hdelta
  apply retainedCyclicClass_forces_monodromy_one
    sourceRotate targetRotate land ⊥ delta hsource htarget
  · simp
  · intro y
    have h := LinearMap.congr_fun hintertwine y
    change targetRotate (land y) = land (sourceRotate y) at h
    change targetRotate (land y) - land (sourceRotate y) ∈ (⊥ : Submodule ℂ V)
    rw [h, sub_self]
    exact Submodule.zero_mem _
  · simpa using hx

end GaloisForLFunctions.HTGeometry
