import GaloisForLFunctions.HTGeometry.CyclicParacyclicBoundaryDefectLaw
import GaloisForLFunctions.RHTower.SourceDaggerCyclicMonodromyRigidity

/-!
# Source--dagger cyclic boundary-defect law

The strict source--dagger cyclic landing is stronger than necessary.  The
equivariance defect may be an exact boundary, provided the physical landed
atom remains nonzero modulo a target-rotation-stable boundary submodule.
The universal two-step defect factorization then forces the Deninger
half-density mate gain to be one on that retained class.

This file also records the complementary obstruction: at an off-critical
parameter every strict single-valued cyclic-to-source--dagger landing is the
zero map.  Finer topology, unboundedness, or nonclosability cannot evade this
algebraic conclusion while strict single-valued equivariance is retained.

The global theorem is a consumer.  It does not construct the arithmetic
boundary submodule, prove that the physical equivariance defect is a boundary,
or prove that the top conormal survives in the quotient.
-/

open Complex

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Complex-linear form of the normalized mixed source-inverse/analytic-dagger
degree-one rotation. -/
def sourceDaggerNormalizedDegreeOneRotationLinear
    (n : ℕ) (s : ℂ) : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) where
  toFun := sourceDaggerNormalizedDegreeOneRotation n s
  map_add' x y := by
    ext <;> simp [sourceDaggerNormalizedDegreeOneRotation, mul_add]
  map_smul' c x := by
    ext <;> simp [sourceDaggerNormalizedDegreeOneRotation]
    ring

@[simp]
theorem sourceDaggerNormalizedDegreeOneRotationLinear_apply
    (n : ℕ) (s : ℂ) (z : ℂ × ℂ) :
    sourceDaggerNormalizedDegreeOneRotationLinear n s z =
      sourceDaggerNormalizedDegreeOneRotation n s z :=
  rfl

/-- The linear mixed rotation has square equal to the half-density mate
gain. -/
theorem sourceDaggerNormalizedDegreeOneRotationLinear_sq
    (n : ℕ) (s : ℂ) (z : ℂ × ℂ) :
    sourceDaggerNormalizedDegreeOneRotationLinear n s
        (sourceDaggerNormalizedDegreeOneRotationLinear n s z) =
      (deningerHalfDensityMateGain n s : ℂ) • z := by
  exact sourceDaggerNormalizedDegreeOneRotation_sq n s z

/--
**Boundary-class source--dagger rigidity.**  It is enough for the mixed
equivariance defect to be an exact boundary.  A landed source atom that
survives modulo that stable boundary forces the critical half-density line.
-/
theorem re_eq_half_of_sourceDaggerCyclicBoundaryClass
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    (sourceRotate : S →ₗ[ℂ] S)
    (land : S →ₗ[ℂ] (ℂ × ℂ))
    (boundary : Submodule ℂ (ℂ × ℂ))
    {n : ℕ} (hn : 2 ≤ n) (s : ℂ)
    (hsource : ∀ x, sourceRotate (sourceRotate x) = x)
    (hboundary : ∀ z ∈ boundary,
      sourceDaggerNormalizedDegreeOneRotationLinear n s z ∈ boundary)
    (hdefect : ∀ x,
      cyclicParacyclicEquivarianceDefect sourceRotate
        (sourceDaggerNormalizedDegreeOneRotationLinear n s) land x ∈ boundary)
    {x : S} (hretained : land x ∉ boundary) :
    s.re = 1 / 2 := by
  have hgainC : (deningerHalfDensityMateGain n s : ℂ) = 1 :=
    retainedCyclicClass_forces_monodromy_one sourceRotate
      (sourceDaggerNormalizedDegreeOneRotationLinear n s) land boundary
      (deningerHalfDensityMateGain n s : ℂ) hsource
      (sourceDaggerNormalizedDegreeOneRotationLinear_sq n s)
      hboundary hdefect hretained
  have hgain : deningerHalfDensityMateGain n s = 1 := by
    exact_mod_cast hgainC
  rw [deningerHalfDensityMateGain] at hgain
  have hexp := (Real.exp_eq_one_iff _).mp hgain
  have hlog : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le one_lt_two hn)
  rcases mul_eq_zero.mp hexp with hre | hnlog
  · linarith
  · exact False.elim (ne_of_gt hlog hnlog)

/--
**Strict source--dagger operator obstruction.**  Off the critical line every
strict single-valued source-cyclic/analytic-paracyclic landing is zero on its
entire source domain.
-/
theorem sourceDaggerStrictCyclicLanding_eq_zero_of_re_ne_half
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    (sourceRotate : S →ₗ[ℂ] S)
    (land : S →ₗ[ℂ] (ℂ × ℂ))
    {n : ℕ} (hn : 2 ≤ n) (s : ℂ)
    (hsource : ∀ x, sourceRotate (sourceRotate x) = x)
    (hintertwine :
      (sourceDaggerNormalizedDegreeOneRotationLinear n s).comp land =
        land.comp sourceRotate)
    (hoffline : s.re ≠ 1 / 2) :
    land = 0 := by
  apply LinearMap.ext
  intro x
  by_contra hx
  apply hoffline
  apply re_eq_half_of_sourceDaggerCyclicBoundaryClass sourceRotate land ⊥ hn s hsource
  · simp [sourceDaggerNormalizedDegreeOneRotationLinear,
      sourceDaggerNormalizedDegreeOneRotation]
  · intro y
    have h := LinearMap.congr_fun hintertwine y
    change sourceDaggerNormalizedDegreeOneRotationLinear n s (land y) =
      land (sourceRotate y) at h
    change sourceDaggerNormalizedDegreeOneRotationLinear n s (land y) -
      land (sourceRotate y) ∈ (⊥ : Submodule ℂ (ℂ × ℂ))
    rw [h, sub_self]
    exact Submodule.zero_mem _
  · simpa using hx

/--
**RH from a retained source--dagger boundary class.**  On every Xi divisor
fibre, it suffices that the equivariance defect be a stable boundary and one
fixed source atom survive in the quotient.  Strict equivariance is not
assumed.
-/
theorem riemannHypothesis_of_sourceDaggerCyclicBoundaryClassLanding
    {S : Type*} [AddCommGroup S] [Module ℂ S]
    (sourceRotate : S →ₗ[ℂ] S) (atom : S) (n : ℕ) (hn : 2 ≤ n)
    (land : XiDivisorSupport → S →ₗ[ℂ] (ℂ × ℂ))
    (boundary : XiDivisorSupport → Submodule ℂ (ℂ × ℂ))
    (hsource : ∀ x, sourceRotate (sourceRotate x) = x)
    (hboundary : ∀ rho z, z ∈ boundary rho →
      sourceDaggerNormalizedDegreeOneRotationLinear n (rho : ℂ) z ∈ boundary rho)
    (hdefect : ∀ rho x,
      cyclicParacyclicEquivarianceDefect sourceRotate
        (sourceDaggerNormalizedDegreeOneRotationLinear n (rho : ℂ))
        (land rho) x ∈ boundary rho)
    (hretained : ∀ rho, land rho atom ∉ boundary rho) :
    RiemannHypothesis := by
  rw [← xiBoundaryCharacterNeutral_iff_riemannHypothesis]
  intro rho
  apply (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff (rho : ℂ)).2
  exact re_eq_half_of_sourceDaggerCyclicBoundaryClass sourceRotate
    (land rho) (boundary rho) hn (rho : ℂ) hsource
    (hboundary rho) (hdefect rho) (hretained rho)

end

end RHTower
