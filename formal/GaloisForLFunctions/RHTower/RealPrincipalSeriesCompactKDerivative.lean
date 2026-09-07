import GaloisForLFunctions.RHTower.RealPrincipalSeriesCompactHarishChandra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Infinitesimal compact rotation in the real principal series

This file differentiates the actual compact-picture action along the standard rotation subgroup
of `K`.  On every finite spherical K-type, pointwise differentiation at the identity is proved to
equal `i` times the transported Harish-Chandra weight operator.  Thus the compact weight operator
is identified with the derivative of genuine principal-series right translation, rather than only
being transported abstractly from the finite-support model.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Standard one-parameter rotation subgroup of the stabilizer `K` of `I`. -/
def realSphericalRotation (t : ℝ) : upperHalfPlaneStabilizer :=
  realCircleToSphericalK (Circle.exp t)

@[simp]
theorem realSphericalRotation_zero : realSphericalRotation 0 = 1 := by
  apply realSphericalKCircleEquiv.injective
  simp [realSphericalRotation, realSphericalKCircleEquiv]

theorem realSphericalRotation_add (t u : ℝ) :
    realSphericalRotation (t + u) = realSphericalRotation t * realSphericalRotation u := by
  apply realSphericalKCircleEquiv.injective
  simp [realSphericalRotation, Circle.exp_add, realSphericalKCircleEquiv]

@[simp]
theorem realSphericalRotation_phase (t : ℝ) :
    realSphericalKToCircle (realSphericalRotation t) = Circle.exp t := by
  simp [realSphericalRotation]

/-- A spherical K-type restricts to its expected exponential along the rotation subgroup. -/
theorem realSphericalKTypeCharacter_rotation (m : ℤ) (t : ℝ) :
    realSphericalKTypeCharacter m (realSphericalRotation t) =
      Complex.exp (((((2 * m : ℤ) : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
  change evenCircleCharacter m
      (realSphericalKToCircle (realCircleToSphericalK (Circle.exp t))) = _
  rw [realSphericalKToCircle_circleToSphericalK]
  change (((Circle.exp t : Circle) : ℂ) ^ (2 * m)) = _
  rw [← Circle.coe_zpow, ← Circle.exp_zsmul, Circle.coe_exp]
  simp only [zsmul_eq_mul]

/-- Smoothness along the rotation subgroup, sufficient for the compact infinitesimal action. -/
def IsRotationSmoothCompactVector {σ : ℝ} (φ : realCompactPictureSpace σ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => φ.1 (realSphericalRotation t))

theorem realCompactKType_isRotationSmooth (σ : ℝ) (m : ℤ) :
    IsRotationSmoothCompactVector (realCompactKType σ m) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ =>
    (realCompactKType σ m).1 (realSphericalRotation t))
  rw [show (fun t : ℝ =>
      (realCompactKType σ m).1 (realSphericalRotation t)) =
      (fun t : ℝ => Complex.exp
        (((((2 * m : ℤ) : ℝ) * t : ℝ) : ℂ) * Complex.I)) by
    funext t
    exact realSphericalKTypeCharacter_rotation m t]
  exact ((Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul contDiff_id)).mul contDiff_const).cexp

/-- Every finite Fourier vector is smooth along the compact rotation subgroup. -/
theorem realCompactKFiniteEmbedding_isRotationSmooth (σ : ℝ)
    (v : SphericalKFiniteModel) :
    IsRotationSmoothCompactVector (realCompactKFiniteEmbedding σ v) := by
  induction v using Finsupp.induction_linear with
  | zero =>
      change ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ => (0 : ℂ))
      exact contDiff_const
  | add v w hv hw =>
      change ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ =>
        (realCompactKFiniteEmbedding σ v).1 (realSphericalRotation t)) at hv
      change ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ =>
        (realCompactKFiniteEmbedding σ w).1 (realSphericalRotation t)) at hw
      change ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ =>
        (realCompactKFiniteEmbedding σ (v + w)).1 (realSphericalRotation t))
      simpa only [map_add, AddMemClass.coe_add, Pi.add_apply] using hv.add hw
  | single m z =>
      rw [realCompactKFiniteEmbedding_single]
      change ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => z *
        (realCompactKType σ m).1 (realSphericalRotation t))
      exact contDiff_const.mul (realCompactKType_isRotationSmooth σ m)

/-- Differential of the weight-`2m` character along the standard rotation subgroup. -/
theorem hasDerivAt_realSphericalKTypeCharacter_rotation (m : ℤ) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ => realSphericalKTypeCharacter m (realSphericalRotation u))
      (realSphericalKTypeCharacter m (realSphericalRotation t) *
        ((((2 * m : ℤ) : ℝ) : ℂ) * Complex.I)) t := by
  let a : ℝ := ((2 * m : ℤ) : ℝ)
  have hr : HasDerivAt (fun u : ℝ => a * u) a t := by
    simpa using (hasDerivAt_id t).const_mul a
  have hc : HasDerivAt (fun u : ℝ => ((a * u : ℝ) : ℂ)) (a : ℂ) t :=
    hr.ofReal_comp
  have hexp := (hc.mul_const Complex.I).cexp
  simpa only [realSphericalKTypeCharacter_rotation, a] using hexp

@[simp]
theorem compactRealPrincipalSeries_rotation_apply (σ : ℝ) (m : ℤ) (t : ℝ)
    (k : upperHalfPlaneStabilizer) :
    ((compactRealPrincipalSeries σ (realSphericalRotation t : SL2R))
        (realCompactKType σ m)).1 k =
      realSphericalKTypeCharacter m (realSphericalRotation t) *
        realSphericalKTypeCharacter m k := by
  rw [compactRealPrincipalSeries_KType_eigenvector]
  rfl

/-- Pointwise differential of actual compact-picture right translation on one K-type. -/
theorem hasDerivAt_compactRealPrincipalSeries_rotation (σ : ℝ) (m : ℤ) (z : ℂ)
    (k : upperHalfPlaneStabilizer) :
    HasDerivAt
      (fun t : ℝ =>
        ((compactRealPrincipalSeries σ (realSphericalRotation t : SL2R))
          (z • realCompactKType σ m)).1 k)
      (((((2 * m : ℤ) : ℝ) : ℂ) * Complex.I) *
        (z * realSphericalKTypeCharacter m k)) 0 := by
  have h := (hasDerivAt_realSphericalKTypeCharacter_rotation m 0).mul_const
    (z * realSphericalKTypeCharacter m k)
  rw [show (fun t : ℝ =>
      ((compactRealPrincipalSeries σ (realSphericalRotation t : SL2R))
        (z • realCompactKType σ m)).1 k) =
      (fun t : ℝ => realSphericalKTypeCharacter m (realSphericalRotation t) *
        (z * realSphericalKTypeCharacter m k)) by
    funext t
    rw [map_smul]
    change z *
        ((compactRealPrincipalSeries σ (realSphericalRotation t : SL2R))
          (realCompactKType σ m)).1 k = _
    rw [compactRealPrincipalSeries_rotation_apply]
    ring]
  have hzero : realSphericalKTypeCharacter m (realSphericalRotation 0) = 1 := by
    rw [realSphericalKTypeCharacter_rotation]
    norm_num
  rw [hzero, one_mul] at h
  exact h

/-- On each finite compact K-type, differentiated rotation is `iH` pointwise. -/
theorem compactRotation_hasDerivAt_eq_I_H_single (s : ℝ) (m : ℤ) (z : ℂ)
    (k : upperHalfPlaneStabilizer) :
    HasDerivAt
      (fun t : ℝ =>
        (compactRealPrincipalSeries (s - 1) (realSphericalRotation t : SL2R)
          (sphericalModelCompactKFiniteEquiv s (Finsupp.single m z))).1 k)
      (Complex.I *
        (compactSphericalPrincipalH s
          (sphericalModelCompactKFiniteEquiv s (Finsupp.single m z))).1.1 k) 0 := by
  rw [sphericalModelCompactKFiniteEquiv_apply_coe,
    realCompactKFiniteEmbedding_single]
  convert hasDerivAt_compactRealPrincipalSeries_rotation (s - 1) m z k using 1
  rw [compactSphericalPrincipalH_single,
    sphericalModelCompactKFiniteEquiv_single_apply]
  push_cast
  ring

end
end GaloisForLFunctions.RHTower
