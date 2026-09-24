import GaloisForLFunctions.RHTower.HyperbolicPointPair

/-!
# The power eigenfunction and the Selberg transform at `i`

`(Im z)^s` is real-`C²` on `ℍ` with positive hyperbolic Laplacian eigenvalue `s(1-s)`. With the
point-pair principle this yields `∫ φ G = G(i)·∫ φ·(Im)^s` for every eigenfunction `G` with
eigenvalue `s(1-s)` and every rotation-invariant kernel `φ`: the Selberg transform of `φ` at `s`.
-/

open Complex Set Filter Topology UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.HyperbolicPowerEigen
open HyperbolicRotationMean HyperbolicPointPair MeasureTheory
noncomputable section

/-- The power eigenfunction `(Im z)^s`. -/
def powerEigen (s : ℂ) (z : ℍ) : ℂ := ((z.im : ℝ) : ℂ) ^ s

/-- The real-linear map `u ↦ (Im u : ℂ)`. -/
def imC : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.imCLM

theorem imC_apply (u : ℂ) : imC u = (u.im : ℂ) := rfl

theorem chart_eq (s : ℂ) {w : ℂ} (hw : 0 < w.im) :
    (powerEigen s ∘ ofComplex) =ᶠ[𝓝 w] fun u => (imC u) ^ s := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hw] with u hu
  simp [powerEigen, Function.comp_apply, ofComplex_apply_of_im_pos hu, imC_apply]

theorem slit {u : ℂ} (hu : 0 < u.im) : imC u ∈ Complex.slitPlane := by
  rw [imC_apply]; exact Complex.ofReal_mem_slitPlane.mpr hu

/-- Real derivative of `u ↦ (Im u)^c` scaled by a constant. -/
theorem hasFDerivAt_pow (c a : ℂ) {u : ℂ} (hu : 0 < u.im) :
    HasFDerivAt (fun v => a * (imC v) ^ c)
      ((a * (c * (imC u) ^ (c - 1))) • imC) u := by
  have hQ : HasDerivAt (fun z : ℂ => a * z ^ c) (a * (c * (imC u) ^ (c - 1) * 1)) (imC u) :=
    ((hasDerivAt_id _).cpow_const (slit hu)).const_mul a
  have h : HasFDerivAt (fun v => a * (imC v) ^ c) _ u :=
    (hQ.hasFDerivAt.restrictScalars ℝ).comp u imC.hasFDerivAt
  refine h.congr_fderiv ?_
  ext v
  simp [mul_comm, mul_left_comm]

theorem fderiv_pow_apply (c a : ℂ) {u : ℂ} (hu : 0 < u.im) (v : ℂ) :
    fderiv ℝ (fun v => a * (imC v) ^ c) u v = a * (c * (imC u) ^ (c - 1)) * (v.im : ℂ) := by
  rw [(hasFDerivAt_pow c a hu).fderiv]
  simp [imC_apply]

theorem powerEigen_smooth (s : ℂ) : IsRealSmoothUpperHalfPlane (powerEigen s) := by
  intro w hw
  have hQ : ContDiffAt ℂ 2 (fun z : ℂ => z ^ s) (imC w) :=
    ((analyticAt_id.cpow analyticAt_const (slit hw)).contDiffAt)
  have h := (hQ.restrict_scalars ℝ).comp w imC.contDiff.contDiffAt
  exact (h.congr_of_eventuallyEq (chart_eq s hw)).contDiffWithinAt

/-- `(Im z)^s` is an eigenfunction of the positive hyperbolic Laplacian with eigenvalue `s(1-s)`. -/
theorem powerEigen_laplacian (s : ℂ) (z : ℍ) :
    positiveHyperbolicLaplacian (powerEigen s) z = s * (1 - s) * powerEigen s z := by
  have hw : 0 < (z : ℂ).im := z.im_pos
  have hfirst : ∀ v : ℂ, (fun u => fderiv ℝ (powerEigen s ∘ ofComplex) u v) =ᶠ[𝓝 (z : ℂ)]
      fun u => ((v.im : ℂ) * s) * (imC u) ^ (s - 1) := by
    intro v
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hw] with u hu
    rw [((chart_eq s hu).fderiv_eq)]
    have := fderiv_pow_apply s 1 hu v
    simp only [one_mul] at this
    rw [this]
    ring
  have h1 : fderiv ℝ (fun u => fderiv ℝ (powerEigen s ∘ ofComplex) u 1) (z : ℂ) 1 = 0 := by
    rw [(hfirst 1).fderiv_eq]
    simp
  have hI : fderiv ℝ (fun u => fderiv ℝ (powerEigen s ∘ ofComplex) u Complex.I) (z : ℂ) Complex.I =
      s * (s - 1) * (imC z) ^ (s - 1 - 1) := by
    rw [(hfirst Complex.I).fderiv_eq, fderiv_pow_apply (s - 1) _ hw Complex.I]
    simp
    ring
  have hy : (imC z) = ((z.im : ℝ) : ℂ) := rfl
  have hy0 : ((z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast z.im_pos.ne'
  unfold positiveHyperbolicLaplacian
  rw [h1, hI, hy]
  simp only [powerEigen]
  have hp : ((z.im : ℝ) : ℂ) ^ (s - 1 - 1) * ((z.im : ℝ) : ℂ) ^ (2 : ℕ) = ((z.im : ℝ) : ℂ) ^ s := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hy0]
    congr 1
    push_cast
    ring
  rw [← hp]
  simp only [UpperHalfPlane.im]
  ring

theorem powerEigen_I (s : ℂ) : powerEigen s UpperHalfPlane.I = 1 := by
  simp [powerEigen]

/-- **Selberg transform at `i`.** For every real-`C²` eigenfunction `G` of the positive hyperbolic
Laplacian with eigenvalue `s(1-s)` and every rotation-invariant kernel `φ`,
`∫ φ G = G(i) · ∫ φ (Im)^s`. The scalar `∫ φ (Im)^s` depends only on `φ` and `s`. -/
theorem integral_kernel_eq_selbergTransform {φ G : ℍ → ℂ} {s : ℂ}
    (hφ : ∀ θ w, φ (rot θ • w) = φ w) (hφm : AEStronglyMeasurable φ volume)
    (hG : IsRealSmoothUpperHalfPlane G)
    (hGe : ∀ z, positiveHyperbolicLaplacian G z = s * (1 - s) * G z)
    (hiG : Integrable (fun w => φ w * G w)) (hiE : Integrable (fun w => φ w * powerEigen s w)) :
    (∫ w, φ w * G w) = G UpperHalfPlane.I * ∫ w, φ w * powerEigen s w := by
  have h := integral_kernel_eigen hφ hφm hG hGe (powerEigen_smooth s) (powerEigen_laplacian s)
    (by rw [powerEigen_I]; exact one_ne_zero) hiG hiE
  rw [h, powerEigen_I, div_one]

end
end GaloisForLFunctions.RHTower.HyperbolicPowerEigen
