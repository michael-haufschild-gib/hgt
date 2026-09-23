import GaloisForLFunctions.RHTower.SelbergMaassTraceEnergy

/-!
# Actual Maass trace currents on the modular boundary

Differentiating the proved modular invariance of the finite congruence trace gives
its exact real differential transformation under each integral Möbius map. Radial
contraction reverses sign under inversion. On the unit circle this cancels the
oriented currents of the paired arcs; translation cancels the vertical-side currents.

The current and its second-derivative slices have the regularity needed for actual
finite interval integration. All regularity comes from the original C² Maass source.
-/

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open scoped MatrixGroups ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassTraceBoundary
open SelbergMaassCongruenceTrace SelbergMaassMean SelbergMaassTraceEnergy
noncomputable section

/-- The actual real differential of the finite trace evaluated on a complex coordinate direction. -/
def current (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (v : ℂ) (z : ℍ) : ℝ := fderiv ℝ (density N f ∘ ofComplex) (z : ℂ) v

/-- The original Möbius differential transports the actual trace current with its full reciprocal-square Jacobian. -/
theorem current_modular (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (A : SL2Z) (z : ℍ) (v : ℂ) :
    current N f v z = current N f ((1 / (denom A z) ^ (2 : ℕ)) * v) (A • z) := by
  let G : ℂ → ℂ := fun w => ((A • ofComplex w : ℍ) : ℂ)
  have hG : HasFDerivAt G (UpperHalfPlane.smulFDeriv (A : GL (Fin 2) ℝ) (z : ℂ)) (z : ℂ) :=
    (UpperHalfPlane.hasStrictFDerivAt_smul (A : GL (Fin 2) ℝ) z).hasFDerivAt
  have hF : DifferentiableAt ℝ (density N f ∘ ofComplex) (G (z : ℂ)) := by
    simpa only [G, ofComplex_apply] using
      ((density_contDiffOn N f).contDiffAt
        (isOpen_upperHalfPlaneSet.mem_nhds (A • z).im_pos)).differentiableAt (by norm_num)
  have he : (density N f ∘ ofComplex) ∘ G = density N f ∘ ofComplex := by
    funext w
    simp only [Function.comp_apply, G, ofComplex_apply, density_invariant]
  have hc := hF.hasFDerivAt.comp (z : ℂ) hG
  rw [he] at hc
  have h := congrArg (fun L => L v) hc.fderiv
  have hj : UpperHalfPlane.smulFDeriv (A : GL (Fin 2) ℝ) (z : ℂ) v =
      (1 / (denom A z) ^ (2 : ℕ)) * v := by
    simp [UpperHalfPlane.smulFDeriv, UpperHalfPlane.σ, mul_comm]
  simpa only [ContinuousLinearMap.comp_apply, G, ofComplex_apply, hj, current] using h

/-- The trace differential contracted with the original radial coordinate vector. -/
def radial (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (z : ℍ) : ℝ :=
  current N f (z : ℂ) z

/-- The actual radial current is the real-coordinate contraction of its horizontal and vertical currents. -/
theorem radial_components (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (z : ℍ) :
    radial N f z = z.re * current N f 1 z + z.im * current N f Complex.I z := by
  have he : (z : ℂ) = z.re • (1 : ℂ) + z.im • Complex.I := by
    change (z : ℂ) = (z : ℂ).re • (1 : ℂ) + (z : ℂ).im • Complex.I
    simpa only [Complex.real_smul, mul_one] using (z : ℂ).re_add_im.symm
  unfold radial current
  rw [he, map_add, map_smul, map_smul]
  rfl

/-- The actual radial trace current changes sign at the inverted upper-half-plane point. -/
theorem radial_inversion (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (z : ℍ) :
    radial N f z + radial N f (ModularGroup.S • z) = 0 := by
  have h := current_modular N f ModularGroup.S z (z : ℂ)
  have hv : (1 / (denom ModularGroup.S z) ^ (2 : ℕ)) * (z : ℂ) = -((ModularGroup.S • z : ℍ) : ℂ) := by
    simp only [UpperHalfPlane.modular_S_smul]
    simp [denom, ModularGroup.S, inv_neg]
    field_simp
  rw [hv] at h
  unfold current at h
  rw [map_neg] at h
  change radial N f z = -radial N f (ModularGroup.S • z) at h
  linarith

/-- Unit modular translation preserves every actual trace differential direction. -/
theorem current_translation (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (z : ℍ) (v : ℂ) :
    current N f v (ModularGroup.T • z) = current N f v z := by
  have h := current_modular N f ModularGroup.T z v
  simpa [denom, ModularGroup.T] using h.symm

/-- Integral inversion pairs the opposite horizontal points on the upper unit circle. -/
theorem inversion_on_unit_circle {x y : ℝ} (hy : 0 < y) (hxy : x ^ (2 : ℕ) + y ^ (2 : ℕ) = 1) :
    ModularGroup.S • ofComplex (point x y) = ofComplex (point (-x) y) := by
  have hp : 0 < (point x y).im := by simpa [point] using hy
  have hn : 0 < (point (-x) y).im := by simpa [point] using hy
  apply UpperHalfPlane.ext
  rw [modular_S_smul, ofComplex_apply_of_im_pos hn]
  change (-(ofComplex (point x y) : ℂ))⁻¹ = point (-x) y
  rw [ofComplex_apply_of_im_pos hp, inv_neg, Complex.inv_def]
  have hs : Complex.normSq (point x y) = 1 := by
    simpa only [point, Complex.normSq_add_mul_I] using hxy
  rw [hs]
  simp [point, map_add, map_mul]
  ring

/-- The two literal oriented unit-circle boundary currents cancel with their actual Jacobian factor. -/
theorem arc_current_cancellation (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {x y : ℝ} (hy : 0 < y) (hxy : x ^ (2 : ℕ) + y ^ (2 : ℕ) = 1) :
    (x / y) * (current N f 1 (ofComplex (point (-x) y)) - current N f 1 (ofComplex (point x y))) -
      current N f Complex.I (ofComplex (point (-x) y)) - current N f Complex.I (ofComplex (point x y)) = 0 := by
  have h := radial_inversion N f (ofComplex (point x y))
  rw [inversion_on_unit_circle hy hxy, radial_components, radial_components] at h
  have hr (u : ℝ) : (ofComplex (point u y)).re = u := by
    change (ofComplex (point u y) : ℂ).re = u
    rw [ofComplex_apply_of_im_pos (by simpa [point] using hy)]
    simp [point]
  have hi (u : ℝ) : (ofComplex (point u y)).im = y := by
    change (ofComplex (point u y) : ℂ).im = y
    rw [ofComplex_apply_of_im_pos (by simpa [point] using hy)]
    simp [point]
  rw [hr, hr, hi, hi] at h
  field_simp
  linear_combination -h

/-- The integral translation matrix gives literal unit translation of the chart coordinate. -/
theorem translation_point (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ModularGroup.T • ofComplex (point x y) = ofComplex (point (x + 1) y) := by
  apply UpperHalfPlane.ext
  rw [modular_T_smul]
  have hp : 0 < (point x y).im := by simpa [point] using hy
  have hq : 0 < (point (x + 1) y).im := by simpa [point] using hy
  rw [UpperHalfPlane.coe_vadd, ofComplex_apply_of_im_pos hp, ofComplex_apply_of_im_pos hq]
  simp [point]
  ring

/-- Every actual trace current slice has horizontal period one. -/
theorem current_slice_periodic (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (v : ℂ) {y : ℝ} (hy : 0 < y) :
    Function.Periodic (fun x => current N f v (ofComplex (point x y))) 1 := by
  intro x
  change current N f v (ofComplex (point (x + 1) y)) = current N f v (ofComplex (point x y))
  rw [← translation_point x hy]
  exact current_translation N f (ofComplex (point x y)) v

/-- The actual horizontal currents agree on the paired vertical sides of the modular strip. -/
theorem side_current_cancellation (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    current N f 1 (ofComplex (point (1 / 2) y)) = current N f 1 (ofComplex (point (-(1 / 2)) y)) := by
  have h := current_slice_periodic N f 1 hy (-(1 / 2))
  change current N f 1 (ofComplex (point (-(1 / 2) + 1) y)) = _ at h
  rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring] at h
  exact h

/-- The actual trace current in real horizontal and height coordinates. -/
def currentAt (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (v : ℂ) (x y : ℝ) : ℝ := dir v (density N f ∘ ofComplex) (point x y)

/-- At positive height the real-coordinate current is the upper-half-plane differential. -/
theorem currentAt_eq_current (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (v : ℂ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    currentAt N f v x y = current N f v (ofComplex (point x y)) := by
  unfold currentAt current dir
  rw [ofComplex_apply_of_im_pos (by simpa [point] using hy)]

/-- The real-coordinate current has period one at every positive height. -/
theorem currentAt_periodic (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (v : ℂ) {y : ℝ} (hy : 0 < y) : Function.Periodic (fun x => currentAt N f v x y) 1 := by
  intro x
  simp only [currentAt_eq_current N f v _ hy]
  exact current_slice_periodic N f v hy x

/-- The exact paired unit-circle current cancellation in the coordinates used for integration. -/
theorem currentAt_arc_cancellation (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {x y : ℝ} (hy : 0 < y) (hxy : x ^ (2 : ℕ) + y ^ (2 : ℕ) = 1) :
    (x / y) * (currentAt N f 1 (-x) y - currentAt N f 1 x y) -
      currentAt N f Complex.I (-x) y - currentAt N f Complex.I x y = 0 := by
  simp only [currentAt_eq_current N f _ _ hy]
  exact arc_current_cancellation N f hy hxy

/-- The actual paired vertical-side currents cancel in integration coordinates. -/
theorem currentAt_side_cancellation (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) : currentAt N f 1 (1 / 2) y = currentAt N f 1 (-(1 / 2)) y := by
  simp only [currentAt_eq_current N f _ _ hy]
  exact side_current_cancellation N f hy

/-- The actual vertical derivative of each trace current slice is its second chart derivative. -/
theorem currentAt_vertical (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (v : ℂ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (currentAt N f v x)
      (dir Complex.I (dir v (density N f ∘ ofComplex)) (point x y)) y := by
  have hp : 0 < (point x y).im := by simpa [point] using hy
  exact (((trace_dir_contDiffOn N f v).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds hp)).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
      y (point_vertical x y)

/-- The actual horizontal derivative of each trace current slice is its second chart derivative. -/
theorem currentAt_horizontal (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (v : ℂ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun t => currentAt N f v t y)
      (dir 1 (dir v (density N f ∘ ofComplex)) (point x y)) x := by
  have hp : 0 < (point x y).im := by simpa [point] using hy
  exact (((trace_dir_contDiffOn N f v).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds hp)).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
      x (point_horizontal x y)

/-- Every actual current has a continuous horizontal slice. -/
theorem currentAt_horizontal_continuous (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (v : ℂ) {y : ℝ} (hy : 0 < y) : Continuous (fun x => currentAt N f v x y) :=
  continuous_iff_continuousAt.mpr (fun x => (currentAt_horizontal N f v hy x).continuousAt)

/-- Every second current derivative has continuous positive-height slices. -/
theorem second_current_vertical_continuousOn (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (v w : ℂ) (x : ℝ) :
    ContinuousOn (fun y => dir v (dir w (density N f ∘ ofComplex)) (point x y)) (Ioi 0) := by
  intro y hy
  have hp : 0 < (point x y).im := by simpa [point] using hy
  exact (((trace_second_dir_continuousOn N f v w).continuousAt
    (isOpen_upperHalfPlaneSet.mem_nhds hp)).comp (point_vertical x y).continuousAt).continuousWithinAt

/-- Every second current derivative has continuous horizontal slices. -/
theorem second_current_horizontal_continuous (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (v w : ℂ) {y : ℝ} (hy : 0 < y) :
    Continuous (fun x => dir v (dir w (density N f ∘ ofComplex)) (point x y)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hp : 0 < (point x y).im := by simpa [point] using hy
  exact ((trace_second_dir_continuousOn N f v w).continuousAt
    (isOpen_upperHalfPlaneSet.mem_nhds hp)).comp (f := fun t : ℝ => point t y) (point_horizontal x y).continuousAt

end
end GaloisForLFunctions.RHTower.SelbergMaassTraceBoundary
