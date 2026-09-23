import GaloisForLFunctions.RHTower.SelbergPositiveEisenstein
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinCuspJointSmooth
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualSignedFourierUniqueness
import GaloisForLFunctions.RHTower.SelbergMaassTraceEnergy

/-!
# Smooth planar realization of the literal positive Eisenstein series

Global Fourier uniqueness and full Fourier--Bessel smoothness identify the
original primitive-pair sum with a smooth planar function. Its actual first
and second Frechet derivatives agree with the original coordinate jets.
-/

open Set Filter Topology UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergEisensteinPlane
open _root_.RHTower SelbergPositiveEisenstein SelbergMaassTraceEnergy SelbergMaassMean SelbergEulerDecay
noncomputable section

/-- The nonzero completion coefficient of the actual positive Eisenstein function. -/
def completion : ℂ := reflectedCompletedLambda (2 * parameter.s)

/-- Both actual completion factors are nonzero in the convergence chamber. -/
theorem completion_ne_zero : completion ≠ 0 := by
  unfold completion reflectedCompletedLambda
  exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num [parameter]))
    (riemannZeta_ne_zero_of_one_lt_re (by norm_num [parameter]))

/-- A smooth planar representative of the literal positive Eisenstein series. -/
def planeE (z : ℂ) : ℝ :=
  (d4BMCompletedEisensteinCuspLeg .scalar (parameter.s - 1 / 2) z.re z.im / completion).re

/-- Actual Fourier uniqueness identifies the smooth representative with the original primitive-pair sum. -/
theorem planeE_eq (z : D4BMUpperHalfPlaneCoordinate) : planeE (point z.x z.y) = E z := by
  have h : completion * d4BMRawEisensteinPoincareSeries z parameter =
      d4BMCompletedEisensteinCuspLeg .scalar (parameter.s - 1 / 2) z.x z.y :=
    d4BM_actualCompletedPoincare_eq_canonicalCuspLeg z parameter z.x
  have hr : d4BMCompletedEisensteinCuspLeg .scalar (parameter.s - 1 / 2) z.x z.y / completion =
      d4BMRawEisensteinPoincareSeries z parameter := by
    rw [← h]
    field_simp [completion_ne_zero]
  simpa only [planeE, point, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, mul_zero, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, Complex.I_im, mul_one, zero_add, E] using congrArg Complex.re hr

/-- The literal Eisenstein series has all joint planar derivatives at positive height. -/
theorem planeE_contDiffOn : ContDiffOn ℝ ∞ planeE {z : ℂ | 0 < z.im} := by
  have hc : ContDiff ℝ ∞ (fun z : ℂ => ![z.re, z.im]) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact Complex.reCLM.contDiff
    · exact Complex.imCLM.contDiff
  have hs := (_root_.RHTower.D4BMAngularSeries.cuspLeg_contDiffOn .scalar (parameter.s - 1 / 2)).comp
    hc.contDiffOn (show Set.MapsTo (fun z : ℂ => ![z.re, z.im]) {z : ℂ | 0 < z.im}
      _root_.RHTower.D4BMAngularSeries.domain from fun z hz => hz)
  exact Complex.reCLM.contDiff.comp_contDiffOn (hs.div_const completion)

/-- The original positive source remains positive in the actual planar chart. -/
theorem planeE_pos {z : ℂ} (hz : 0 < z.im) : 0 < planeE z := by
  have hp : point z.re z.im = z := by apply Complex.ext <;> simp [point]
  rw [← hp, planeE_eq ⟨z.re, z.im, hz⟩]
  exact E_pos _

private theorem planeE_c2 {z : ℂ} (hz : 0 < z.im) : ContDiffAt ℝ 2 planeE z :=
  ((contDiffOn_infty.mp planeE_contDiffOn) 2).contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds hz)

/-- The actual horizontal source slice differentiates to the original real Eisenstein jet. -/
theorem planeE_horizontal (z : D4BMUpperHalfPlaneCoordinate) :
    HasDerivAt (fun x => planeE (point x z.y)) (Ex z) z.x := by
  have h := horizontal_derivative z
  convert h using 1
  funext x
  exact planeE_eq (d4BMHorizontalCoordinate z x)

/-- The actual vertical source slice differentiates to the original real Eisenstein jet. -/
theorem planeE_vertical (z : D4BMUpperHalfPlaneCoordinate) :
    HasDerivAt (fun y => planeE (point z.x y)) (Ey z) z.y := by
  apply (vertical_derivative z).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds z.y_pos] with y hy
  exact planeE_eq ⟨z.x, y, hy⟩

/-- The horizontal Frechet derivative is the original termwise-differentiated source sum. -/
theorem planeE_dir_one (z : D4BMUpperHalfPlaneCoordinate) : dir 1 planeE (point z.x z.y) = Ex z := by
  have hz : 0 < (point z.x z.y).im := by simpa [point] using z.y_pos
  have h := ((planeE_c2 hz).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt z.x (point_horizontal z.x z.y)
  exact h.unique (planeE_horizontal z)

/-- The vertical Frechet derivative is the original termwise-differentiated source sum. -/
theorem planeE_dir_I (z : D4BMUpperHalfPlaneCoordinate) : dir Complex.I planeE (point z.x z.y) = Ey z := by
  have hz : 0 < (point z.x z.y).im := by simpa [point] using z.y_pos
  have h := ((planeE_c2 hz).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt z.y (point_vertical z.x z.y)
  exact h.unique (planeE_vertical z)

/-- The actual horizontal second Frechet derivative is the original second jet. -/
theorem planeE_second_one (z : D4BMUpperHalfPlaneCoordinate) :
    dir 1 (dir 1 planeE) (point z.x z.y) = Exx z := by
  have hz : 0 < (point z.x z.y).im := by simpa [point] using z.y_pos
  have h := ((dir_contDiffAt (planeE_c2 hz) 1).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt z.x
    (point_horizontal z.x z.y)
  have hj : HasDerivAt (fun x => dir 1 planeE (point x z.y)) (Exx z) z.x := by
    convert horizontal_second_derivative z using 1
    funext x
    exact planeE_dir_one (d4BMHorizontalCoordinate z x)
  exact h.unique hj

/-- The actual vertical second Frechet derivative is the original second jet. -/
theorem planeE_second_I (z : D4BMUpperHalfPlaneCoordinate) :
    dir Complex.I (dir Complex.I planeE) (point z.x z.y) = Eyy z := by
  have hz : 0 < (point z.x z.y).im := by simpa [point] using z.y_pos
  have h := ((dir_contDiffAt (planeE_c2 hz) Complex.I).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt z.y
    (point_vertical z.x z.y)
  have hj : HasDerivAt (fun y => dir Complex.I planeE (point z.x y)) (Eyy z) z.y := by
    apply (vertical_second_derivative z).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds z.y_pos] with y hy
    exact planeE_dir_I ⟨z.x, y, hy⟩
  exact h.unique hj

/-- The literal planar Frechet Laplacian satisfies the original positive-sign eigen-equation. -/
theorem planeE_eigen_equation {z : ℂ} (hz : 0 < z.im) : z.im ^ (2 : ℕ) * realLaplacian planeE z = 2 * planeE z := by
  let w : D4BMUpperHalfPlaneCoordinate := ⟨z.re, z.im, hz⟩
  have hp : point w.x w.y = z := by apply Complex.ext <;> simp [point, w]
  have h := eigen_equation w
  rw [← planeE_second_one, ← planeE_second_I, ← planeE_eq, hp] at h
  exact h

end
end GaloisForLFunctions.RHTower.SelbergEisensteinPlane
