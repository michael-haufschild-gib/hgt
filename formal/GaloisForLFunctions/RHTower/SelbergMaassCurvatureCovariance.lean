import GaloisForLFunctions.RHTower.SelbergMaassWeakCurvature
import GaloisForLFunctions.RHTower.SelbergMaassCuspTransport

/-!
# Modular covariance of actual regularized Maass curvature

Complexification transfers the existing real C² Möbius Laplacian covariance to
the actual regularized trace radius. Its source curvature identity then proves
invariance of the full density relative to hyperbolic volume, with the nodal
regularization term retained. No additional smoothness or spectral bound is used.
-/

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open scoped MatrixGroups ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassCurvatureCovariance
open SelbergMaassCongruenceTrace SelbergMaassTraceEnergy SelbergMaassTraceRegularized
  SelbergMaassWeakCurvature SelbergMaassCuspTransport
open GaloisForLFunctions.HTGeometry.ComplexC2Laplacian (laplacian)
open SelbergMaassTraceEnergy (dir)
noncomputable section

private theorem dir_ofReal {F : ℂ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ F z) (v : ℂ) :
    dir v (fun w => (F w : ℂ)) z = (dir (E := ℝ) v F z : ℂ) := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp z hf.hasFDerivAt
  exact congrArg (fun L => L v) h.fderiv

private theorem second_dir_ofReal {F : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 F z) (v : ℂ) :
    dir v (dir v (fun w => (F w : ℂ))) z = (dir (E := ℝ) v (dir (E := ℝ) v F) z : ℂ) := by
  have he : dir v (fun w => (F w : ℂ)) =ᶠ[𝓝 z] (fun w => (dir (E := ℝ) v F w : ℂ)) := by
    filter_upwards [hf.eventually (by norm_num)] with w hw
    exact dir_ofReal (hw.differentiableAt (by norm_num)) v
  change fderiv ℝ (dir v (fun w => (F w : ℂ))) z v = _
  rw [he.fderiv_eq]
  exact dir_ofReal ((dir_contDiffAt hf v).differentiableAt (by norm_num)) v

/-- Complexification commutes with the actual real C² planar Laplacian. -/
theorem laplacian_ofReal {F : ℂ → ℝ} {z : ℂ} (hf : ContDiffAt ℝ 2 F z) :
    laplacian (fun w => (F w : ℂ)) z = (realLaplacian F z : ℂ) := by
  change dir 1 (dir 1 (fun w => (F w : ℂ))) z +
    dir Complex.I (dir Complex.I (fun w => (F w : ℂ))) z = _
  rw [second_dir_ofReal hf, second_dir_ofReal hf, realLaplacian, Complex.ofReal_add]

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

private theorem radius_chart (e : Ioi (0 : ℝ)) :
    (fun w : ℍ => (radius N f e (w : ℂ) : ℂ)) ∘ ofComplex =
      (fun w : ℂ => (radius N f e w : ℂ)) := by
  funext w
  simp only [Function.comp_apply, radius, ofComplex_apply]

private theorem complex_radius_smooth (e : Ioi (0 : ℝ)) :
    IsRealSmoothUpperHalfPlane (fun w : ℍ => (radius N f e (w : ℂ) : ℂ)) := by
  unfold IsRealSmoothUpperHalfPlane
  rw [radius_chart]
  exact Complex.ofRealCLM.contDiff.fun_comp_contDiffOn (radius_contDiffOn N f e)

private theorem complex_radius_laplacian (e : Ioi (0 : ℝ)) (z : ℍ) :
    positiveHyperbolicLaplacian (fun w : ℍ => (radius N f e (w : ℂ) : ℂ)) z =
      (-(z.im ^ (2 : ℕ) * realLaplacian (radius N f e) (z : ℂ)) : ℝ) := by
  change -(z.im : ℂ) ^ (2 : ℕ) * laplacian
    ((fun w : ℍ => (radius N f e (w : ℂ) : ℂ)) ∘ ofComplex) (z : ℂ) = _
  rw [radius_chart, laplacian_ofReal ((radius_contDiffOn N f e).contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos))]
  simp only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_pow, neg_mul]

/-- The actual regularized radius has an invariant hyperbolic Laplacian. -/
theorem radius_hyperbolic_laplacian_invariant (e : Ioi (0 : ℝ)) (A : SL2Z) (z : ℍ) :
    (A • z : ℍ).im ^ (2 : ℕ) * realLaplacian (radius N f e) (A • z : ℍ) =
      z.im ^ (2 : ℕ) * realLaplacian (radius N f e) (z : ℂ) := by
  have h := positive_laplacian_pullback A
    (fun w : ℍ => (radius N f e (w : ℂ) : ℂ)) (complex_radius_smooth N f e) z
  have he : (fun w : ℍ => (radius N f e (A • w : ℍ) : ℂ)) =
      (fun w : ℍ => (radius N f e (w : ℂ) : ℂ)) := by
    funext w
    rw [radius_invariant]
  rw [he, complex_radius_laplacian, complex_radius_laplacian] at h
  exact neg_injective (Complex.ofReal_injective h.symm)

/-- The actual regularized curvature density relative to hyperbolic volume. -/
def hyperbolicCurvature (e : Ioi (0 : ℝ)) (z : ℍ) : ℝ :=
  z.im ^ (2 : ℕ) * curvatureWeight N f e (z : ℂ)

/-- The full retained hyperbolic curvature has the exact source decomposition. -/
theorem hyperbolicCurvature_eq (e : Ioi (0 : ℝ)) (z : ℍ) :
    hyperbolicCurvature N f e z =
      z.im ^ (2 : ℕ) * realLaplacian (radius N f e) (z : ℂ) +
        lam * density N f z / radius N f e (z : ℂ) := by
  rw [hyperbolicCurvature, curvatureWeight_eq N f e z.im_pos]
  simp only [massWeight, ofComplex_apply, UpperHalfPlane.coe_im]
  field_simp [ne_of_gt z.im_pos, (radius_pos N f e (z : ℂ)).ne']

/-- Every actual regularized hyperbolic curvature density is modular invariant. -/
theorem hyperbolicCurvature_invariant (e : Ioi (0 : ℝ)) (A : SL2Z) (z : ℍ) :
    hyperbolicCurvature N f e (A • z) = hyperbolicCurvature N f e z := by
  rw [hyperbolicCurvature_eq, hyperbolicCurvature_eq,
    radius_hyperbolic_laplacian_invariant, density_invariant, radius_invariant]

end
end GaloisForLFunctions.RHTower.SelbergMaassCurvatureCovariance
