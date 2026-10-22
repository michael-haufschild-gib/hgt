import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspMeanLaplacian
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspIndicialSelection

/-!
# The actual global response mean solves the complete forced cusp equation.

The field is the original native energy response. Its identification with
continued retarded propagation and any extinction law remain separate.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff MatrixGroups
namespace RHTower.D4BMCuspResponse
open D4BMModularCore D4BMCuspProjection D4BMGlobalAngularResponse
noncomputable section

/-- The planar field is the actual globally smooth representative of the native response. -/
def responsePlanar (q : XiZeroCopy) (branch : Bool) : ℂ → ℂ := globalResponse q branch ∘ ofComplex

/-- The actual response's width-one cusp coefficient. -/
def responseMean (q : XiZeroCopy) (branch : Bool) : ℝ → ℂ := average (responsePlanar q branch)

/-- The actual response inherits full positive-height chart smoothness. -/
theorem responsePlanar_smooth (q : XiZeroCopy) (branch : Bool) :
    ContDiffOn ℝ ∞ (responsePlanar q branch) {z : ℂ | 0 < z.im} :=
  (globalResponse_smooth q branch).planar_contDiffOn

/-- The original modular translation gives periodicity of the actual response at every positive height. -/
theorem responsePlanar_periodic (q : XiZeroCopy) (branch : Bool) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    responsePlanar q branch (point (x+1) y) = responsePlanar q branch (point x y) := by
  have hpos (t : ℝ) : 0 < (point t y).im := by simpa [point] using hy
  have ht : ofComplex (point (x+1) y) = T • ofComplex (point x y) := by
    rw [ofComplex_apply_of_im_pos (hpos x),ofComplex_apply_of_im_pos (hpos (x+1))]
    apply UpperHalfPlane.ext_re_im
    · rw [ModularGroup.re_T_smul]
      simp [point]
    · rw [ModularGroup.im_T_smul]
      simp [point]
  have h := globalResponse_invariant q branch (QuotientGroup.mk T) (ofComplex (point x y))
  simpa only [responsePlanar,Function.comp_apply,ht,PSL2Z_mk_smul] using h

/-- Averaging the original global classical equation gives the actual forced cusp ODE. -/
theorem responseMean_global_equation (q : XiZeroCopy) (branch : Bool) {y : ℝ} (hy : 0 < y) :
    (y:ℂ)^(2 : ℕ)*deriv (deriv (responseMean q branch)) y-
      parameter q branch*responseMean q branch y =
        average (globalForcing q branch ∘ ofComplex) y := by
  have hf := responsePlanar_smooth q branch
  have hg := (globalForcing_smooth q branch).planar_contDiffOn
  have hL := average_laplacian (responsePlanar q branch) hf hy (responsePlanar_periodic q branch hy)
  have hi1 : IntegrableOn (fun x => parameter q branch*responsePlanar q branch (point x y))
      (Ioc (-1/2:ℝ) (1/2)) :=
    ((slice_continuous (responsePlanar q branch) hf hy).const_mul _).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hi2 : IntegrableOn (fun x => (globalForcing q branch ∘ ofComplex) (point x y))
      (Ioc (-1/2:ℝ) (1/2)) :=
    (slice_continuous _ hg hy).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have he : average (planarLaplacian (responsePlanar q branch)) y =
      (parameter q branch*responseMean q branch y+average (globalForcing q branch ∘ ofComplex) y)/(y:ℂ)^(2 : ℕ) := by
    unfold average mean
    calc
      (∫ x in Ioc (-1/2:ℝ) (1/2), planarLaplacian (responsePlanar q branch) (point x y)) =
          ∫ x in Ioc (-1/2:ℝ) (1/2),
            (parameter q branch*responsePlanar q branch (point x y)+
              (globalForcing q branch ∘ ofComplex) (point x y))/(y:ℂ)^(2 : ℕ) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        simpa only [responsePlanar,Function.comp_apply,point,Complex.add_im,
          Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add] using
          globalResponse_classical_planar q branch (point x y) (by simpa [point] using hy)
      _ = _ := by rw [integral_div,integral_add hi1 hi2,integral_const_mul]; rfl
  rw [hL] at he
  change deriv (deriv (responseMean q branch)) y = _ at he
  rw [he]
  field_simp [Complex.ofReal_ne_zero.mpr hy.ne']
  ring

private theorem point_mem_fd (x : ℝ) {y : ℝ} (hy : 2 < y) (hx : x ∈ Ioc (-1/2:ℝ) (1/2)) :
    ofComplex (point x y) ∈ fd := by
  have hp : 0 < (point x y).im := by simp [point]; linarith
  rw [ofComplex_apply_of_im_pos hp]
  constructor
  · simp [point,Complex.normSq_apply]
    nlinarith [sq_nonneg x]
  · simpa [point] using abs_le.mpr ⟨by simpa only [neg_div] using hx.1.le,hx.2⟩

/-- Inside the literal cusp rectangle, the global source mean is the original forcing's full mean. -/
theorem globalForcing_average (q : XiZeroCopy) (branch : Bool) {y : ℝ} (hy : 2 < y) :
    average (globalForcing q branch ∘ ofComplex) y = mean (fun x => forcing q branch ![x,y]) := by
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  have h := globalForcing_eq_on_fd q branch (ofComplex (point x y)) (point_mem_fd x hy hx)
  have hp : 0 < (point x y).im := by simp [point]; linarith
  rw [ofComplex_apply_of_im_pos hp] at h
  dsimp only [Function.comp_apply]
  rw [ofComplex_apply_of_im_pos hp]
  simpa only [coordinates,point,UpperHalfPlane.re,UpperHalfPlane.im,
    Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_I_re,Complex.mul_I_im,neg_zero,add_zero,zero_add] using h

/-- The actual original response solves the cusp ODE with every Fourier pair and cutoff term retained. -/
theorem responseMean_equation (q : XiZeroCopy) (branch : Bool) {y : ℝ} (hy : 2 < y) :
    (y:ℂ)^(2 : ℕ)*deriv (deriv (responseMean q branch)) y-
      parameter q branch*responseMean q branch y =
        (parameter q branch/2)*(principal (center q) ![0,y] ^(2 : ℕ)+
          8*∑' N, amplitude (center q) y N^(2 : ℕ))-
          ((y:ℂ)^(2 : ℕ)*deriv (deriv (cutoffHeight q branch)) y-
            parameter q branch*cutoffHeight q branch y) := by
  rw [responseMean_global_equation q branch (by linarith),globalForcing_average q branch hy]
  exact mean_forcing q branch (by linarith)

end
end RHTower.D4BMCuspResponse
