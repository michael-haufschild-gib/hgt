import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspNativeSourcePair
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMClassicalResponse
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# Differentiation under the native width-one cusp average.

The field is the original native energy response. Its identification with
continued retarded propagation and any extinction law remain separate.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMCuspResponse
open D4BMModularCore D4BMCuspProjection
noncomputable section

def point (x y : ℝ) : ℂ := (x:ℂ)+(y:ℂ)*Complex.I

def vertical (F : ℂ → ℂ) (z : ℂ) : ℂ := fderiv ℝ F z Complex.I

def horizontal (F : ℂ → ℂ) (z : ℂ) : ℂ := fderiv ℝ F z 1

def average (F : ℂ → ℂ) (y : ℝ) : ℂ := mean (fun x => F (point x y))

private theorem point_vertical (x y : ℝ) :
    HasDerivAt (point x) Complex.I y := by
  change HasDerivAt (fun t : ℝ => (x:ℂ)+(t:ℂ)*Complex.I) Complex.I y
  simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul] using ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I).const_add (x:ℂ)

private theorem point_horizontal (x y : ℝ) :
    HasDerivAt (fun t => point t y) 1 x := by
  simpa [point] using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y:ℂ)*Complex.I)

/-- Actual vertical slice derivative of a smooth positive-height chart field. -/
theorem slice_vertical_derivative (F : ℂ → ℂ)
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im}) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t => F (point x t)) (vertical F (point x y)) y := by
  have hp : 0 < (point x y).im := by simpa [point] using hy
  exact ((hf.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds hp)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt y (point_vertical x y)

/-- Actual horizontal slice derivative, retaining the original chart differential. -/
theorem slice_horizontal_derivative (F : ℂ → ℂ)
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im}) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun t => F (point t y)) (horizontal F (point x y)) x := by
  have hp : 0 < (point x y).im := by simpa [point] using hy
  exact ((hf.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds hp)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt x (point_horizontal x y)

/-- Every actual positive-height horizontal slice is continuous. -/
theorem slice_continuous (F : ℂ → ℂ)
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    Continuous (fun x => F (point x y)) :=
  continuous_iff_continuousAt.mpr (fun x => (slice_horizontal_derivative F hf y hy x).continuousAt)

/-- The literal width-one average differentiates under its integral. Compact
horizontal support and a local positive-height rectangle discharge domination. -/
theorem average_hasDerivAt (F : ℂ → ℂ)
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (average F) (average (vertical F) y) y := by
  have hd : ContDiffOn ℝ ∞ (vertical F) {z : ℂ | 0 < z.im} :=
    planar_derivative_contDiffOn hf Complex.I
  let K : Set (ℝ × ℝ) := Icc (-1/2:ℝ) (1/2) ×ˢ Icc (y/2) (y+1)
  have hcont : ContinuousOn (fun xy : ℝ × ℝ => vertical F (point xy.1 xy.2)) K := by
    apply hd.continuousOn.comp (show Continuous (fun xy : ℝ × ℝ => point xy.1 xy.2) by
      unfold point; fun_prop).continuousOn
    intro xy hxy
    have hlow := hxy.2.1
    change 0 < (point xy.1 xy.2).im
    simp only [point,Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add]
    linarith
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont
  have hn : Ioo (y/2) (y+1) ∈ 𝓝 y := Ioo_mem_nhds (by linarith) (by linarith)
  have hpos : ∀ t ∈ Ioo (y/2) (y+1), 0 < t := by intro t ht; linarith [ht.1]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc (-1/2:ℝ) (1/2)))
    (F := fun t x => F (point x t)) (F' := fun t x => vertical F (point x t))
    (bound := fun _ => C) hn
    (by filter_upwards [hn] with t ht
        exact (slice_continuous F hf (hpos t ht)).aestronglyMeasurable.restrict)
    ((slice_continuous F hf hy).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    ((slice_continuous (vertical F) hd hy).aestronglyMeasurable.restrict)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        intro t ht
        exact hC (x,t) ⟨⟨hx.1.le,hx.2⟩,⟨ht.1.le,ht.2.le⟩⟩)
    (integrable_const C)
    (by filter_upwards with x
        intro t ht
        exact slice_vertical_derivative F hf x (hpos t ht))).2

end
end RHTower.D4BMCuspResponse
