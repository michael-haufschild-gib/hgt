import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspMeanDerivative

/-!
# The full planar Laplacian under a periodic cusp average.

The field is the original native energy response. Its identification with
continued retarded propagation and any extinction law remain separate.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMCuspResponse
open D4BMModularCore D4BMCuspProjection
noncomputable section

/-- The average's first derivative is the exact mean of the vertical derivative. -/
theorem average_deriv (F : ℂ → ℂ)
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    deriv (average F) y = average (vertical F) y := (average_hasDerivAt F hf hy).deriv

/-- The original average has a second derivative given by the actual second chart derivative. -/
theorem average_second_hasDerivAt (F : ℂ → ℂ)
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (deriv (average F)) (average (vertical (vertical F)) y) y := by
  apply (average_hasDerivAt (vertical F) (planar_derivative_contDiffOn hf Complex.I) hy).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hy] with t ht
  exact average_deriv F hf ht

private theorem horizontal_periodic (F : ℂ → ℂ)
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im}) (y : ℝ) (hy : 0 < y)
    (hp : ∀ x : ℝ, F (point (x+1) y)=F (point x y)) (x : ℝ) :
    horizontal F (point (x+1) y)=horizontal F (point x y) := by
  have h1 := (slice_horizontal_derivative F hf y hy (x+1)).scomp x ((hasDerivAt_id x).add_const 1)
  have h2 := slice_horizontal_derivative F hf y hy x
  have he : (fun t : ℝ => F (point (t+1) y)) = (fun t => F (point t y)) := funext hp
  have h1' : HasDerivAt (fun t : ℝ => F (point t y)) (horizontal F (point (x+1) y)) x := by
    simpa only [Function.comp_def,id_eq,one_smul,he] using h1
  exact h1'.unique h2

/-- Horizontal periodicity cancels the full horizontal second derivative in the actual mean. -/
theorem average_horizontal_second (F : ℂ → ℂ)
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y)
    (hp : ∀ x : ℝ, F (point (x+1) y)=F (point x y)) :
    average (horizontal (horizontal F)) y = 0 := by
  have hd := planar_derivative_contDiffOn hf (1:ℂ)
  have hdd := planar_derivative_contDiffOn hd (1:ℂ)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (-1/2:ℝ)) (b := (1/2:ℝ))
    (fun x _ => slice_horizontal_derivative (horizontal F) hd y hy x)
    ((slice_continuous (horizontal (horizontal F)) hdd hy).intervalIntegrable _ _)
  rw [intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ) ≤ 1/2)] at h
  change average (horizontal (horizontal F)) y = _ at h
  rw [h]
  have hp' := horizontal_periodic F hf y hy hp (-1/2)
  norm_num at hp'
  exact sub_eq_zero.mpr (by simpa only [neg_div] using hp')

/-- The cusp mean of the full planar Laplacian equals the original mean's second height derivative. -/
theorem average_laplacian (F : ℂ → ℂ)
    (hf : ContDiffOn ℝ ∞ F {z : ℂ | 0 < z.im}) {y : ℝ} (hy : 0 < y)
    (hp : ∀ x : ℝ, F (point (x+1) y)=F (point x y)) :
    average (planarLaplacian F) y = deriv (deriv (average F)) y := by
  have hd1 := planar_derivative_contDiffOn hf (1:ℂ)
  have hdI := planar_derivative_contDiffOn hf Complex.I
  have hi1 : IntegrableOn (fun x => horizontal (horizontal F) (point x y))
      (Ioc (-1/2:ℝ) (1/2)) := (slice_continuous (horizontal (horizontal F))
    (planar_derivative_contDiffOn hd1 (1:ℂ)) hy).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hiI : IntegrableOn (fun x => vertical (vertical F) (point x y))
      (Ioc (-1/2:ℝ) (1/2)) := (slice_continuous (vertical (vertical F))
    (planar_derivative_contDiffOn hdI Complex.I) hy).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  simp only [average,mean,planarLaplacian,Fin.sum_univ_two,direction,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  change (∫ x in Ioc (-1/2:ℝ) (1/2),
    horizontal (horizontal F) (point x y)+vertical (vertical F) (point x y)) = _
  rw [integral_add hi1 hiI]
  change average (horizontal (horizontal F)) y+average (vertical (vertical F)) y = _
  rw [average_horizontal_second F hf hy hp,zero_add]
  exact (average_second_hasDerivAt F hf hy).deriv.symm

end
end RHTower.D4BMCuspResponse
