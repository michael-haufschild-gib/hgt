import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineJacobianModuli
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineHeightNormalization
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.PositiveGridCorrection
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

/-!
# Real node corrections for prescribed spline coefficients

Bounded dual primitives turn a complex target vector into real node displacements.
Their finite sums control displacement size and the nonlinear increment, including
the exact spline denominator. Geometric sums bound the baseline numerator residual.
The closed-ball inverse theorem converts a half-Lipschitz defect from the identity
into an explicit small-target realization once the discrete Jacobian is controlled.
-/

open Finset Complex Metric
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

variable {ι : Type*} [Fintype ι]

def splineHeightCorrection (δ : ℝ) (t : ι → ℝ) (y : ι → ℂ) (x : ℝ) : ℝ :=
  2*(∑ i, splineDual δ (t i) x*y i).re

def splineHeightCorrectionBound (δ : ℝ) (t : ι → ℝ) : ℝ :=
  2*∑ i, splineDualBound δ (t i)

lemma splineHeightCorrection_sub (δ : ℝ) (t : ι → ℝ) (y z : ι → ℂ) (x : ℝ) :
    splineHeightCorrection δ t y x-splineHeightCorrection δ t z x=
      splineHeightCorrection δ t (y-z) x := by
  simp only [splineHeightCorrection, Pi.sub_apply, mul_sub, sum_sub_distrib, Complex.sub_re]

lemma splineHeightCorrection_complex (δ : ℝ) (t : ι → ℝ) (y : ι → ℂ) (x : ℝ) :
    (splineHeightCorrection δ t y x : ℂ)=
      ∑ i, (splineDual δ (t i) x*y i+
        (starRingEnd ℂ) (splineDual δ (t i) x)*(starRingEnd ℂ) (y i)) := by
  have hr (w : ℂ) : ((2*w.re : ℝ) : ℂ)=w+(starRingEnd ℂ) w := by
    apply Complex.ext <;> simp [two_mul]
  rw [splineHeightCorrection, hr, map_sum, sum_add_distrib]
  simp only [map_mul]

lemma splineHeightCorrectionBound_nonneg {δ : ℝ} (hδ : 0 < δ) {t : ι → ℝ}
    (ht : ∀ i, 0 < t i) : 0 ≤ splineHeightCorrectionBound δ t := by
  apply mul_nonneg (by norm_num)
  apply sum_nonneg
  intro i _
  exact (norm_nonneg (splineDual δ (t i) 0)).trans
    (norm_splineDual_le (s := t i) hδ (by linarith only [ht i]) 0)

lemma abs_splineHeightCorrection_le {δ : ℝ} (hδ : 0 < δ) {t : ι → ℝ}
    (ht : ∀ i, 0 < t i) (y : ι → ℂ) (x : ℝ) :
    |splineHeightCorrection δ t y x| ≤ splineHeightCorrectionBound δ t*‖y‖ := by
  rw [splineHeightCorrection, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2*‖∑ i, splineDual δ (t i) x*y i‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
    _ ≤ 2*∑ i, ‖splineDual δ (t i) x*y i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)
    _ ≤ 2*∑ i, splineDualBound δ (t i)*‖y‖ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply sum_le_sum
      intro i _
      rw [norm_mul]
      have hd : ‖splineDual δ (t i) x‖ ≤ splineDualBound δ (t i) :=
        norm_splineDual_le (s := t i) hδ (by linarith only [ht i]) x
      exact mul_le_mul hd (norm_le_pi_norm y i) (norm_nonneg _) ((norm_nonneg _).trans hd)
    _ = _ := by rw [← sum_mul, splineHeightCorrectionBound]; ring

lemma abs_splineHeightCorrection_sub_le {δ : ℝ} (hδ : 0 < δ) {t : ι → ℝ}
    (ht : ∀ i, 0 < t i) (y z : ι → ℂ) (x : ℝ) :
    |splineHeightCorrection δ t y x-splineHeightCorrection δ t z x| ≤
      splineHeightCorrectionBound δ t*‖y-z‖ := by
  rw [splineHeightCorrection_sub]
  exact abs_splineHeightCorrection_le hδ ht (y-z) x

/-- The node-motion remainder is Lipschitz in the target parameter on a fixed ball. -/
theorem norm_corrected_spline_increment_le {δ : ℝ} (hδ : 0 < δ) {t : ι → ℝ}
    (ht : ∀ i, 0 < t i) {ρ : ℝ} (hρ : 0 ≤ ρ) {y z : ι → ℂ}
    (hy : ‖y‖ ≤ ρ) (hz : ‖z‖ ≤ ρ) (i : ι) (x : ℝ) :
    ‖shiftedSplineNumerator δ (t i) (x+splineHeightCorrection δ t z x)-
      shiftedSplineNumerator δ (t i) (x+splineHeightCorrection δ t y x)-
      shiftedSplineSlope δ (t i) x*
        ((splineHeightCorrection δ t z x-splineHeightCorrection δ t y x : ℝ) : ℂ)‖ ≤
      splineSecondBound δ (t i)*(splineHeightCorrectionBound δ t)^2*ρ*‖z-y‖ := by
  have hP := splineHeightCorrectionBound_nonneg hδ ht
  have hC : 0 ≤ splineSecondBound δ (t i) := sum_nonneg fun _ _ => abs_nonneg _
  have hya := (abs_splineHeightCorrection_le hδ ht y x).trans (mul_le_mul_of_nonneg_left hy hP)
  have hza := (abs_splineHeightCorrection_le hδ ht z x).trans (mul_le_mul_of_nonneg_left hz hP)
  have h := norm_spline_increment_remainder_le δ (t i) x hya hza
  refine h.trans ?_
  calc
    _ ≤ splineSecondBound δ (t i)*(splineHeightCorrectionBound δ t*ρ)*
        (splineHeightCorrectionBound δ t*‖z-y‖) :=
      mul_le_mul_of_nonneg_left (abs_splineHeightCorrection_sub_le hδ ht z y x)
        (mul_nonneg hC (mul_nonneg hP hρ))
    _ = _ := by ring

/-- Exact geometric sums make the baseline residual independent of the grid spacing error. -/
lemma norm_grid_spline_numerator_sum_le {Λ η t : ℝ} (hΛ : 0 < Λ) (hη : 0 < η)
    (hfreq : ∀ j : Fin 9, |t+splineShift j| ≤ 2*Λ)
    (hgap : ∀ j : Fin 9, η ≤ |t+splineShift j|) (δ H : ℝ) (n : ℕ) :
    ‖∑ j : Fin n, shiftedSplineNumerator δ t (H+j.val*(Real.pi/(2*Λ)))‖ ≤
      2*Λ*splineNumeratorBound δ/η := by
  have he : (∑ j : Fin n, shiftedSplineNumerator δ t (H+j.val*(Real.pi/(2*Λ))))=
      ∑ k : Fin 9, (splineCoefficient δ k : ℂ)*
        ∑ j : Fin n, phase (t+splineShift k) (H+j.val*(Real.pi/(2*Λ))) := by
    unfold shiftedSplineNumerator
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    rw [mul_sum]
  rw [he]
  calc
    _ ≤ ∑ k : Fin 9, |splineCoefficient δ k| *(2*Λ/η) := by
      refine (norm_sum_le _ _).trans ?_
      apply sum_le_sum
      intro k _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (norm_grid_sum_le hΛ hη (hfreq k) (hgap k) H n) (abs_nonneg _)
    _ = _ := by rw [← sum_mul]; unfold splineNumeratorBound; ring

def normalizedSplineNumerator (H δ t x : ℝ) : ℂ :=
  splineHeightFactor H δ x*shiftedSplineNumerator δ t x

lemma normalizedSplineNumerator_eq (H δ t x : ℝ) :
    normalizedSplineNumerator H δ t x=(H : ℂ)^8*
      (Complex.sinh ((δ : ℂ)+(x : ℂ)*Complex.I)/((δ : ℂ)+(x : ℂ)*Complex.I))^8*phase t x := by
  rw [normalizedSplineNumerator, splineHeightFactor, shiftedSplineNumerator_eq, div_pow]
  ring

lemma norm_shiftedSplineNumerator_sub_le (δ t x y : ℝ) :
    ‖shiftedSplineNumerator δ t y-shiftedSplineNumerator δ t x‖ ≤ splineSlopeBound δ t*|y-x| := by
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (s := Set.univ) (fun u _ => (hasDerivAt_shiftedSplineNumerator δ t u).hasDerivWithinAt)
      (fun u _ => norm_shiftedSplineSlope_le δ t u) convex_univ (Set.mem_univ x) (Set.mem_univ y)

lemma norm_splineHeightFactor_sub_le {H δ C x y : ℝ} (hH : 0 < H)
    (hx : x ∈ Set.Icc H (H+C)) (hy : y ∈ Set.Icc H (H+C)) :
    ‖splineHeightFactor H δ y-splineHeightFactor H δ x‖ ≤ (8/H)*|y-x| := by
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u (hu : u ∈ Set.Icc H (H+C)) => (hasDerivAt_splineHeightFactor (δ := δ) hH hu.1).hasDerivWithinAt)
      (fun u (hu : u ∈ Set.Icc H (H+C)) => norm_splineHeightFactor_deriv_le (δ := δ) hH hu.1)
      (convex_Icc _ _) hx hy

def splineNormalizationErrorBound (H δ t C : ℝ) : ℝ :=
  8*((C+δ)*splineSlopeBound δ t+splineNumeratorBound δ)/H

lemma norm_spline_normalization_error_sub_le {H δ C x y : ℝ} (hH : 0 < H)
    (hδ : 0 ≤ δ) (t : ℝ) (hx : x ∈ Set.Icc H (H+C)) (hy : y ∈ Set.Icc H (H+C)) :
    ‖(splineHeightFactor H δ y-1)*shiftedSplineNumerator δ t y-
      (splineHeightFactor H δ x-1)*shiftedSplineNumerator δ t x‖ ≤
      splineNormalizationErrorBound H δ t C*|y-x| := by
  have hq := norm_splineHeightFactor_sub_one_le hH hδ hy.1 hy.2
  have hd := norm_splineHeightFactor_sub_le (δ := δ) hH hx hy
  have hv := norm_shiftedSplineNumerator_sub_le δ t x y
  have hb := norm_shiftedSplineNumerator_le δ t x
  have he : (splineHeightFactor H δ y-1)*shiftedSplineNumerator δ t y-
      (splineHeightFactor H δ x-1)*shiftedSplineNumerator δ t x=
      (splineHeightFactor H δ y-1)*(shiftedSplineNumerator δ t y-shiftedSplineNumerator δ t x)+
      (splineHeightFactor H δ y-splineHeightFactor H δ x)*shiftedSplineNumerator δ t x := by ring
  rw [he]
  calc
    _ ≤ ‖splineHeightFactor H δ y-1‖*‖shiftedSplineNumerator δ t y-shiftedSplineNumerator δ t x‖+
        ‖splineHeightFactor H δ y-splineHeightFactor H δ x‖*‖shiftedSplineNumerator δ t x‖ := by
      simpa only [norm_mul] using norm_add_le
        ((splineHeightFactor H δ y-1)*(shiftedSplineNumerator δ t y-shiftedSplineNumerator δ t x))
        ((splineHeightFactor H δ y-splineHeightFactor H δ x)*shiftedSplineNumerator δ t x)
    _ ≤ (8*(C+δ)/H)*(splineSlopeBound δ t*|y-x|)+((8/H)*|y-x|)*splineNumeratorBound δ :=
      add_le_add (mul_le_mul hq hv (norm_nonneg _) ((norm_nonneg _).trans hq))
        (mul_le_mul hd hb (norm_nonneg _) ((norm_nonneg _).trans hd))
    _ = _ := by unfold splineNormalizationErrorBound; ring

/-- Exact spline coefficients retain the same linearization, with an inverse-height error. -/
theorem norm_exact_corrected_spline_increment_le {H δ C : ℝ} (hH : 0 < H) (hδ : 0 < δ)
    {t : ι → ℝ} (ht : ∀ i, 0 < t i) {ρ : ℝ} (hρ : 0 ≤ ρ) {y z : ι → ℂ}
    (hy : ‖y‖ ≤ ρ) (hz : ‖z‖ ≤ ρ) (i : ι) (x : ℝ)
    (hxy : x+splineHeightCorrection δ t y x ∈ Set.Icc H (H+C))
    (hxz : x+splineHeightCorrection δ t z x ∈ Set.Icc H (H+C)) :
    ‖normalizedSplineNumerator H δ (t i) (x+splineHeightCorrection δ t z x)-
      normalizedSplineNumerator H δ (t i) (x+splineHeightCorrection δ t y x)-
      shiftedSplineSlope δ (t i) x*
        ((splineHeightCorrection δ t z x-splineHeightCorrection δ t y x : ℝ) : ℂ)‖ ≤
      (splineSecondBound δ (t i)*(splineHeightCorrectionBound δ t)^2*ρ+
        splineNormalizationErrorBound H δ (t i) C*splineHeightCorrectionBound δ t)*‖z-y‖ := by
  let a := splineHeightCorrection δ t y x
  let b := splineHeightCorrection δ t z x
  have hn := norm_corrected_spline_increment_le hδ ht hρ hy hz i x
  have hE := norm_spline_normalization_error_sub_le hH hδ.le (t i) hxy hxz
  have hd := abs_splineHeightCorrection_sub_le hδ ht z y x
  have hC : 0 ≤ C := by linarith only [hxy.1,hxy.2]
  have hG : 0 ≤ splineSlopeBound δ (t i) := sum_nonneg fun _ _ => abs_nonneg _
  have hB := splineNumeratorBound_nonneg δ
  have hE0 : 0 ≤ splineNormalizationErrorBound H δ (t i) C := by
    unfold splineNormalizationErrorBound
    positivity
  rw [show x+b-(x+a)=b-a by ring] at hE
  have hEb := hE.trans (mul_le_mul_of_nonneg_left hd hE0)
  have he : normalizedSplineNumerator H δ (t i) (x+b)-
      normalizedSplineNumerator H δ (t i) (x+a)-shiftedSplineSlope δ (t i) x*((b-a : ℝ) : ℂ)=
      (shiftedSplineNumerator δ (t i) (x+b)-shiftedSplineNumerator δ (t i) (x+a)-
        shiftedSplineSlope δ (t i) x*((b-a : ℝ) : ℂ))+
      ((splineHeightFactor H δ (x+b)-1)*shiftedSplineNumerator δ (t i) (x+b)-
        (splineHeightFactor H δ (x+a)-1)*shiftedSplineNumerator δ (t i) (x+a)) := by
    unfold normalizedSplineNumerator
    ring
  change ‖normalizedSplineNumerator H δ (t i) (x+b)-
      normalizedSplineNumerator H δ (t i) (x+a)-shiftedSplineSlope δ (t i) x*((b-a : ℝ) : ℂ)‖ ≤ _
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add hn hEb).trans_eq (by ring))

/-- A half-Lipschitz defect from the identity gives an explicit small-target inverse. -/
lemma exists_small_solution_of_half_defect {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : E → E} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hf : ApproximatesLinearOn f (ContinuousLinearMap.id ℝ E) (closedBall 0 ρ) (1/2))
    (hf0 : ‖f 0‖ ≤ ρ/4) {v : E} (hv : ‖v‖ ≤ ρ/4) :
    ∃ y : E, ‖y‖ ≤ ρ ∧ f y=v := by
  let R : (ContinuousLinearMap.id ℝ E).NonlinearRightInverse :=
    { toFun := id
      nnnorm := 1
      bound' := fun y => by simp
      right_inv' := fun y => rfl }
  have hs := hf.surjOn_closedBall_of_nonlinearRightInverse R hρ (Set.Subset.refl _)
  have hv' : v ∈ closedBall (f 0) (((R.nnnorm : ℝ)⁻¹-((1/2 : NNReal) : ℝ))*ρ) := by
    rw [mem_closedBall, dist_eq_norm]
    have hn := (norm_sub_le v (f 0)).trans (add_le_add hv hf0)
    norm_num [R]
    linarith only [hn]
  obtain ⟨y,hy,he⟩ := hs hv'
  refine ⟨y, ?_, he⟩
  simpa only [mem_closedBall, dist_zero_right] using hy

#print axioms norm_corrected_spline_increment_le
#print axioms norm_exact_corrected_spline_increment_le
#print axioms norm_grid_spline_numerator_sum_le
#print axioms exists_small_solution_of_half_defect
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
