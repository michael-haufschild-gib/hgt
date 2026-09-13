import GaloisForLFunctions.HTGeometry.BarnesMellinRepresentation
import GaloisForLFunctions.HTGeometry.MonomialLaplaceComplex
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Causal Gamma-half kernels and pole-clearing filters

The normalized complex-rate Gamma-half kernel is integrable in the positive-rate
half-plane. Convolution with a causal exponential supplies an explicit pole-clearing
filter, whose Laplace transform has square `(s+w)/(s+3)^2`.
-/

open MeasureTheory Set Filter Topology
open scoped Convolution

noncomputable section
namespace GaloisForLFunctions.HTGeometry

def causalComplexLaplaceWeight (s : ℂ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(s * t)) * f t

def causalComplexLaplace (s : ℂ) (f : ℝ → ℂ) : ℂ :=
  ∫ t, causalComplexLaplaceWeight s f t

theorem causalComplexLaplaceWeight_integrable {s : ℂ} (hs : 0 ≤ s.re)
    {f : ℝ → ℂ} (hf : Integrable f) (hc : ∀ t ≤ 0, f t = 0) :
    Integrable (causalComplexLaplaceWeight s f) := by
  apply hf.norm.mono'
  · exact (by fun_prop : Continuous (fun t : ℝ => Complex.exp (-(s * t))))
      |>.aestronglyMeasurable.mul hf.aestronglyMeasurable
  filter_upwards [] with t
  by_cases ht : t ≤ 0
  · simp [causalComplexLaplaceWeight, hc t ht]
  · have he : Real.exp (-(s.re * t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hs (le_of_not_ge ht)))
    simpa [causalComplexLaplaceWeight, norm_mul, Complex.norm_exp] using
      mul_le_mul_of_nonneg_right he (norm_nonneg (f t))

theorem causalComplexLaplaceWeight_convolution (s : ℂ) (f g : ℝ → ℂ) :
    causalComplexLaplaceWeight s (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) =
      causalComplexLaplaceWeight s f ⋆[ContinuousLinearMap.mul ℂ ℂ]
        causalComplexLaplaceWeight s g := by
  funext t
  rw [causalComplexLaplaceWeight, convolution_def, convolution_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  change Complex.exp (-(s * t)) * (f u * g (t-u)) =
    (Complex.exp (-(s*u)) * f u) * (Complex.exp (-(s*((t-u : ℝ) : ℂ))) * g (t-u))
  have he : Complex.exp (-(s * t)) =
      Complex.exp (-(s*u)) * Complex.exp (-(s*((t-u : ℝ) : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

theorem causalComplexLaplace_convolution {s : ℂ} (hs : 0 ≤ s.re)
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (hfc : ∀ t ≤ 0, f t = 0) (hgc : ∀ t ≤ 0, g t = 0) :
    causalComplexLaplace s (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) =
      causalComplexLaplace s f * causalComplexLaplace s g := by
  rw [causalComplexLaplace, causalComplexLaplaceWeight_convolution,
    integral_convolution (ContinuousLinearMap.mul ℂ ℂ)
      (causalComplexLaplaceWeight_integrable hs hf hfc)
      (causalComplexLaplaceWeight_integrable hs hg hgc)]
  rfl

theorem causal_convolution_nonpos {f g : ℝ → ℂ}
    (hf : ∀ t ≤ 0, f t = 0) (hg : ∀ t ≤ 0, g t = 0) {t : ℝ} (ht : t ≤ 0) :
    (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) t = 0 := by
  rw [convolution_def]
  apply integral_eq_zero_of_ae
  filter_upwards [] with u
  change f u * g (t-u) = 0
  by_cases hu : u ≤ 0
  · rw [hf u hu, zero_mul]
  · rw [hg (t-u) (by linarith), mul_zero]

def gammaHalfCausal (w : ℂ) : ℝ → ℂ :=
  (Ioi 0).indicator (fun t : ℝ => (Complex.Gamma (1/2 : ℂ))⁻¹ *
    ((t : ℂ) ^ (-(1/2 : ℂ)) * Complex.exp (-(w*t))))

theorem gammaHalfCausal_nonpos (w : ℂ) {t : ℝ} (ht : t ≤ 0) :
    gammaHalfCausal w t = 0 := by
  exact indicator_of_notMem (not_lt.mpr ht) _

theorem gammaHalfCausal_integrable {w : ℂ} (hw : 0 < w.re) :
    Integrable (gammaHalfCausal w) := by
  unfold gammaHalfCausal
  rw [integrable_indicator_iff measurableSet_Ioi]
  have h := (integrableOn_cpow_mul_exp_neg_mul_Ioi
    (s := (1/2 : ℂ)) (by norm_num) hw).const_mul (Complex.Gamma (1/2 : ℂ))⁻¹
  change Integrable _ (volume.restrict (Ioi 0))
  simpa only [show (1/2 : ℂ)-1 = -(1/2 : ℂ) by ring] using h

theorem causalComplexLaplaceWeight_gammaHalf (s w : ℂ) :
    causalComplexLaplaceWeight s (gammaHalfCausal w) = gammaHalfCausal (s+w) := by
  funext t
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · simp only [causalComplexLaplaceWeight, gammaHalfCausal, indicator_of_mem ht]
    have he : Complex.exp (-(s*t)) * Complex.exp (-(w*t)) =
        Complex.exp (-((s+w)*t)) := by rw [← Complex.exp_add]; congr 1; ring
    calc
      _ = (Complex.Gamma (1/2 : ℂ))⁻¹ * ((t : ℂ) ^ (-(1/2 : ℂ))) *
        (Complex.exp (-(s*t)) * Complex.exp (-(w*t))) := by ring
      _ = _ := by rw [he]; ring
  · simp only [causalComplexLaplaceWeight, gammaHalfCausal, indicator_of_notMem ht, mul_zero]

theorem causalComplexLaplace_gammaHalf {s w : ℂ} (h : 0 < (s+w).re) :
    causalComplexLaplace s (gammaHalfCausal w) = (s+w) ^ (-(1/2 : ℂ)) := by
  rw [causalComplexLaplace, causalComplexLaplaceWeight_gammaHalf, gammaHalfCausal,
    integral_indicator measurableSet_Ioi, integral_const_mul]
  have hi := integral_cpow_mul_exp_neg_mul_Ioi (s := (1/2 : ℂ)) (by norm_num) h
  rw [show (1/2 : ℂ)-1 = -(1/2 : ℂ) by ring] at hi
  rw [hi]
  have hg := Complex.Gamma_ne_zero_of_re_pos (s := (1/2 : ℂ)) (by norm_num)
  rw [← mul_assoc, inv_mul_cancel₀ hg, one_mul]

def causalExpThree : ℝ → ℂ :=
  (Ioi 0).indicator (fun t : ℝ => Complex.exp (-(3*(t : ℂ))))

theorem causalExpThree_nonpos {t : ℝ} (ht : t ≤ 0) : causalExpThree t = 0 :=
  indicator_of_notMem (not_lt.mpr ht) _

theorem causalExpThree_integrable : Integrable causalExpThree := by
  unfold causalExpThree
  rw [integrable_indicator_iff measurableSet_Ioi]
  simpa using integrableOn_natPow_mul_cexp (c := 3) (by norm_num) 0

theorem causalComplexLaplaceWeight_expThree (s : ℂ) :
    causalComplexLaplaceWeight s causalExpThree =
      (Ioi 0).indicator (fun t : ℝ => Complex.exp (-((s+3)*t))) := by
  funext t
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · simp only [causalComplexLaplaceWeight, causalExpThree, indicator_of_mem ht]
    rw [← Complex.exp_add]
    congr 1
    ring
  · simp only [causalComplexLaplaceWeight, causalExpThree, indicator_of_notMem ht, mul_zero]

theorem causalComplexLaplace_expThree {s : ℂ} (hs : 0 ≤ s.re) :
    causalComplexLaplace s causalExpThree = (s+3)⁻¹ := by
  rw [causalComplexLaplace, causalComplexLaplaceWeight_expThree,
    integral_indicator measurableSet_Ioi]
  simpa using integral_Ioi_pow_mul_cexp
    (c := s+3) (by simp only [Complex.add_re]; norm_num; linarith) 0

def filteredGammaHalf (w : ℂ) (t : ℝ) : ℂ :=
  gammaHalfCausal w t - (3-w) *
    (causalExpThree ⋆[ContinuousLinearMap.mul ℂ ℂ] gammaHalfCausal w) t

theorem filteredGammaHalf_nonpos (w : ℂ) {t : ℝ} (ht : t ≤ 0) :
    filteredGammaHalf w t = 0 := by
  rw [filteredGammaHalf, gammaHalfCausal_nonpos w ht,
    causal_convolution_nonpos (fun _ h => causalExpThree_nonpos h)
      (fun _ h => gammaHalfCausal_nonpos w h) ht, mul_zero, sub_zero]

theorem filteredGammaHalf_integrable {w : ℂ} (hw : 0 < w.re) :
    Integrable (filteredGammaHalf w) :=
  (gammaHalfCausal_integrable hw).sub
    ((causalExpThree_integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ)
      (gammaHalfCausal_integrable hw)).const_mul (3-w))

theorem causalComplexLaplace_filteredGammaHalf {s w : ℂ}
    (hs : 0 ≤ s.re) (hw : 0 < w.re) :
    causalComplexLaplace s (filteredGammaHalf w) =
      (1 - (3-w) * (s+3)⁻¹) * (s+w) ^ (-(1/2 : ℂ)) := by
  have hc := causalExpThree_integrable.integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (gammaHalfCausal_integrable hw)
  have hcc : ∀ t ≤ 0,
      (causalExpThree ⋆[ContinuousLinearMap.mul ℂ ℂ] gammaHalfCausal w) t = 0 :=
    fun _ h => causal_convolution_nonpos (fun _ h => causalExpThree_nonpos h)
      (fun _ h => gammaHalfCausal_nonpos w h) h
  have heq : causalComplexLaplaceWeight s (filteredGammaHalf w) = fun t =>
      causalComplexLaplaceWeight s (gammaHalfCausal w) t - (3-w) *
        causalComplexLaplaceWeight s
          (causalExpThree ⋆[ContinuousLinearMap.mul ℂ ℂ] gammaHalfCausal w) t := by
    funext t
    simp only [causalComplexLaplaceWeight, filteredGammaHalf]
    ring
  rw [causalComplexLaplace, heq,
    integral_sub (causalComplexLaplaceWeight_integrable hs (gammaHalfCausal_integrable hw)
      (fun _ h => gammaHalfCausal_nonpos w h))
      ((causalComplexLaplaceWeight_integrable hs hc hcc).const_mul (3-w)),
    integral_const_mul]
  change causalComplexLaplace s (gammaHalfCausal w) - (3-w) *
    causalComplexLaplace s (causalExpThree ⋆[ContinuousLinearMap.mul ℂ ℂ]
      gammaHalfCausal w) = _
  rw [causalComplexLaplace_convolution hs causalExpThree_integrable
    (gammaHalfCausal_integrable hw) (fun _ h => causalExpThree_nonpos h)
      (fun _ h => gammaHalfCausal_nonpos w h),
    causalComplexLaplace_expThree hs,
    causalComplexLaplace_gammaHalf (by simp only [Complex.add_re]; linarith)]
  ring

theorem causalComplexLaplace_filteredGammaHalf_sq {s w : ℂ}
    (hs : 0 ≤ s.re) (hw : 0 < w.re) :
    causalComplexLaplace s (filteredGammaHalf w) ^ 2 = (s+w)/(s+3)^2 := by
  have hw0 : s+w ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.zero_re] at hr
    linarith
  have hs0 : s+3 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    linarith
  have hp : ((s+w) ^ (-(1/2 : ℂ))) ^ 2 = (s+w)⁻¹ := by
    rw [← Complex.cpow_mul_nat]
    norm_num [Complex.cpow_neg_one]
  rw [causalComplexLaplace_filteredGammaHalf hs hw, mul_pow, hp]
  field_simp
  ring

end GaloisForLFunctions.HTGeometry

