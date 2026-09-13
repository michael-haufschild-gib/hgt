import GaloisForLFunctions.HTGeometry.CausalGammaHalfLaplace
import GaloisForLFunctions.HTGeometry.FourierUniquenessL1
import GaloisForLFunctions.HTGeometry.BochnerLaplaceHolomorphy

/-!
# A positive decaying convolution square does not control source growth

Two conjugate filtered Gamma-half kernels produce a real causal source. Its
convolution square is an explicit nonnegative exponentially damped cubic. After
undoing part of the damping, the source has an absolutely convergent Laplace
integral at `2`, but not at `3/4`. Fourier uniqueness verifies the full convolution
identity; a simple transform zero obstructs the stronger source integrability.
-/

open MeasureTheory Set Filter Topology FourierTransform
open scoped Convolution ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.HTGeometry

def conjugateGammaSource : ℝ → ℂ :=
  filteredGammaHalf (1+2*Complex.I) ⋆[ContinuousLinearMap.mul ℂ ℂ]
    filteredGammaHalf (1-2*Complex.I)

theorem conjugateGammaSource_integrable : Integrable conjugateGammaSource :=
  (filteredGammaHalf_integrable (w := 1+2*Complex.I) (by norm_num)).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ)
    (filteredGammaHalf_integrable (w := 1-2*Complex.I) (by norm_num))

theorem conjugateGammaSource_nonpos {t : ℝ} (ht : t ≤ 0) :
    conjugateGammaSource t = 0 :=
  causal_convolution_nonpos (fun _ h => filteredGammaHalf_nonpos _ h)
    (fun _ h => filteredGammaHalf_nonpos _ h) ht

theorem causalComplexLaplace_conjugateGammaSource_sq {s : ℂ} (hs : 0 ≤ s.re) :
    causalComplexLaplace s conjugateGammaSource ^ 2 = ((s+1)^2+4)/(s+3)^4 := by
  rw [conjugateGammaSource, causalComplexLaplace_convolution hs
      (filteredGammaHalf_integrable (by norm_num))
      (filteredGammaHalf_integrable (by norm_num))
      (fun _ h => filteredGammaHalf_nonpos _ h)
      (fun _ h => filteredGammaHalf_nonpos _ h),
    mul_pow, causalComplexLaplace_filteredGammaHalf_sq hs (by norm_num),
    causalComplexLaplace_filteredGammaHalf_sq hs (by norm_num)]
  have he : (s+(1+2*Complex.I)) * (s+(1-2*Complex.I)) = (s+1)^2+4 := by
    calc
      _ = (s+1)^2 - 4 * Complex.I^2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [← mul_div_mul_comm, he]
  congr 1
  ring

def positiveCubicKernel (t : ℝ) : ℝ :=
  Real.exp (-(3*t)) * (t - 2*t^2 + (4/3)*t^3)

def positiveCubicCausal : ℝ → ℂ :=
  (Ioi 0).indicator (fun t => (positiveCubicKernel t : ℂ))

theorem positiveCubicKernel_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ positiveCubicKernel t := by
  have hp : t - 2*t^2 + (4/3)*t^3 = t*((1-t)^2+t^2/3) := by ring
  rw [positiveCubicKernel, hp]
  positivity

theorem tendsto_positiveCubicKernel : Tendsto positiveCubicKernel atTop (𝓝 0) := by
  have h := ((tendsto_pow_mul_exp_neg_mul_atTop (by norm_num : (0:ℝ)<3) 1).sub
    ((tendsto_pow_mul_exp_neg_mul_atTop (by norm_num : (0:ℝ)<3) 2).const_mul 2)).add
    ((tendsto_pow_mul_exp_neg_mul_atTop (by norm_num : (0:ℝ)<3) 3).const_mul (4/3))
  have heq : positiveCubicKernel = fun t : ℝ => t^1*Real.exp (-(3*t)) -
      2*(t^2*Real.exp (-(3*t))) + (4/3)*(t^3*Real.exp (-(3*t))) := by
    funext t
    simp only [positiveCubicKernel, pow_one]
    ring
  rw [heq]
  simpa only [mul_zero, sub_zero, zero_add] using h

theorem positiveCubicKernel_integrand (s : ℂ) (t : ℝ) :
    Complex.exp (-(s*t)) * (positiveCubicKernel t : ℂ) =
      (t : ℂ)^1*Complex.exp (-((s+3)*t)) -
      2*((t : ℂ)^2*Complex.exp (-((s+3)*t))) +
      (4/3)*((t : ℂ)^3*Complex.exp (-((s+3)*t))) := by
  unfold positiveCubicKernel
  push_cast
  have he : Complex.exp (-(s*t)) * Complex.exp (-(3*(t : ℂ))) =
      Complex.exp (-((s+3)*t)) := by rw [← Complex.exp_add]; congr 1; ring
  calc
    _ = (Complex.exp (-(s*t)) * Complex.exp (-(3*(t : ℂ)))) *
      ((t : ℂ)-2*(t : ℂ)^2+(4/3)*(t : ℂ)^3) := by ring
    _ = _ := by rw [he]; ring

theorem integrableOn_positiveCubicKernel_integrand {s : ℂ} (hs : -3 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(s*t)) * (positiveCubicKernel t : ℂ))
      (Ioi 0) := by
  have hc : 0 < (s+3).re := by simp only [Complex.add_re]; norm_num; linarith
  have h := ((integrableOn_natPow_mul_cexp hc 1).sub
    ((integrableOn_natPow_mul_cexp hc 2).const_mul 2)).add
    ((integrableOn_natPow_mul_cexp hc 3).const_mul (4/3))
  exact h.congr (Eventually.of_forall fun t => (positiveCubicKernel_integrand s t).symm)

theorem positiveCubicCausal_integrable : Integrable positiveCubicCausal := by
  rw [positiveCubicCausal, integrable_indicator_iff measurableSet_Ioi]
  have h := integrableOn_positiveCubicKernel_integrand (s := 0) (by norm_num)
  simpa using h

theorem causalComplexLaplace_positiveCubic {s : ℂ} (hs : -3 < s.re) :
    causalComplexLaplace s positiveCubicCausal = ((s+1)^2+4)/(s+3)^4 := by
  have hc : 0 < (s+3).re := by simp only [Complex.add_re]; norm_num; linarith
  have hs0 : s+3 ≠ 0 := by intro h; rw [h] at hc; norm_num at hc
  have he : causalComplexLaplaceWeight s positiveCubicCausal = (Ioi 0).indicator
      (fun t : ℝ => Complex.exp (-(s*t)) * (positiveCubicKernel t : ℂ)) := by
    funext t
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · simp only [causalComplexLaplaceWeight, positiveCubicCausal, indicator_of_mem ht]
    · simp only [causalComplexLaplaceWeight, positiveCubicCausal, indicator_of_notMem ht, mul_zero]
  rw [causalComplexLaplace, he, integral_indicator measurableSet_Ioi]
  have h12 : IntegrableOn (fun t : ℝ => (t : ℂ)^1*Complex.exp (-((s+3)*t)) -
      2*((t : ℂ)^2*Complex.exp (-((s+3)*t)))) (Ioi 0) :=
    (integrableOn_natPow_mul_cexp hc 1).sub ((integrableOn_natPow_mul_cexp hc 2).const_mul 2)
  simp_rw [positiveCubicKernel_integrand]
  rw [integral_add h12 ((integrableOn_natPow_mul_cexp hc 3).const_mul (4/3)),
    integral_sub (integrableOn_natPow_mul_cexp hc 1)
      ((integrableOn_natPow_mul_cexp hc 2).const_mul 2),
    integral_const_mul, integral_const_mul, integral_Ioi_pow_mul_cexp hc 1,
    integral_Ioi_pow_mul_cexp hc 2, integral_Ioi_pow_mul_cexp hc 3]
  norm_num
  field_simp
  ring

theorem causalComplexLaplace_fourier (f : ℝ → ℂ) (x : ℝ) :
    causalComplexLaplace ((2*Real.pi*x : ℝ)*Complex.I) f = 𝓕 f x := by
  rw [causalComplexLaplace, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with t
  change Complex.exp (-(((2*Real.pi*x : ℝ)*Complex.I)*(t : ℂ))) * f t =
    Complex.exp (((-2*Real.pi*(x*t) : ℝ) : ℂ)*Complex.I) * f t
  congr 2
  push_cast
  ring

theorem conjugateGammaSource_convolution_self :
    (conjugateGammaSource ⋆[ContinuousLinearMap.mul ℂ ℂ] conjugateGammaSource)
      =ᵐ[volume] positiveCubicCausal := by
  apply _root_.HTGeometry.ae_eq_of_fourierIntegral_eq
    (conjugateGammaSource_integrable.integrable_convolution
      (ContinuousLinearMap.mul ℂ ℂ) conjugateGammaSource_integrable)
    positiveCubicCausal_integrable
  intro x
  rw [← causalComplexLaplace_fourier, ← causalComplexLaplace_fourier,
    causalComplexLaplace_convolution (by simp) conjugateGammaSource_integrable
      conjugateGammaSource_integrable (fun _ h => conjugateGammaSource_nonpos h)
      (fun _ h => conjugateGammaSource_nonpos h),
    ← pow_two, causalComplexLaplace_conjugateGammaSource_sq (by simp),
    causalComplexLaplace_positiveCubic (by simp)]

theorem gammaHalfCausal_conj (w : ℂ) :
    (fun t => conj (gammaHalfCausal w t)) = gammaHalfCausal (conj w) := by
  funext t
  by_cases ht : 0 < t
  · simp only [gammaHalfCausal, indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
    have hg : conj (Complex.Gamma (1/2 : ℂ)) = Complex.Gamma (1/2 : ℂ) := by
      rw [← Complex.Gamma_conj]
      congr 1
      simp only [map_div₀, map_one, show conj (2 : ℂ) = 2 from Complex.conj_ofReal 2]
    have hp : conj ((t : ℂ)^(-(1/2 : ℂ))) = (t : ℂ)^(-(1/2 : ℂ)) := by
      have he := Complex.ofReal_cpow ht.le (-(1/2 : ℝ))
      norm_num only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
        Complex.ofReal_ofNat] at he
      rw [← he]
      exact Complex.conj_ofReal _
    simp only [map_mul, map_inv₀, hg, hp, ← Complex.exp_conj, map_neg, Complex.conj_ofReal]
  · simp only [gammaHalfCausal, indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht), map_zero]

theorem causalExpThree_conj : (fun t => conj (causalExpThree t)) = causalExpThree := by
  funext t
  by_cases ht : 0 < t
  · simp [causalExpThree, ht, ← Complex.exp_conj,
      show conj (3 : ℂ) = 3 from Complex.conj_ofReal 3]
  · simp [causalExpThree, ht]

theorem convolution_conj_complex (f g : ℝ → ℂ) :
    (fun t => conj ((f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) t)) =
      (fun t => conj (f t)) ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun t => conj (g t)) := by
  funext t
  rw [convolution_def, ← integral_conj, convolution_def]
  apply integral_congr_ae
  filter_upwards [] with u
  exact map_mul (starRingEnd ℂ) (f u) (g (t-u))

theorem filteredGammaHalf_conj (w : ℂ) :
    (fun t => conj (filteredGammaHalf w t)) = filteredGammaHalf (conj w) := by
  funext t
  simp only [filteredGammaHalf, map_sub, map_mul]
  rw [show conj (3 : ℂ) = 3 from Complex.conj_ofReal 3,
    congrFun (gammaHalfCausal_conj w) t,
    congrFun (convolution_conj_complex causalExpThree (gammaHalfCausal w)) t,
    gammaHalfCausal_conj, causalExpThree_conj]

theorem conjugateGammaSource_real (t : ℝ) :
    (conjugateGammaSource t).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  unfold conjugateGammaSource
  rw [congrFun (convolution_conj_complex _ _) t, filteredGammaHalf_conj, filteredGammaHalf_conj]
  have hp : conj (1+2*Complex.I) = 1-2*Complex.I := by
    simp [show conj (2 : ℂ) = 2 from Complex.conj_ofReal 2, sub_eq_add_neg]
  have hm : conj (1-2*Complex.I) = 1+2*Complex.I := by
    simp [show conj (2 : ℂ) = 2 from Complex.conj_ofReal 2]
  rw [hp, hm]
  have h := convolution_flip (L := ContinuousLinearMap.mul ℂ ℂ) (μ := volume)
    (f := filteredGammaHalf (1+2*Complex.I)) (g := filteredGammaHalf (1-2*Complex.I))
  rw [ContinuousLinearMap.flip_mul] at h
  exact congrFun h t

theorem causalComplexLaplace_eq_ray (s : ℂ) {f : ℝ → ℂ}
    (hc : ∀ t ≤ 0, f t = 0) : causalComplexLaplace s f = bochnerLaplaceRay f s := by
  rw [causalComplexLaplace, bochnerLaplaceRay, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : 0 < t
  · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
    rfl
  · rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht)]
    simp [causalComplexLaplaceWeight, hc t (le_of_not_gt ht)]

theorem causalComplexLaplaceWeight_integrable_of_ray {s : ℂ} {f : ℝ → ℂ}
    (hc : ∀ t ≤ 0, f t = 0)
    (hi : IntegrableOn (fun t => expRay s t • f t) (Ioi 0)) :
    Integrable (causalComplexLaplaceWeight s f) := by
  have he : causalComplexLaplaceWeight s f = (Ioi 0).indicator
      (fun t => expRay s t • f t) := by
    funext t
    by_cases ht : 0 < t
    · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
      rfl
    · rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht)]
      simp [causalComplexLaplaceWeight, hc t (le_of_not_gt ht)]
  rw [he, integrable_indicator_iff measurableSet_Ioi]
  exact hi

def positiveCubicTransform (s : ℂ) : ℂ := ((s+1)^2+4)/(s+3)^4
def positiveCubicZero : ℂ := -1+2*Complex.I

theorem positiveCubicTransform_zero : positiveCubicTransform positiveCubicZero = 0 := by
  have he : (positiveCubicZero+1)^2+4 = 0 := by
    calc
      _ = 4*(Complex.I^2+1) := by unfold positiveCubicZero; ring
      _ = 0 := by simp [Complex.I_sq]
  rw [positiveCubicTransform, he, zero_div]

theorem hasDerivAt_positiveCubicTransform_zero :
    HasDerivAt positiveCubicTransform (4*Complex.I/(positiveCubicZero+3)^4)
      positiveCubicZero := by
  have hden : positiveCubicZero+3 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [positiveCubicZero] at hr
  have hn : HasDerivAt (fun s : ℂ => (s+1)^2+4)
      (2*(positiveCubicZero+1)) positiveCubicZero := by
    simpa using (((hasDerivAt_id positiveCubicZero).add_const 1).fun_pow 2).add_const 4
  have hd : HasDerivAt (fun s : ℂ => (s+3)^4)
      (4*(positiveCubicZero+3)^3) positiveCubicZero := by
    simpa using ((hasDerivAt_id positiveCubicZero).add_const 3).fun_pow 4
  have he : (2*(positiveCubicZero+1)*(positiveCubicZero+3)^4 -
      ((positiveCubicZero+1)^2+4)*(4*(positiveCubicZero+3)^3))/((positiveCubicZero+3)^4)^2 =
      4*Complex.I/(positiveCubicZero+3)^4 := by
    have hz : (positiveCubicZero+1)^2+4 = 0 := by
      calc
        _ = 4*(Complex.I^2+1) := by unfold positiveCubicZero; ring
        _ = 0 := by simp [Complex.I_sq]
    rw [hz, zero_mul, sub_zero]
    have hh : 2*(positiveCubicZero+1) = 4*Complex.I := by unfold positiveCubicZero; ring
    rw [hh]
    field_simp
  have h := hn.div hd (pow_ne_zero 4 hden)
  rw [he] at h
  exact h

theorem conjugateGammaSource_not_integrable_weighted :
    ¬ Integrable (causalComplexLaplaceWeight (-5/4) conjugateGammaSource) := by
  intro hi
  have hc : ∀ t ≤ 0, conjugateGammaSource t = 0 :=
    fun _ h => conjugateGammaSource_nonpos h
  have hray : IntegrableOn (fun t => expRay ((-5/4 : ℝ) : ℂ) t •
      conjugateGammaSource t) (Ioi 0) := by
    have hh : ((-5/4 : ℝ) : ℂ) = (-5/4 : ℂ) := by push_cast; rfl
    rw [hh]
    exact hi.integrableOn
  have hInt (s : ℂ) (hs : (-5/4 : ℝ) < s.re) :
      Integrable (causalComplexLaplaceWeight s conjugateGammaSource) :=
    causalComplexLaplaceWeight_integrable_of_ray hc
      (bochnerLaplaceRay_integrable conjugateGammaSource_integrable.aestronglyMeasurable
        hray s hs.le)
  have hsq (s : ℂ) (hs : (-5/4 : ℝ) < s.re) :
      causalComplexLaplace s conjugateGammaSource ^ 2 = positiveCubicTransform s := by
    calc
      _ = causalComplexLaplace s (conjugateGammaSource ⋆[ContinuousLinearMap.mul ℂ ℂ]
          conjugateGammaSource) := by
        conv_rhs => rw [causalComplexLaplace, causalComplexLaplaceWeight_convolution,
          integral_convolution (ContinuousLinearMap.mul ℂ ℂ) (hInt s hs) (hInt s hs)]
        change _ = causalComplexLaplace s conjugateGammaSource *
          causalComplexLaplace s conjugateGammaSource
        rw [pow_two]
      _ = causalComplexLaplace s positiveCubicCausal := by
        apply integral_congr_ae
        filter_upwards [conjugateGammaSource_convolution_self] with t ht
        simp only [causalComplexLaplaceWeight, ht]
      _ = _ := causalComplexLaplace_positiveCubic (by linarith)
  have hp : (-5/4 : ℝ) < positiveCubicZero.re := by norm_num [positiveCubicZero]
  have hz : causalComplexLaplace positiveCubicZero conjugateGammaSource = 0 :=
    (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp
      (by rw [hsq _ hp, positiveCubicTransform_zero])
  have hd : DifferentiableAt ℂ (fun s => causalComplexLaplace s conjugateGammaSource)
      positiveCubicZero := by
    simp_rw [causalComplexLaplace_eq_ray _ hc]
    exact bochnerLaplaceRay_differentiableAt
      conjugateGammaSource_integrable.aestronglyMeasurable hray _ hp
  have heq : (fun s => causalComplexLaplace s conjugateGammaSource ^ 2) =ᶠ[𝓝 positiveCubicZero]
      positiveCubicTransform := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hp] with s hs
    exact hsq s hs
  have he := ((hd.hasDerivAt.fun_pow 2).congr_of_eventuallyEq heq.symm).unique
    hasDerivAt_positiveCubicTransform_zero
  have hne : 4*Complex.I/(positiveCubicZero+3)^4 ≠ 0 := by
    apply div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
    apply pow_ne_zero
    intro h
    have hr := congrArg Complex.re h
    norm_num [positiveCubicZero] at hr
  apply hne
  simpa [hz] using he.symm

theorem causalComplexLaplaceWeight_comp (s z : ℂ) (f : ℝ → ℂ) :
    causalComplexLaplaceWeight s (causalComplexLaplaceWeight z f) =
      causalComplexLaplaceWeight (s+z) f := by
  funext t
  simp only [causalComplexLaplaceWeight, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

def growingGammaSource : ℝ → ℂ := causalComplexLaplaceWeight (-2) conjugateGammaSource

def decayingPositiveSquare (t : ℝ) : ℝ :=
  Real.exp (-t) * (t-2*t^2+(4/3)*t^3)

theorem growingGammaSource_nonpos {t : ℝ} (ht : t ≤ 0) :
    growingGammaSource t = 0 := by
  simp [growingGammaSource, causalComplexLaplaceWeight, conjugateGammaSource_nonpos ht]

theorem growingGammaSource_real (t : ℝ) : (growingGammaSource t).im = 0 := by
  have he : Complex.exp (-((-2 : ℂ)*t)) = (Real.exp (2*t) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  unfold growingGammaSource causalComplexLaplaceWeight
  rw [he, Complex.mul_im, conjugateGammaSource_real]
  simp only [Complex.ofReal_im, mul_zero, zero_mul, add_zero]

theorem growingGammaSource_integrable_weight_two :
    Integrable (causalComplexLaplaceWeight 2 growingGammaSource) := by
  rw [growingGammaSource, causalComplexLaplaceWeight_comp]
  have he : causalComplexLaplaceWeight (2 + -2) conjugateGammaSource = conjugateGammaSource := by
    funext t
    simp [causalComplexLaplaceWeight]
  rw [he]
  exact conjugateGammaSource_integrable

theorem growingGammaSource_not_integrable_weight_three_quarters :
    ¬ Integrable (causalComplexLaplaceWeight (3/4) growingGammaSource) := by
  rw [growingGammaSource, causalComplexLaplaceWeight_comp]
  rw [show (3/4 : ℂ)+ -2 = -5/4 by ring]
  exact conjugateGammaSource_not_integrable_weighted

theorem decayingPositiveSquare_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ decayingPositiveSquare t := by
  have hp : t-2*t^2+(4/3)*t^3 = t*((1-t)^2+t^2/3) := by ring
  rw [decayingPositiveSquare, hp]
  positivity

theorem decayingPositiveSquare_pos {t : ℝ} (ht : 0 < t) :
    0 < decayingPositiveSquare t := by
  have hp : t-2*t^2+(4/3)*t^3 = t*((1-t)^2+t^2/3) := by ring
  rw [decayingPositiveSquare, hp]
  positivity

theorem tendsto_decayingPositiveSquare : Tendsto decayingPositiveSquare atTop (𝓝 0) := by
  have h := ((tendsto_pow_mul_exp_neg_mul_atTop (by norm_num : (0:ℝ)<1) 1).sub
    ((tendsto_pow_mul_exp_neg_mul_atTop (by norm_num : (0:ℝ)<1) 2).const_mul 2)).add
    ((tendsto_pow_mul_exp_neg_mul_atTop (by norm_num : (0:ℝ)<1) 3).const_mul (4/3))
  have heq : decayingPositiveSquare = fun t : ℝ => t^1*Real.exp (-(1*t)) -
      2*(t^2*Real.exp (-(1*t))) + (4/3)*(t^3*Real.exp (-(1*t))) := by
    funext t
    simp only [decayingPositiveSquare, pow_one, one_mul]
    ring
  rw [heq]
  simpa only [mul_zero, sub_zero, zero_add] using h

theorem weighted_positiveCubic_eq_decaying :
    causalComplexLaplaceWeight (-2) positiveCubicCausal =
      (Ioi 0).indicator (fun t => (decayingPositiveSquare t : ℂ)) := by
  funext t
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · simp only [causalComplexLaplaceWeight, positiveCubicCausal, indicator_of_mem ht,
      positiveCubicKernel, decayingPositiveSquare]
    push_cast
    have he : Complex.exp (-((-2 : ℂ)*t)) * Complex.exp (-(3*(t : ℂ))) =
        Complex.exp (-(t : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [← mul_assoc, he]
  · simp only [causalComplexLaplaceWeight, positiveCubicCausal, indicator_of_notMem ht, mul_zero]

theorem growingGammaSource_convolution_self :
    (growingGammaSource ⋆[ContinuousLinearMap.mul ℂ ℂ] growingGammaSource) =ᵐ[volume]
      (Ioi 0).indicator (fun t => (decayingPositiveSquare t : ℂ)) := by
  rw [growingGammaSource, ← causalComplexLaplaceWeight_convolution,
    ← weighted_positiveCubic_eq_decaying]
  filter_upwards [conjugateGammaSource_convolution_self] with t ht
  simp only [causalComplexLaplaceWeight, ht]

theorem decayingPositiveSquare_integrable :
    Integrable ((Ioi (0 : ℝ)).indicator (fun t => (decayingPositiveSquare t : ℂ))) := by
  rw [← weighted_positiveCubic_eq_decaying]
  have he : causalComplexLaplaceWeight (-2) positiveCubicCausal = (Ioi 0).indicator
      (fun t : ℝ => Complex.exp (-((-2 : ℂ)*t)) * (positiveCubicKernel t : ℂ)) := by
    funext t
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · simp only [causalComplexLaplaceWeight, positiveCubicCausal, indicator_of_mem ht]
    · simp only [causalComplexLaplaceWeight, positiveCubicCausal, indicator_of_notMem ht, mul_zero]
  rw [he, integrable_indicator_iff measurableSet_Ioi]
  exact integrableOn_positiveCubicKernel_integrand (by norm_num)

/-- A real causal source can have a nonnegative decaying convolution square without
absolute Laplace convergence at `3/4`, despite absolute convergence at `2`. -/
theorem exists_real_causal_positive_square_without_weighted_integrability :
    ∃ g : ℝ → ℂ, (∀ t, (g t).im = 0) ∧ (∀ t ≤ 0, g t = 0) ∧
      Integrable (causalComplexLaplaceWeight 2 g) ∧
      ¬ Integrable (causalComplexLaplaceWeight (3/4) g) ∧
      ∃ K : ℝ → ℝ, (∀ t ≥ 0, 0 ≤ K t) ∧ (∀ t > 0, 0 < K t) ∧
        Tendsto K atTop (𝓝 0) ∧ Integrable ((Ioi 0).indicator (fun t => (K t : ℂ))) ∧
        (g ⋆[ContinuousLinearMap.mul ℂ ℂ] g) =ᵐ[volume]
          (Ioi 0).indicator (fun t => (K t : ℂ)) :=
  ⟨growingGammaSource, growingGammaSource_real, fun _ h => growingGammaSource_nonpos h,
    growingGammaSource_integrable_weight_two,
    growingGammaSource_not_integrable_weight_three_quarters,
    decayingPositiveSquare, fun _ h => decayingPositiveSquare_nonneg h,
    fun _ h => decayingPositiveSquare_pos h, tendsto_decayingPositiveSquare,
    decayingPositiveSquare_integrable, growingGammaSource_convolution_self⟩

end GaloisForLFunctions.HTGeometry

