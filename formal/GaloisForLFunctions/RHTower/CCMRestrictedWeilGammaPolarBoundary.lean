import GaloisForLFunctions.RHTower.CCMActualHeadGammaAutocorrelationEnergy
import GaloisForLFunctions.RHTower.DigammaIntegralRepresentation
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPrimeOuterShell

/-!
# Exact Gamma jump boundary for the truncated pole profile

The actual compressed translation increment on `exp(x/2)` has an explicit scalar
jump kernel. It splits into an integrable universal Gauss core, a finite interval
term, and two positive endpoint tails. This gives the exact Hardy-phase-normalized
integral `-R - EulerGamma - log(2*pi) + B(R,L)`, where
`B(R,L) = -log(1-exp(-2R))/2 - log(tanh(L/2))/2` is strictly positive.

The core is proved strictly between zero and one, and its mass is evaluated from
integrable Gauss differences. No divergent integrals are separated. These source
and integral identities do not assume or establish Friedrichs operator-domain
membership of the truncated pole profile, or the sign needed for RH.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal InnerProduct
noncomputable section
namespace RHTower

private def geometricKernel (h : ℝ) : ℝ :=
  Real.exp (-h) / (1-Real.exp (-h))

/-- The integrable universal part of the Gamma action on the positive pole profile. -/
def ccmGammaPolarCore (h : ℝ) : ℝ :=
  2 * ccmGammaTranslationDensity h - geometricKernel h

private theorem real_gauss (s t : ℝ) :
    (gaussLaplaceKernel (s : ℂ) t).re =
      (Real.exp (-t) - Real.exp (-s*t)) / (1 - Real.exp (-t)) := by
  unfold gaussLaplaceKernel
  have hmul : -(s : ℂ) * (t : ℂ) = ((-s*t : ℝ) : ℂ) := by push_cast; ring
  rw [hmul, ← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
  norm_cast

private theorem core_gauss (h : ℝ) :
    ccmGammaPolarCore h =
      -2 * (gaussLaplaceKernel ((1/4 : ℝ) : ℂ) (2*h)).re +
        (gaussLaplaceKernel ((1/2 : ℝ) : ℂ) (2*h)).re := by
  rw [real_gauss, real_gauss, ccmGammaPolarCore, ccmGammaTranslationDensity, geometricKernel]
  rw [show -(1/4:ℝ)*(2*h)= -(h/2) by ring,
    show -(1/2:ℝ)*(2*h)= -h by ring]
  have he : Real.exp (-(2*h)) = Real.exp (-h) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  by_cases hh : h=0
  · subst h; norm_num
  · have hn : Real.exp (-h) ≠ 1 := by
      intro heq
      have hz : -h = 0 := Real.exp_injective (by simpa using heq)
      exact hh (by linarith)
    have hp : 1 + Real.exp (-h) ≠ 0 := by positivity
    have hn2 : 1 - Real.exp (-h)^2 ≠ 0 := by
      have heq : 1 - Real.exp (-h)^2 = (1-Real.exp (-h))*(1+Real.exp (-h)) := by ring
      rw [heq]
      exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hn)) hp
    field_simp
    ring

private theorem gauss_real_integrable (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun h => (gaussLaplaceKernel (s : ℂ) (2*h)).re) (Ioi (0 : ℝ)) volume := by
  have hc := integrableOn_gaussLaplaceKernel (s := (s : ℂ)) (by simpa using hs)
  have hr : IntegrableOn (fun t => (gaussLaplaceKernel (s : ℂ) t).re) (Ioi (0:ℝ)) volume :=
    Complex.reCLM.integrable_comp hc
  have hscale := (integrableOn_Ioi_comp_mul_left_iff
    (fun t => (gaussLaplaceKernel (s : ℂ) t).re) 0 (by norm_num : (0:ℝ)<2)).mpr
      (by simpa only [mul_zero] using hr)
  exact hscale

/-- Absolute integrability follows from two genuine Gauss differences, without splitting
any divergent exponential term at the origin. -/
theorem integrableOn_ccmGammaPolarCore :
    IntegrableOn ccmGammaPolarCore (Ioi (0 : ℝ)) volume := by
  have hq := gauss_real_integrable (1/4) (by norm_num)
  have hh := gauss_real_integrable (1/2) (by norm_num)
  exact ((hq.const_mul (-2)).add hh).congr
    (Eventually.of_forall fun x => (core_gauss x).symm)

private theorem gauss_real_integral (s : ℝ) (hs : 0 < s) :
    (∫ h in Ioi (0 : ℝ), (gaussLaplaceKernel (s : ℂ) (2*h)).re) =
      (1/2) * ((Complex.digamma (s : ℂ)).re + Real.eulerMascheroniConstant) := by
  rw [integral_comp_mul_left_Ioi (fun t => (gaussLaplaceKernel (s : ℂ) t).re)
    0 (by norm_num : (0:ℝ)<2)]
  simp only [mul_zero, smul_eq_mul]
  have hc := integrableOn_gaussLaplaceKernel (s := (s : ℂ)) (by simpa using hs)
  have hreal : (∫ t in Ioi (0:ℝ), (gaussLaplaceKernel (s : ℂ) t).re) =
      (∫ t in Ioi (0:ℝ), gaussLaplaceKernel (s : ℂ) t).re :=
    Complex.reCLM.integral_comp_comm hc
  rw [hreal, integral_gaussLaplaceKernel_eq_tsum (by simpa using hs)]
  have hpsi := digamma_eq_neg_euler_add_tsum_gauss (s := (s : ℂ)) (by simpa using hs)
  have hre := congrArg Complex.re hpsi
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re] at hre
  norm_num
  linarith

/-- Exact Gamma core mass, in the actual phase normalization. -/
theorem integral_ccmGammaPolarCore :
    (∫ h in Ioi (0 : ℝ), ccmGammaPolarCore h) =
      -(Complex.digamma (1/4 : ℂ)).re - Real.eulerMascheroniConstant - Real.log 2 := by
  have hq := gauss_real_integrable (1/4) (by norm_num)
  have hh := gauss_real_integrable (1/2) (by norm_num)
  have heq : (∫ h in Ioi (0:ℝ), ccmGammaPolarCore h) =
      -2 * (∫ h in Ioi (0:ℝ), (gaussLaplaceKernel ((1/4:ℝ):ℂ) (2*h)).re) +
        (∫ h in Ioi (0:ℝ), (gaussLaplaceKernel ((1/2:ℝ):ℂ) (2*h)).re) := by
    simp_rw [core_gauss]
    rw [integral_add (hq.const_mul (-2)) hh, integral_const_mul]
  rw [heq, gauss_real_integral _ (by norm_num), gauss_real_integral _ (by norm_num)]
  have hhalf : (Complex.digamma ((1/2:ℝ):ℂ)).re =
      -2*Real.log 2 - Real.eulerMascheroniConstant := by
    have he := congrArg Complex.re Complex.digamma_one_half
    simpa [Complex.log_re] using he
  rw [hhalf]
  push_cast
  ring

/-- The universal core is strictly between zero and one on the positive ray. -/
theorem ccmGammaPolarCore_pos_lt_one {h : ℝ} (hh : 0 < h) :
    0 < ccmGammaPolarCore h ∧ ccmGammaPolarCore h < 1 := by
  let t := Real.exp (-(h/2))
  have ht : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have ht2 : Real.exp (-h)=t^2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have ht4 : Real.exp (-(2*h))=t^4 := by
    rw [show (4:ℕ)=2*2 by norm_num, pow_mul, ← ht2, pow_two, ← Real.exp_add]
    congr 1
    ring
  have heq : ccmGammaPolarCore h = t*(t^2+t+2)/((1+t)*(1+t^2)) := by
    unfold ccmGammaPolarCore ccmGammaTranslationDensity geometricKernel
    rw [ht2, ht4]
    change 2*(t/(1-t^4)) - t^2/(1-t^2) = _
    have hden2 : 1-t^2 ≠ 0 := by nlinarith
    have hden4 : 1-t^4 ≠ 0 := by
      have hsq : t^2 < 1 := by nlinarith
      nlinarith [sq_nonneg (t^2)]
    have hden : (1+t)*(1+t^2) ≠ 0 := by positivity
    field_simp
    ring
  rw [heq]
  constructor
  · positivity
  · apply (div_lt_iff₀ (by positivity : 0<(1+t)*(1+t^2))).mpr
    nlinarith

private theorem geometric_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn geometricKernel (Ioi r) volume := by
  apply Integrable.of_integral_ne_zero
  change (∫ h in Ioi r, Real.exp (-h)/(1-Real.exp (-h))) ≠ 0
  rw [integral_geometricGaussKernel_Ioi hr]
  have hlog : Real.log (1-Real.exp (-r)) < 0 :=
    Real.log_neg (one_sub_exp_neg_pos hr) (by linarith [Real.exp_pos (-r)])
  linarith

private theorem geometric_scaled_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun h => geometricKernel (2*h)) (Ioi r) volume :=
  (integrableOn_Ioi_comp_mul_left_iff geometricKernel r (by norm_num : (0:ℝ)<2)).mpr
    (geometric_integrable (by linarith))

private theorem geometric_scaled_integral {r : ℝ} (hr : 0 < r) :
    (∫ h in Ioi r, geometricKernel (2*h)) =
      -(1/2)*Real.log (1-Real.exp (-(2*r))) := by
  rw [integral_comp_mul_left_Ioi geometricKernel r (by norm_num : (0:ℝ)<2)]
  change (2:ℝ)⁻¹ * (∫ h in Ioi (2*r), Real.exp (-h)/(1-Real.exp (-h))) = _
  rw [integral_geometricGaussKernel_Ioi (by linarith)]
  ring

private theorem reciprocal_sinh_eq (h : ℝ) :
    Real.exp (-h)/(1-Real.exp (-(2*h))) = geometricKernel h - geometricKernel (2*h) := by
  unfold geometricKernel
  have he : Real.exp (-(2*h))=Real.exp (-h)^2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  by_cases hh : h=0
  · subst h; norm_num
  · have hn : Real.exp (-h) ≠ 1 := by
      intro heq
      have hz : -h=0 := Real.exp_injective (by simpa using heq)
      exact hh (by linarith)
    have hp : 1+Real.exp (-h) ≠ 0 := by positivity
    have hn2 : 1-Real.exp (-h)^2 ≠ 0 := by
      rw [show 1-Real.exp (-h)^2=(1-Real.exp (-h))*(1+Real.exp (-h)) by ring]
      exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hn)) hp
    field_simp
    ring

/-- The boundary term has only ordinary positive-cutoff logarithms. -/
def ccmGammaPolarBoundary (R L : ℝ) : ℝ :=
  -(1/2)*Real.log (1-Real.exp (-(2*R))) - Real.log (1-Real.exp (-L)) +
    (1/2)*Real.log (1-Real.exp (-(2*L)))

/-- Exact integral of the second endpoint tail. -/
theorem integral_ccmGammaPolar_leftTail {L : ℝ} (hL : 0 < L) :
    (∫ h in Ioi L, Real.exp (-h)/(1-Real.exp (-(2*h)))) =
      -Real.log (1-Real.exp (-L)) + (1/2)*Real.log (1-Real.exp (-(2*L))) := by
  simp_rw [reciprocal_sinh_eq]
  rw [integral_sub (geometric_integrable hL) (geometric_scaled_integrable hL),
    geometric_scaled_integral hL]
  change (∫ h in Ioi L, Real.exp (-h)/(1-Real.exp (-h))) - _ = _
  rw [integral_geometricGaussKernel_Ioi hL]
  ring

/-- Both endpoint contributions are positive at every strict interior point. -/
theorem ccmGammaPolarBoundary_pos {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    0 < ccmGammaPolarBoundary R L := by
  have hpR := one_sub_exp_neg_pos (by linarith : 0<2*R)
  have hpL := one_sub_exp_neg_pos hL
  have hp2L := one_sub_exp_neg_pos (by linarith : 0<2*L)
  have hnR : Real.log (1-Real.exp (-(2*R))) < 0 :=
    Real.log_neg hpR (by linarith [Real.exp_pos (-(2*R))])
  have hnL : Real.log (1-Real.exp (-L)) < 0 :=
    Real.log_neg hpL (by linarith [Real.exp_pos (-L)])
  have hmono : Real.log (1-Real.exp (-L)) ≤ Real.log (1-Real.exp (-(2*L))) := by
    apply Real.log_le_log hpL
    have he := Real.exp_le_exp.mpr (by linarith : -(2*L) ≤ -L)
    linarith
  unfold ccmGammaPolarBoundary
  linarith

/-- The actual positive-pole ratio in the physical Gamma jump integral, with the two
hard endpoint cutoffs still present. -/
def ccmGammaPolarJumpKernel (R L h : ℝ) : ℝ :=
  ccmGammaTranslationDensity h *
    (2 - (if h ≤ R then Real.exp (h/2) else 0) -
      (if h ≤ L then Real.exp (-(h/2)) else 0))

private theorem jump_decomposition (R L : ℝ) {h : ℝ} (hh : 0 < h) :
    ccmGammaPolarJumpKernel R L h = ccmGammaPolarCore h -
      (Ioc (0:ℝ) R).indicator (fun _ => (1:ℝ)) h +
        (Ioi R).indicator (fun h => geometricKernel (2*h)) h +
          (Ioi L).indicator (fun h => Real.exp (-h)/(1-Real.exp (-(2*h)))) h := by
  have hden : 1-Real.exp (-(2*h)) ≠ 0 := ne_of_gt (one_sub_exp_neg_pos (by linarith))
  have hp : ccmGammaTranslationDensity h * Real.exp (h/2) =
      1 + geometricKernel (2*h) := by
    unfold ccmGammaTranslationDensity geometricKernel
    have he : Real.exp (-(h/2))*Real.exp (h/2)=1 := by rw [← Real.exp_add]; simp
    rw [div_mul_eq_mul_div, he]
    apply (div_eq_iff hden).mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ hden]
    ring
  have hm : ccmGammaTranslationDensity h * Real.exp (-(h/2)) =
      Real.exp (-h)/(1-Real.exp (-(2*h))) := by
    unfold ccmGammaTranslationDensity
    rw [div_mul_eq_mul_div, ← Real.exp_add]
    congr 2
    ring
  have hgeom := reciprocal_sinh_eq h
  unfold ccmGammaPolarJumpKernel ccmGammaPolarCore
  by_cases hR : h ≤ R <;> by_cases hL : h ≤ L
  · simp only [hR, hL, if_true, indicator_of_mem (show h ∈ Ioc (0:ℝ) R from ⟨hh,hR⟩),
      indicator_of_notMem (show h ∉ Ioi R from not_lt.mpr hR),
      indicator_of_notMem (show h ∉ Ioi L from not_lt.mpr hL), add_zero]
    nlinarith [hp, hm, hgeom]
  · simp only [hR, hL, if_true, if_false, sub_zero,
      indicator_of_mem (show h ∈ Ioc (0:ℝ) R from ⟨hh,hR⟩),
      indicator_of_notMem (show h ∉ Ioi R from not_lt.mpr hR),
      indicator_of_mem (show h ∈ Ioi L from lt_of_not_ge hL), add_zero]
    nlinarith [hp, hgeom]
  · simp only [hR, hL, if_true, if_false, sub_zero,
      indicator_of_notMem (show h ∉ Ioc (0:ℝ) R from fun hmem => hR hmem.2),
      indicator_of_mem (show h ∈ Ioi R from lt_of_not_ge hR),
      indicator_of_notMem (show h ∉ Ioi L from not_lt.mpr hL), add_zero]
    nlinarith [hm, hgeom]
  · simp only [hR, hL, if_false, sub_zero,
      indicator_of_notMem (show h ∉ Ioc (0:ℝ) R from fun hmem => hR hmem.2),
      indicator_of_mem (show h ∈ Ioi R from lt_of_not_ge hR),
      indicator_of_mem (show h ∈ Ioi L from lt_of_not_ge hL)]
    nlinarith [hgeom]

private theorem positive_tail_integrable {r : ℝ} (hr : 0 ≤ r) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi r) volume) :
    IntegrableOn ((Ioi r).indicator f) (Ioi (0:ℝ)) volume := by
  rw [integrableOn_indicator_iff measurableSet_Ioi, Ioi_inter_Ioi, max_eq_left hr]
  exact hf

private theorem positive_tail_integral {r : ℝ} (hr : 0 ≤ r) (f : ℝ → ℝ) :
    (∫ h in Ioi (0:ℝ), (Ioi r).indicator f h) = ∫ h in Ioi r, f h := by
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hr]

private theorem cutoff_one_integrable (R : ℝ) :
    IntegrableOn ((Ioc (0:ℝ) R).indicator (fun _ => (1:ℝ))) (Ioi (0:ℝ)) volume := by
  rw [integrableOn_indicator_iff measurableSet_Ioc,
    inter_eq_left.mpr (show Ioc (0:ℝ) R ⊆ Ioi (0:ℝ) from fun _ h => h.1)]
  exact integrableOn_const (by simp [Real.volume_Ioc])

private theorem cutoff_one_integral {R : ℝ} (hR : 0 ≤ R) :
    (∫ h in Ioi (0:ℝ), (Ioc (0:ℝ) R).indicator (fun _ => (1:ℝ)) h) = R := by
  rw [setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.mpr (show Ioc (0:ℝ) R ⊆ Ioi (0:ℝ) from fun _ h => h.1), setIntegral_const]
  simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal hR]

private theorem left_tail_integrable {L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun h => Real.exp (-h)/(1-Real.exp (-(2*h)))) (Ioi L) volume := by
  simp_rw [reciprocal_sinh_eq]
  exact (geometric_integrable hL).sub (geometric_scaled_integrable hL)

/-- Absolute integrability of the complete pole-profile Gamma jump kernel. -/
theorem integrableOn_ccmGammaPolarJumpKernel {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    IntegrableOn (ccmGammaPolarJumpKernel R L) (Ioi (0:ℝ)) volume := by
  have hsum := ((integrableOn_ccmGammaPolarCore.sub (cutoff_one_integrable R)).add
    (positive_tail_integrable hR.le (geometric_scaled_integrable hR))).add
      (positive_tail_integrable hL.le (left_tail_integrable hL))
  refine hsum.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  exact (jump_decomposition R L hh).symm

/-- Exact Gamma jump integral: interval length, universal core mass, and both endpoint tails. -/
theorem integral_ccmGammaPolarJumpKernel {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    (∫ h in Ioi (0:ℝ), ccmGammaPolarJumpKernel R L h) =
      -R - (Complex.digamma (1/4 : ℂ)).re - Real.eulerMascheroniConstant - Real.log 2 +
        ccmGammaPolarBoundary R L := by
  have hRint := positive_tail_integrable hR.le (geometric_scaled_integrable hR)
  have hLint := positive_tail_integrable hL.le (left_tail_integrable hL)
  have hcore := integrableOn_ccmGammaPolarCore.sub (cutoff_one_integrable R)
  have heq : (∫ h in Ioi (0:ℝ), ccmGammaPolarJumpKernel R L h) =
      ∫ h in Ioi (0:ℝ), ccmGammaPolarCore h -
        (Ioc (0:ℝ) R).indicator (fun _ => (1:ℝ)) h +
          (Ioi R).indicator (fun h => geometricKernel (2*h)) h +
            (Ioi L).indicator (fun h => Real.exp (-h)/(1-Real.exp (-(2*h)))) h := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro h hh
    exact jump_decomposition R L hh
  have hadd1 := integral_add (hcore.add hRint) hLint
  have hadd2 := integral_add hcore hRint
  have hsub := integral_sub integrableOn_ccmGammaPolarCore (cutoff_one_integrable R)
  simp only [Pi.add_apply, Pi.sub_apply] at hadd1 hadd2 hsub
  rw [heq, hadd1, hadd2, hsub,
    cutoff_one_integral hR.le, integral_ccmGammaPolarCore,
    positive_tail_integral hR.le, positive_tail_integral hL.le,
    geometric_scaled_integral hR, integral_ccmGammaPolar_leftTail hL]
  unfold ccmGammaPolarBoundary
  ring

/-- The physical Gamma ratio is normalized by the actual Hardy phase, with the predicted
constant and explicit positive endpoint term. This is an integral identity, not yet an
assertion of Friedrichs operator-domain membership of the truncated profile. -/
theorem ccmGammaPolarJump_actualPhase {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    2*gammaHardyPhaseRate 0 + (∫ h in Ioi (0:ℝ), ccmGammaPolarJumpKernel R L h) =
      -R - Real.eulerMascheroniConstant - Real.log (2*Real.pi) + ccmGammaPolarBoundary R L := by
  rw [integral_ccmGammaPolarJumpKernel hR hL]
  have hg : 2*gammaHardyPhaseRate 0 = (Complex.digamma (1/4 : ℂ)).re - Real.log Real.pi := by
    unfold gammaHardyPhaseRate linePt
    norm_num
    ring
  rw [hg, Real.log_mul (by norm_num : (2:ℝ)≠0) (ne_of_gt Real.pi_pos)]
  ring

/-- The exact jump kernel is the pointwise representative of the actual compressed
Gamma translation increment acting on the positive pole profile. -/
theorem ccmGammaPolarJump_source_coeFn (a : SuzukiPositiveAperture)
    {h : ℝ} (hh : 0 < h) :
    (((ccmGammaTranslationDensity h : ℂ) •
      ((2:ℂ) • ccmPolarApertureVector a (1/2) -
        ccmApertureCompression a (ccmSymmetricLogTranslation h)
          (ccmPolarApertureVector a (1/2))) : suzukiApertureHilbert a) : SoninL2) =ᵐ[volume]
      (centralInterval a.1).indicator (fun x => (Real.exp (x/2) : ℂ) *
        (ccmGammaPolarJumpKernel (a.1-x) (a.1+x) h : ℂ)) := by
  let p := ccmPolarApertureVector a (1/2)
  let S := ccmApertureCompression a (ccmSymmetricLogTranslation h)
  let d : SoninL2 := (2:ℂ) • p.1 - (S p : SoninL2)
  change (fun x => ((ccmGammaTranslationDensity h : ℂ) • d) x) =ᵐ[volume] _
  have hp := (ccmPolarL2Vector_coeFn a (1/2)).comp_tendsto
    (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae
  have hm := (ccmPolarL2Vector_coeFn a (1/2)).comp_tendsto
    (MellinL2.realTranslation_measurePreserving (-h)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [Lp.coeFn_smul (ccmGammaTranslationDensity h : ℂ) d,
    Lp.coeFn_sub ((2:ℂ) • p.1) (S p : SoninL2), Lp.coeFn_smul (2:ℂ) p.1,
    ccmApertureSymmetricTranslation_coeFn a h p,
    ccmPolarL2Vector_coeFn a (1/2), hp, hm] with x hr hd htwo hs hx hxp hxm
  rw [hr]
  change (ccmGammaTranslationDensity h : ℂ) * d x = _
  rw [hd]
  change (ccmGammaTranslationDensity h : ℂ) * (((2:ℂ) • p.1) x - (S p : SoninL2) x) = _
  rw [htwo]
  change (ccmGammaTranslationDensity h : ℂ) * (2*p.1 x - (S p : SoninL2) x) = _
  change p.1 x = _ at hx
  rw [hs, hx]
  change (ccmPolarL2Vector a (1/2)) (x+h) =
    (centralInterval a.1).indicator (ccmPolarProfile (1/2)) (x+h) at hxp
  change (ccmPolarL2Vector a (1/2)) (x+ -h) =
    (centralInterval a.1).indicator (ccmPolarProfile (1/2)) (x+ -h) at hxm
  by_cases hmem : x ∈ centralInterval a.1
  · rw [indicator_of_mem hmem, indicator_of_mem hmem, indicator_of_mem hmem]
    change -a.1 ≤ x ∧ x ≤ a.1 at hmem
    change (ccmGammaTranslationDensity h : ℂ) *
      (2*ccmPolarProfile (1/2) x - ((ccmPolarL2Vector a (1/2)) (x+h) +
        (ccmPolarL2Vector a (1/2)) (x-h))) = _
    rw [hxp, show x-h=x+ -h by ring, hxm]
    have hplus : x+h ∈ centralInterval a.1 ↔ h ≤ a.1-x := by
      change (-a.1 ≤ x+h ∧ x+h ≤ a.1) ↔ _
      constructor
      · intro hz; linarith [hz.2]
      · intro hz; constructor <;> linarith [hmem.1]
    have hminus : x+ -h ∈ centralInterval a.1 ↔ h ≤ a.1+x := by
      change (-a.1 ≤ x+ -h ∧ x+ -h ≤ a.1) ↔ _
      constructor
      · intro hz; linarith [hz.1]
      · intro hz; constructor <;> linarith [hmem.2]
    have heplus : ccmPolarProfile (1/2) (x+h) =
        (Real.exp (x/2) : ℂ)*(Real.exp (h/2) : ℂ) := by
      unfold ccmPolarProfile
      rw [show (1/2:ℝ)*(x+h)=x/2+h/2 by ring, Real.exp_add, Complex.ofReal_mul]
    have heminus : ccmPolarProfile (1/2) (x+ -h) =
        (Real.exp (x/2) : ℂ)*(Real.exp (-(h/2)) : ℂ) := by
      unfold ccmPolarProfile
      rw [show (1/2:ℝ)*(x+ -h)=x/2+ -(h/2) by ring, Real.exp_add, Complex.ofReal_mul]
    simp only [Set.indicator, hplus, hminus]
    simp only [heplus, heminus]
    simp only [ccmPolarProfile, show (1/2:ℝ)*x=x/2 by ring, ccmGammaPolarJumpKernel]
    split_ifs <;> push_cast <;> ring
  · rw [indicator_of_notMem hmem, indicator_of_notMem hmem, indicator_of_notMem hmem]
    ring

/-- The endpoint tail formula equals the logarithmic boundary profile predicted by
its two elementary antiderivatives. -/
theorem ccmGammaPolarBoundary_eq_log_tanh (R : ℝ) {L : ℝ} (hL : 0 < L) :
    ccmGammaPolarBoundary R L =
      -(1/2)*Real.log (1-Real.exp (-(2*R))) - (1/2)*Real.log (Real.tanh (L/2)) := by
  have hp : 0 < 1-Real.exp (-L) := one_sub_exp_neg_pos hL
  have hq : 0 < 1+Real.exp (-L) := by positivity
  have he : Real.exp (-(2*L))=Real.exp (-L)^2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hprod : 1-Real.exp (-(2*L))=(1-Real.exp (-L))*(1+Real.exp (-L)) := by
    rw [he]
    ring
  have ht : Real.tanh (L/2) = (1-Real.exp (-L))/(1+Real.exp (-L)) := by
    rw [Real.tanh_eq]
    apply (div_eq_div_iff (by positivity) (ne_of_gt hq)).mpr
    have hmul : Real.exp (L/2)*Real.exp (-L)=Real.exp (-(L/2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    nlinarith
  unfold ccmGammaPolarBoundary
  rw [hprod, Real.log_mul (ne_of_gt hp) (ne_of_gt hq), ht,
    Real.log_div (ne_of_gt hp) (ne_of_gt hq)]
  ring
end RHTower
