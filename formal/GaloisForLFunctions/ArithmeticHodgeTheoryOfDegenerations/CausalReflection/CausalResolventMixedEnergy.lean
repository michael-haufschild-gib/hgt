import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ModulatedCausalReflectionEnergy

/-!
# Positive mixed energy of a weighted causal resolvent

Expanding the reflection norm identity identifies the real mixed term.
Modulation preserves that term, while an exponential weight shifts the
decay rate. In particular, an undamped resolvent has positive mixed energy
after every positive exponential weight.
-/

noncomputable section
open MeasureTheory Filter
open scoped Convolution

namespace GaloisForLFunctions.HTGeometry
open _root_.RHTower

private theorem norm_sq_add_complex (z w : ℂ) :
    ‖z + w‖ ^ 2 = ‖z‖ ^ 2 + 2 * ((starRingEnd ℂ) z * w).re + ‖w‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The real mixed product of two actual square-integrable profiles is integrable. -/
theorem integrable_real_conj_mul_of_memLp_two {f g : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun u => ((starRingEnd ℂ) (f u) * g u).re) := by
  have hfi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hgi := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hfg : Integrable (fun u => ‖f u + g u‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (hf.add hg).aestronglyMeasurable).mp (hf.add hg)
  apply (((hfg.sub hfi).sub hgi).const_mul (1 / 2 : ℝ)).congr
  refine Eventually.of_forall fun u => ?_
  change (1 / 2 : ℝ) * (‖f u + g u‖ ^ 2 - ‖f u‖ ^ 2 - ‖g u‖ ^ 2) = _
  rw [norm_sq_add_complex]
  ring

private theorem integral_norm_sq_add_complex {f g : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    (∫ u, ‖f u + g u‖ ^ 2) = (∫ u, ‖f u‖ ^ 2) +
      2 * (∫ u, ((starRingEnd ℂ) (f u) * g u).re) + ∫ u, ‖g u‖ ^ 2 := by
  have hfi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hgi := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hc := integrable_real_conj_mul_of_memLp_two hf hg
  calc
    _ = ∫ u, ‖f u‖ ^ 2 + 2 * ((starRingEnd ℂ) (f u) * g u).re + ‖g u‖ ^ 2 :=
      integral_congr_ae (Eventually.of_forall fun u => norm_sq_add_complex (f u) (g u))
    _ = (∫ u, ‖f u‖ ^ 2 + 2 * ((starRingEnd ℂ) (f u) * g u).re) +
        ∫ u, ‖g u‖ ^ 2 := integral_add (hfi.add (hc.const_mul 2)) hgi
    _ = ((∫ u, ‖f u‖ ^ 2) + ∫ u, 2 * ((starRingEnd ℂ) (f u) * g u).re) +
        ∫ u, ‖g u‖ ^ 2 :=
      congrArg (fun y : ℝ => y + ∫ u, ‖g u‖ ^ 2) (integral_add hfi (hc.const_mul 2))
    _ = _ := by rw [integral_const_mul]

/-- The real mixed term of an actual causal resolvent is its rate times its energy. -/
theorem integral_causalConvolution_mixed_energy {a : ℝ} (ha : 0 < a)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    (∫ u, ((starRingEnd ℂ) (f u) *
      (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) u).re) =
      a * ∫ u, ‖(causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) u‖ ^ 2 := by
  let g := causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f
  have hg : MemLp g 2 volume := memLp_causalExponentialConvolution ha hf
  have hp : 0 < -(1 / 2 : ℝ) + (a + 1 / 2) := by linarith only [ha]
  have he := integral_causalExponential_reflection_energy
    (a := -(1 / 2 : ℝ)) (x := a + 1 / 2) hp hf
  simp only [show -(1 / 2 : ℝ) + (a + 1 / 2) = a by ring] at he
  change (∫ u, ‖f u‖ ^ 2) =
    (∫ u, ‖-f u + (2 * (-(1 / 2 : ℝ)) : ℂ) * g u‖ ^ 2) +
      (4 * (-(1 / 2 : ℝ)) * (a + 1 / 2)) * ∫ u, ‖g u‖ ^ 2 at he
  have hr : (∫ u, ‖-f u + (2 * (-(1 / 2 : ℝ)) : ℂ) * g u‖ ^ 2) =
      ∫ u, ‖f u + g u‖ ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    change ‖-f u + (2 * (-(1 / 2 : ℝ)) : ℂ) * g u‖ ^ 2 = ‖f u + g u‖ ^ 2
    have hh : -f u + (2 * (-(1 / 2 : ℝ)) : ℂ) * g u = -(f u + g u) := by
      push_cast
      ring
    rw [hh, norm_neg]
  rw [hr, integral_norm_sq_add_complex hf hg] at he
  change (∫ u, ((starRingEnd ℂ) (f u) * g u).re) = a * ∫ u, ‖g u‖ ^ 2
  nlinarith only [he]

private theorem real_conj_mul_causalModulation (b : ℝ) (f g : ℝ → ℂ) (u : ℝ) :
    ((starRingEnd ℂ) (causalModulation b f u) * causalModulation b g u).re =
      ((starRingEnd ℂ) (f u) * g u).re := by
  have hs : causalModulation b f u + causalModulation b g u =
      causalModulation b (fun t => f t + g t) u := by
    unfold causalModulation
    ring
  have he := norm_sq_add_complex (causalModulation b f u) (causalModulation b g u)
  rw [hs, norm_causalModulation, norm_causalModulation, norm_causalModulation] at he
  have hh := norm_sq_add_complex (f u) (g u)
  nlinarith only [he, hh]

/-- Oscillatory modulation preserves the exact resolvent mixed identity. -/
theorem integral_modulatedCausalConvolution_mixed_energy {a : ℝ} (ha : 0 < a)
    (b : ℝ) {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    (∫ u, ((starRingEnd ℂ) (f u) * modulatedCausalConvolution a b f u).re) =
      a * ∫ u, ‖modulatedCausalConvolution a b f u‖ ^ 2 := by
  have he := integral_causalConvolution_mixed_energy ha (memLp_two_causalModulation b hf)
  have hi : causalModulation (-b) (causalModulation b f) = f := by
    rw [causalModulation_add, neg_add_cancel, causalModulation_zero]
  have hm (u : ℝ) : ((starRingEnd ℂ) (f u) * modulatedCausalConvolution a b f u).re =
      ((starRingEnd ℂ) (causalModulation b f u) *
        (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] causalModulation b f) u).re := by
    rw [modulatedCausalConvolution_eq_conjugate]
    have hh := real_conj_mul_causalModulation (-b) (causalModulation b f)
      (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] causalModulation b f) u
    rw [hi] at hh
    exact hh
  have hn (u : ℝ) : ‖modulatedCausalConvolution a b f u‖ =
      ‖(causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] causalModulation b f) u‖ := by
    rw [modulatedCausalConvolution_eq_conjugate, norm_causalModulation]
  simp_rw [hm, hn]
  exact he

/-- Weighting shifts the decay rate of the literal modulated resolvent. -/
theorem causalLaplaceWeighted_modulatedCausalConvolution (a x b : ℝ) (f : ℝ → ℂ) :
    causalLaplaceWeighted x (modulatedCausalConvolution a b f) =
      modulatedCausalConvolution (a + x) b (causalLaplaceWeighted x f) := by
  rw [modulatedCausalConvolution_eq_conjugate, causalLaplaceWeighted_causalModulation,
    causalLaplaceWeighted_causalExponentialConvolution, causalLaplaceWeighted_causalModulation,
    modulatedCausalConvolution_eq_conjugate]

/-- The weighted mixed term is positive even for an undamped resolvent. -/
theorem integral_weighted_modulatedCausalConvolution_mixed_energy {a x : ℝ}
    (hx : 0 < a + x) (b : ℝ) {f : ℝ → ℂ}
    (hf : MemLp (causalLaplaceWeighted x f) 2 volume) :
    Integrable (fun u => ((starRingEnd ℂ) (causalLaplaceWeighted x f u) *
      causalLaplaceWeighted x (modulatedCausalConvolution a b f) u).re) ∧
    (∫ u, ((starRingEnd ℂ) (causalLaplaceWeighted x f u) *
      causalLaplaceWeighted x (modulatedCausalConvolution a b f) u).re) =
      (a + x) * ∫ u, ‖causalLaplaceWeighted x (modulatedCausalConvolution a b f) u‖ ^ 2 := by
  constructor
  · exact integrable_real_conj_mul_of_memLp_two hf
      (memLp_weighted_modulatedCausalConvolution hx b hf)
  · rw [causalLaplaceWeighted_modulatedCausalConvolution]
    exact integral_modulatedCausalConvolution_mixed_energy hx b hf

end GaloisForLFunctions.HTGeometry
