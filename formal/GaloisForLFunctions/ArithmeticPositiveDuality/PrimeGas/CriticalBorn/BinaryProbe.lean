import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Law

/-! # Recovering a circle law from vacuum interference at two relative phases -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Filter Finset MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped Topology ComplexConjugate

/-- Intensity of the vacuum superposed with occupation k of one mode. -/
def intensity (b : ℂ) (k : ℕ) (z : Circle) := ‖1 + b*(z:ℂ)^k‖^2

def intensityMean (μ : ProbabilityMeasure Circle) (b : ℂ) (k : ℕ) :=
  ∫ z, intensity b k z ∂(μ : Measure Circle)

private def monomialMean (μ : ProbabilityMeasure Circle) (k : ℕ) :=
  ∫ z : Circle, (z:ℂ)^k ∂(μ : Measure Circle)

private theorem square_one_add {u : ℂ} (hu : ‖u‖=1) : ‖1+u‖^2 = 2+2*u.re := by
  have h := congrArg (fun r : ℝ => r^2) hu
  simp only [Complex.sq_norm,Complex.normSq_apply,one_pow] at h
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.one_re,Complex.one_im,zero_add]
  nlinarith only [h]

private theorem intensity_mean {b : ℂ} (hb : ‖b‖=1) (k : ℕ) (μ : ProbabilityMeasure Circle) :
    intensityMean μ b k = 2 + 2*(b * monomialMean μ k).re := by
  let f := fun z : Circle => b*(z:ℂ)^k
  have hc : Continuous f := continuous_const.mul (continuous_subtype_val.pow k)
  have hi : Integrable f (μ : Measure Circle) := hc.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have sqr (z : Circle) : intensity b k z = 2 + 2 * RCLike.re (f z) :=
    square_one_add (by rw [norm_mul,hb,norm_pow,Circle.norm_coe,one_pow,mul_one])
  rw [intensityMean]
  simp only [sqr]
  rw [integral_add (integrable_const _) (hi.re.const_mul _),integral_const_mul,integral_re hi,
    integral_const,probReal_univ,one_smul]
  change 2+2*(∫ z : Circle, b*(z:ℂ)^k ∂(μ : Measure Circle)).re = _
  rw [integral_const_mul,monomialMean]

private theorem uniform_monomial (k : ℕ) : monomialMean uniform (k+1) = 0 := by
  change (∫ z : Circle, (z:ℂ)^(k+1) ∂circleLebesgue) = 0
  simpa only [zpow_natCast,if_neg (show ((k+1:ℕ):ℤ)≠0 by omega)] using
    integral_circleLebesgue_coe_zpow ((k+1:ℕ):ℤ)

private theorem conjugate_monomial (ρ : ProbabilityMeasure Circle) (k : ℕ) :
    circleMeasureMomentZ (ρ : Measure Circle) (k:ℤ) = conj (monomialMean ρ k) := by
  have he (z : Circle) : ((z:ℂ)^k)⁻¹ = conj ((z:ℂ)^k) :=
    Complex.inv_eq_conj (by rw [norm_pow,Circle.norm_coe,one_pow])
  simp only [circleMeasureMomentZ,zpow_neg,zpow_natCast,he,integral_conj,monomialMean]

private theorem negative_mode (ρ : ProbabilityMeasure Circle) (k : ℕ) :
    circleMeasureMomentZ (ρ : Measure Circle) (Int.negSucc k) = monomialMean ρ (k+1) := by
  change (∫ z : Circle, (z:ℂ)^((k+1:ℕ):ℤ) ∂(ρ : Measure Circle)) = _
  simp only [zpow_natCast,monomialMean]

/-- Two fixed relative amplitudes in each positive occupation determine
weak Haar convergence through the real and imaginary Fourier coordinates. -/
theorem haar_iff_binary_probes (μ : ℕ → ProbabilityMeasure Circle) :
    Tendsto μ atTop (𝓝 uniform) ↔ ∀ k : ℕ,
      Tendsto (fun N => intensityMean (μ N) 1 (k+1)) atTop (𝓝 2) ∧
      Tendsto (fun N => intensityMean (μ N) Complex.I (k+1)) atTop (𝓝 2) := by
  constructor
  · intro h k
    have m := ((continuous_circleMeasureMomentZ (Int.negSucc k)).tendsto uniform).comp h
    simp only [Function.comp_def,negative_mode,uniform_monomial] at m
    have lim (b : ℂ) (hb : ‖b‖=1) : Tendsto (fun N => intensityMean (μ N) b (k+1)) atTop (𝓝 2) := by
      have hr := Complex.continuous_re.continuousAt.tendsto.comp (m.const_mul b)
      simpa only [intensity_mean hb,Function.comp_def,mul_zero,Complex.zero_re,add_zero] using
        (hr.const_mul 2).const_add 2
    exact ⟨lim 1 norm_one,lim Complex.I Complex.norm_I⟩
  · intro h
    have coords (k : ℕ) : Tendsto (fun N => monomialMean (μ N) (k+1)) atTop
        (𝓝 (monomialMean uniform (k+1))) := by
      obtain ⟨hr,hi⟩ := h k
      simp only [intensity_mean norm_one,one_mul] at hr
      simp only [intensity_mean Complex.norm_I,Complex.I_mul_re] at hi
      have realPart := (hr.sub_const 2).div_const 2
      have imagPart := (hi.sub_const 2).div_const (-2)
      rw [sub_self,zero_div] at realPart imagPart
      have rr : Tendsto (fun N => (monomialMean (μ N) (k+1)).re) atTop (𝓝 0) := by
        exact realPart.congr (fun N => by ring)
      have ii : Tendsto (fun N => (monomialMean (μ N) (k+1)).im) atTop (𝓝 0) := by
        exact imagPart.congr (fun N => by ring)
      rw [uniform_monomial]
      have c := (Complex.continuous_ofReal.continuousAt.tendsto.comp rr).add
        ((Complex.continuous_ofReal.continuousAt.tendsto.comp ii).mul_const Complex.I)
      simpa only [Function.comp_def,Complex.re_add_im,Complex.ofReal_zero,zero_mul,add_zero] using c
    have allMoments (k : ℕ) : Tendsto (fun N => monomialMean (μ N) k) atTop
        (𝓝 (monomialMean uniform k)) := by
      cases k with
      | zero => simp only [monomialMean,pow_zero,integral_const,probReal_univ,one_smul]; exact tendsto_const_nhds
      | succ k => exact coords k
    rw [isClosedEmbedding_completeCircleMomentSequence.isEmbedding.tendsto_nhds_iff,tendsto_pi_nhds]
    intro k
    cases k with
    | ofNat l =>
      simpa only [Function.comp_def,completeCircleMomentSequence,Int.ofNat_eq_natCast,conjugate_monomial]
        using Complex.continuous_conj.continuousAt.tendsto.comp (allMoments l)
    | negSucc l =>
      simpa only [Function.comp_def,completeCircleMomentSequence,negative_mode] using coords l

#print axioms haar_iff_binary_probes

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
