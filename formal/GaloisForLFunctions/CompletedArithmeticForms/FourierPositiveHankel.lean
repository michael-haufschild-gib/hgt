import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterMixedSignedJetCompleteness
import GaloisForLFunctions.HTGeometry.MomentHankelStrict
import GaloisForLFunctions.HTGeometry.PositiveReweightingSupport

/-!
# Strict Hankel positivity from a positive Schwartz spectrum

Fourier inversion identifies signed jets with the polynomial moments of
the real spectral density. A strictly positive density has infinite support,
so every finite moment matrix is positive definite. Positive geometric
rescaling preserves this strictness.
-/

open Complex Filter Set MeasureTheory Matrix
open scoped SchwartzMap FourierTransform BigOperators
namespace GaloisForLFunctions.CompletedArithmeticForms
noncomputable section

private theorem integrable_pow_mul_schwartz (f : SchwartzMap ℝ ℂ) (n : ℕ) :
    Integrable (fun x : ℝ => (x : ℂ) ^ n * f x) := by
  refine (f.integrable_pow_mul volume n).mono' (by fun_prop) ?_
  filter_upwards with x
  simp only [norm_mul, norm_pow, Complex.norm_real]
  exact le_rfl

private theorem integrable_pow_mul_schwartz_re (f : SchwartzMap ℝ ℂ) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n * (f x).re) := by
  have h := Complex.reCLM.integrable_comp (integrable_pow_mul_schwartz f n)
  simpa only [Function.comp_apply, Complex.reCLM_apply, Complex.mul_re, ← Complex.ofReal_pow, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] using h

/-- Fourier inversion identifies all real signed jets with the moments of the real spectrum. -/
theorem signedSchwartzJet_eq_fourierMoment (f : SchwartzMap ℝ ℂ) (n : ℕ) :
    ((-I) ^ n * iteratedDeriv n f 0).re =
      (2 * Real.pi) ^ n * ∫ ξ : ℝ, ξ ^ n * (𝓕 (f : ℝ → ℂ) ξ).re := by
  rw [_root_.RHTower.schwartz_iteratedDeriv_zero_eq_fourierMoment,
    ← integral_const_mul]
  have he (ξ : ℝ) : (-I) ^ n *
      ((2 * (Real.pi : ℂ) * I * (ξ : ℂ)) ^ n * 𝓕 (f : ℝ → ℂ) ξ) =
      ((2 * Real.pi : ℝ) : ℂ) ^ n * ((ξ : ℂ) ^ n * 𝓕 (f : ℝ → ℂ) ξ) := by
    have hp : (-I) * (2 * (Real.pi : ℂ) * I * (ξ : ℂ)) =
        ((2 * Real.pi : ℝ) : ℂ) * (ξ : ℂ) := by
      push_cast
      linear_combination -(2 * (Real.pi : ℂ) * (ξ : ℂ)) * Complex.I_sq
    rw [← mul_assoc, ← mul_pow, hp, mul_pow, mul_assoc]
  simp_rw [he]
  rw [integral_const_mul]
  have hr := Complex.reCLM.integral_comp_comm
    (integrable_pow_mul_schwartz (𝓕 f) n)
  simp only [Complex.reCLM_apply, Complex.mul_re, ← Complex.ofReal_pow,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hr ⊢
  simp only [SchwartzMap.fourier_coe] at hr
  change (∫ x : ℝ, x ^ n * (𝓕 (f : ℝ → ℂ) x).re) =
    (∫ x : ℝ, (x ^ n : ℝ) * 𝓕 (f : ℝ → ℂ) x).re at hr
  rw [← hr]

/-- Positive mass and a nonzero geometric rescaling preserve every strict Hankel section. -/
theorem momentHankelMatrix_posDef_geometric {s : ℕ → ℝ} {C a : ℝ}
    (hC : 0 < C) (ha : a ≠ 0) {N : ℕ}
    (hM : (_root_.HTGeometry.momentHankelMatrix s N).PosDef) :
    (_root_.HTGeometry.momentHankelMatrix (fun n => C * a ^ n * s n) N).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hM ⊢
  refine ⟨_root_.HTGeometry.momentHankelMatrix_isHermitian _ _, ?_⟩
  intro v hv
  let w : Fin N → ℝ := fun i => a ^ (i : ℕ) * v i
  have hw : w ≠ 0 := by
    intro hz
    apply hv
    funext i
    have hi := congrFun hz i
    dsimp only [w, Pi.zero_apply] at hi
    exact (mul_eq_zero.mp hi).resolve_left (pow_ne_zero _ ha)
  have hp := mul_pos hC (hM.2 hw)
  simp only [star_trivial] at hp ⊢
  convert hp using 1
  simp only [dotProduct, Matrix.mulVec, _root_.HTGeometry.momentHankelMatrix,
    Finset.mul_sum, pow_add, w]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A strictly positive Schwartz spectrum has strictly positive moment matrices at every rank. -/
theorem schwartzRealMoment_hankel_posDef (f : SchwartzMap ℝ ℂ)
    (hf : ∀ x : ℝ, 0 < (f x).re) (N : ℕ) :
    (_root_.HTGeometry.momentHankelMatrix
      (fun n => ∫ x : ℝ, x ^ n * (f x).re) N).PosDef := by
  let w : ℝ → NNReal := fun x => Real.toNNReal (f x).re
  let μ : Measure ℝ := volume.withDensity (fun x => (w x : ENNReal))
  have hw : Measurable w := by
    dsimp only [w]
    exact (Complex.continuous_re.comp f.continuous).measurable.real_toNNReal
  have hval (x : ℝ) : (w x : ℝ) = (f x).re := Real.coe_toNNReal _ (hf x).le
  have hmom (n : ℕ) : (∫ x : ℝ, x ^ n * (f x).re) = ∫ x : ℝ, x ^ n ∂μ := by
    change _ = ∫ x : ℝ, x ^ n ∂volume.withDensity (fun x => (w x : ENNReal))
    rw [integral_withDensity_eq_integral_smul hw]
    apply integral_congr_ae
    filter_upwards with x
    rw [NNReal.smul_def, hval]
    ring
  have hint (n : ℕ) : Integrable (fun x : ℝ => x ^ n) μ := by
    change Integrable (fun x : ℝ => x ^ n) (volume.withDensity (fun x => (w x : ENNReal)))
    rw [integrable_withDensity_iff_integrable_smul hw]
    have hi := integrable_pow_mul_schwartz_re f n
    apply hi.congr
    filter_upwards with x
    rw [NNReal.smul_def, hval]
    ring
  have hinf (F : Finset ℝ) : 0 < μ {x : ℝ | x ∉ F} := by
    have hpos : ∀ᵐ x : ℝ ∂volume, (w x : ENNReal) ≠ 0 := by
      filter_upwards with x
      rw [ne_eq, ENNReal.coe_eq_zero, ← NNReal.coe_eq_zero, hval]
      exact (hf x).ne'
    rw [pos_iff_ne_zero]
    intro hz
    have hzero := (HTGeometry.measure_withDensity_eq_zero_iff volume
      hw.coe_nnreal_ennreal hpos {x : ℝ | x ∉ F}).mp hz
    have hF : volume (F : Set ℝ) = 0 := F.finite_toSet.measure_zero volume
    have he : {x : ℝ | x ∉ F} = univ \ (F : Set ℝ) := by ext x; simp
    rw [he, measure_sdiff_null hF] at hzero
    simp at hzero
  exact _root_.HTGeometry.momentHankelMatrix_posDef_of_infiniteSupport _ hmom hint hinf N

/-- Strict positivity of the actual Fourier transform controls the full signed jet tower. -/
theorem signedSchwartzJet_hankel_posDef (f : SchwartzMap ℝ ℂ)
    (hf : ∀ ξ : ℝ, 0 < (𝓕 (f : ℝ → ℂ) ξ).re) (N : ℕ) :
    (_root_.HTGeometry.momentHankelMatrix
      (fun n => ((-I) ^ n * iteratedDeriv n f 0).re) N).PosDef := by
  have hm := schwartzRealMoment_hankel_posDef (𝓕 f) hf N
  have hg := momentHankelMatrix_posDef_geometric (C := 1) (a := 2 * Real.pi)
    (by norm_num) (by positivity) hm
  have he : (fun n => 1 * (2 * Real.pi) ^ n * ∫ x : ℝ, x ^ n * ((𝓕 f) x).re) =
      (fun n => ((-I) ^ n * iteratedDeriv n f 0).re) := by
    funext n
    simpa only [one_mul, SchwartzMap.fourier_coe] using (signedSchwartzJet_eq_fourierMoment f n).symm
  rw [he] at hg
  exact hg

end
end GaloisForLFunctions.CompletedArithmeticForms
