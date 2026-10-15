import GaloisForLFunctions.RHTower.WeilMarkovPrimitiveHyperplane

/-!
# The archimedean-minus-prime form on a single pole hyperplane

For a real test `F` the pole term of its autocorrelation is
`P(F) = 2 (∫F e^{-x/2}) (∫F e^{x/2})`, the product of the two Laplace values of `F` at the poles
`s = 0` and `s = 1` of the completed zeta function. It is a form of signature `(1,1)` and vanishes on
each of the two hyperplanes `{∫F e^{-x/2} = 0}` and `{∫F e^{x/2} = 0}`. On either hyperplane the
archimedean-minus-prime form `M = arch − primes` coincides with the Weil form `W = Σ_ρ |F̂(ρ)|²`.

A failure of the Riemann hypothesis produces an even test with vanishing pole values and negative
Weil energy; it lies on both hyperplanes. Hence the Riemann hypothesis is equivalent to `M ≥ 0` on
either single pole hyperplane. Compared with the symmetric hyperplane `{∫F cosh(x/2) = 0}`, this
isolates one null line of the pole plane at a time.
-/

open Complex MeasureTheory
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower

noncomputable section

/-- If the Laplace value at the pole `s = 0` vanishes, the pole term of the autocorrelation is
zero. -/
theorem weilPoleTerm_eq_zero_of_paperFT_I_div_two_eq_zero {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (h : paperFT f (I / 2) = 0) :
    weilPoleTerm (EF.weilTest f f) = 0 := by
  rw [weilPoleTerm_weilTest_eq hf hfc, h, map_zero, zero_mul, mul_zero, add_zero]

/-- If the Laplace value at the pole `s = 1` vanishes, the pole term of the autocorrelation is
zero. -/
theorem weilPoleTerm_eq_zero_of_paperFT_neg_I_div_two_eq_zero {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (h : paperFT f (-I / 2) = 0) :
    weilPoleTerm (EF.weilTest f f) = 0 := by
  rw [weilPoleTerm_weilTest_eq hf hfc, h, map_zero, mul_zero, zero_mul, add_zero]

/-- On the pole hyperplane `{f̂(i/2) = 0}` the archimedean-minus-prime form is the Weil form. -/
theorem markovEnergy_eq_W_re_of_paperFT_I_div_two_eq_zero {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (h : paperFT f (I / 2) = 0) :
    markovEnergy f = (zetaZeroConfig.W f f).re := by
  rw [markovEnergy_eq_W_sub hf hfc,
    weilPoleTerm_eq_zero_of_paperFT_I_div_two_eq_zero hf.continuous hfc h, Complex.zero_re,
    sub_zero]

/-- On the pole hyperplane `{f̂(-i/2) = 0}` the archimedean-minus-prime form is the Weil form. -/
theorem markovEnergy_eq_W_re_of_paperFT_neg_I_div_two_eq_zero {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (h : paperFT f (-I / 2) = 0) :
    markovEnergy f = (zetaZeroConfig.W f f).re := by
  rw [markovEnergy_eq_W_sub hf hfc,
    weilPoleTerm_eq_zero_of_paperFT_neg_I_div_two_eq_zero hf.continuous hfc h, Complex.zero_re,
    sub_zero]

/-- Under RH the Weil energy of every test is nonnegative. -/
theorem W_re_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) : 0 ≤ (zetaZeroConfig.W f f).re := by
  rw [zeta_W_eq_weilFullFunctional hf hfc]
  exact (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH) f hf hfc

/-- The Laplace value at the pole `s = 1` of a real test is its `e^{x/2}`-moment. -/
theorem paperFT_ofReal_neg_I_half_eq_integral (u : ℝ → ℝ) :
    paperFT (fun x => (u x : ℂ)) (-I / 2) = ((∫ x, u x * Real.exp (x / 2) : ℝ) : ℂ) := by
  unfold paperFT
  rw [← integral_complex_ofReal]
  congr 1
  funext x
  push_cast
  congr 1
  congr 1
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **RH is positivity of the archimedean-minus-prime form on the pole hyperplane `s = 0`.**
`RH ⟺ M(F) ≥ 0` for every real `C²` compactly supported `F` with `∫ F(x) e^{-x/2} dx = 0`. -/
theorem riemannHypothesis_iff_forall_exp_neg_half_moment_zero_markovEnergy_nonneg :
    RiemannHypothesis ↔ ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F →
      ∫ x, F x * Real.exp (-(x / 2)) = 0 → 0 ≤ markovEnergy (fun x => (F x : ℂ)) := by
  constructor
  · intro hRH F hF hFc h0
    have hf : ContDiff ℝ 2 (fun x => (F x : ℂ)) := Complex.ofRealCLM.contDiff.comp hF
    have hfc : HasCompactSupport (fun x => (F x : ℂ)) := hFc.comp_left Complex.ofReal_zero
    have hp : paperFT (fun x => (F x : ℂ)) (I / 2) = 0 := by
      rw [paperFT_ofReal_I_half_eq_integral, h0, Complex.ofReal_zero]
    rw [markovEnergy_eq_W_re_of_paperFT_I_div_two_eq_zero hf hfc hp]
    exact W_re_nonneg_of_riemannHypothesis hRH hf hfc
  · intro h
    by_contra hRH
    obtain ⟨u, hu, huc, -, hpole, hneg⟩ :=
      exists_even_poleFree_negative_of_not_riemannHypothesis hRH
    have hf : ContDiff ℝ 2 (fun x => (u x : ℂ)) := Complex.ofRealCLM.contDiff.comp hu
    have hfc : HasCompactSupport (fun x => (u x : ℂ)) := huc.comp_left Complex.ofReal_zero
    have h0 : ∫ x, u x * Real.exp (-(x / 2)) = 0 := by
      have := hpole
      rw [paperFT_ofReal_I_half_eq_integral] at this
      exact_mod_cast this
    have hM := h u hu huc h0
    rw [markovEnergy_eq_W_re_of_paperFT_I_div_two_eq_zero hf hfc hpole] at hM
    exact absurd hM (not_le.mpr hneg)

/-- **RH is positivity of the archimedean-minus-prime form on the pole hyperplane `s = 1`.**
`RH ⟺ M(F) ≥ 0` for every real `C²` compactly supported `F` with `∫ F(x) e^{x/2} dx = 0`. -/
theorem riemannHypothesis_iff_forall_exp_half_moment_zero_markovEnergy_nonneg :
    RiemannHypothesis ↔ ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F →
      ∫ x, F x * Real.exp (x / 2) = 0 → 0 ≤ markovEnergy (fun x => (F x : ℂ)) := by
  constructor
  · intro hRH F hF hFc h0
    have hf : ContDiff ℝ 2 (fun x => (F x : ℂ)) := Complex.ofRealCLM.contDiff.comp hF
    have hfc : HasCompactSupport (fun x => (F x : ℂ)) := hFc.comp_left Complex.ofReal_zero
    have hp : paperFT (fun x => (F x : ℂ)) (-I / 2) = 0 := by
      rw [paperFT_ofReal_neg_I_half_eq_integral, h0, Complex.ofReal_zero]
    rw [markovEnergy_eq_W_re_of_paperFT_neg_I_div_two_eq_zero hf hfc hp]
    exact W_re_nonneg_of_riemannHypothesis hRH hf hfc
  · intro h
    by_contra hRH
    obtain ⟨u, hu, huc, heven, hpole, hneg⟩ :=
      exists_even_poleFree_negative_of_not_riemannHypothesis hRH
    have hf : ContDiff ℝ 2 (fun x => (u x : ℂ)) := Complex.ofRealCLM.contDiff.comp hu
    have hfc : HasCompactSupport (fun x => (u x : ℂ)) := huc.comp_left Complex.ofReal_zero
    have h0 : ∫ x, u x * Real.exp (x / 2) = 0 := by
      rw [integral_mul_exp_half_of_even heven]
      have := hpole
      rw [paperFT_ofReal_I_half_eq_integral] at this
      exact_mod_cast this
    have hM := h u hu huc h0
    rw [markovEnergy_eq_W_re_of_paperFT_I_div_two_eq_zero hf hfc hpole] at hM
    exact absurd hM (not_le.mpr hneg)

end

end RHTower
