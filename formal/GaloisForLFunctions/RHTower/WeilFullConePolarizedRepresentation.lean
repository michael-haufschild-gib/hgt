import GaloisForLFunctions.RHTower.WeilFullConeAtomExtraction

/-!
# Polarized spectral representation of the Weil form

For a full-cone Weil-positive `lam` with boundary measure `μ_lam`, and `C²` compactly supported
`f, g`,

`W_lam(f ⋆ g̃) = ∫ f̂(r) · conj(ĝ(r)) dμ_lam(r)`  (`weilFullFunctional_weilTest_eq_integral`),

and, translating `f`, `W_lam(transl_y(f ⋆ g̃)) = ∫ e^{iry} f̂(r) conj(ĝ(r)) dμ_lam(r)`.  This extends the
diagonal representation `W_lam(f ⋆ f̃) = ∫ |f̂|² dμ_lam` to all sesquilinear tests.  It gives, for
instance, `|W_lam(transl_y(f ⋆ g̃))| ≤ (W_lam(f ⋆ f̃) W_lam(g ⋆ g̃))^{1/2}`
(`norm_weilFullFunctional_transl_weilTest_le`).

**Proof.**  Polarization: `4 (f ⋆ g̃) = Σ_k i^k (h_k ⋆ h̃_k)` with `h_k = f + i^k g`.  Apply the
diagonal representation to each `h_k` and the identity `Σ_k i^k |a + i^k b|² = 4 a b̄`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ComplexConjugate ENNReal NNReal
open Zeta23

noncomputable section

namespace RHTower.WeilSpectral

theorem integrable_mul_conj_shift {f g : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (x : ℝ) : Integrable fun u => f u * conj (g (u - x)) :=
  (hf.mul ((continuous_conj.comp (hg.comp (continuous_id.sub continuous_const))))).integrable_of_hasCompactSupport
    (hfc.mul_right)

/-- Expansion of `(f + c g) ⋆ (f + c g)~`. -/
theorem weilTest_add_smul_self {f g : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (c : ℂ) (x : ℝ) :
    EF.weilTest (f + c • g) (f + c • g) x = EF.weilTest f f x + conj c * EF.weilTest f g x +
      c * EF.weilTest g f x + c * conj c * EF.weilTest g g x := by
  simp only [weilTest_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  set F1 : ℝ → ℂ := fun u => f u * conj (f (u - x)) with hF1
  set F2 : ℝ → ℂ := fun u => conj c * (f u * conj (g (u - x))) with hF2
  set F3 : ℝ → ℂ := fun u => c * (g u * conj (f (u - x))) with hF3
  set F4 : ℝ → ℂ := fun u => c * conj c * (g u * conj (g (u - x))) with hF4
  have h1 : Integrable F1 := integrable_mul_conj_shift hf hfc hf x
  have h2 : Integrable F2 := (integrable_mul_conj_shift hf hfc hg x).const_mul (conj c)
  have h3 : Integrable F3 := (integrable_mul_conj_shift hg hgc hf x).const_mul c
  have h4 : Integrable F4 := (integrable_mul_conj_shift hg hgc hg x).const_mul (c * conj c)
  have e : (fun u : ℝ => (f u + c * g u) * (conj (f (u - x)) + conj c * conj (g (u - x)))) =
      ((F1 + F2) + F3) + F4 := by
    funext u; simp only [Pi.add_apply, hF1, hF2, hF3, hF4]; ring
  rw [e, integral_add' ((h1.add h2).add h3) h4, integral_add' (h1.add h2) h3, integral_add' h1 h2]
  simp only [hF1, hF2, hF3, hF4]
  rw [integral_const_mul, integral_const_mul, integral_const_mul]

theorem polarization_coeffs (A B B' C : ℂ) :
    (1 / 4 : ℂ) * ∑ k : Fin 4, I ^ (k : ℕ) *
      (A + conj (I ^ (k : ℕ)) * B + I ^ (k : ℕ) * B' + I ^ (k : ℕ) * conj (I ^ (k : ℕ)) * C) = B := by
  have h0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have h1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have h2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [Fin.sum_univ_four, h0, h1, h2, h3]
  simp only [map_pow, Complex.conj_I]
  have hI2 : I ^ 2 = -1 := Complex.I_sq
  have hI3 : I ^ 3 = -I := by rw [pow_succ, hI2]; ring
  have hn2 : (-I) ^ 2 = -1 := by rw [neg_sq, hI2]
  have hn3 : (-I) ^ 3 = I := by rw [show (-I) ^ 3 = -(I ^ 3) by ring, hI3, neg_neg]
  rw [hI2, hI3, hn2, hn3]
  ring_nf
  rw [hI2]
  ring

/-- **Polarization of the Weil test.** -/
theorem weilTest_polarization {f g : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    EF.weilTest f g = (1 / 4 : ℂ) • ∑ k : Fin 4, (I ^ (k : ℕ)) •
      EF.weilTest (f + I ^ (k : ℕ) • g) (f + I ^ (k : ℕ) • g) := by
  funext x
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  simp_rw [weilTest_add_smul_self hf hfc hg hgc]
  simp only [Finset.mul_sum]
  rw [← Finset.mul_sum]
  exact (polarization_coeffs _ _ _ _).symm

theorem admissible_weilTest_add {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (c : ℂ) :
    Admissible (EF.weilTest (f + c • g) (f + c • g)) :=
  admissible_weilTest (hf.add (hg.const_smul c)) (hfc.add (hgc.smul_left))

/-- The diagonal representation as a complex integral. -/
theorem weilFullFunctional_weilTest_self_eq_integral {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {h : ℝ → ℂ} (hh : ContDiff ℝ 2 h) (hhc : HasCompactSupport h) :
    weilFullFunctional lam (EF.weilTest h h) =
      ∫ r, ((‖paperFT h r‖ ^ 2 : ℝ) : ℂ) ∂boundaryMeasure hW := by
  obtain ⟨hfin, heq⟩ := weilFullFunctional_weilTest_eq_lintegral hW hh hhc
  rw [heq, integral_complex_ofReal]
  congr 1
  rw [← integral_toReal
    (measurable_specDensity (hh.continuous.integrable_of_hasCompactSupport hhc)).coe_nnreal_ennreal.aemeasurable
    (Eventually.of_forall fun r => ENNReal.coe_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp [specDensity]

theorem integrable_norm_sq_paperFT {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {h : ℝ → ℂ}
    (hh : ContDiff ℝ 2 h) (hhc : HasCompactSupport h) :
    Integrable (fun r : ℝ => ‖paperFT h r‖ ^ 2) (boundaryMeasure hW) := by
  obtain ⟨hfin, -⟩ := weilFullFunctional_weilTest_eq_lintegral hW hh hhc
  have hint : Integrable (fun r : ℝ => ((specDensity h r : ℝ≥0∞).toReal)) (boundaryMeasure hW) :=
    integrable_toReal_of_lintegral_ne_top
      (measurable_specDensity (hh.continuous.integrable_of_hasCompactSupport hhc)).coe_nnreal_ennreal.aemeasurable
      hfin.ne
  refine hint.congr (Eventually.of_forall fun r => ?_)
  simp [specDensity]

theorem paperFT_add_smul_real {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (c : ℂ)
    (r : ℝ) : paperFT (f + c • g) r = paperFT f r + c * paperFT g r := by
  unfold paperFT
  have hb : ∀ u : ℝ, ‖cexp (I * (r : ℂ) * (u : ℂ))‖ = 1 := fun u => by
    rw [show I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hm : Continuous fun u : ℝ => cexp (I * (r : ℂ) * (u : ℂ)) := by fun_prop
  have h1 : Integrable fun u => f u * cexp (I * (r : ℂ) * (u : ℂ)) :=
    hf.norm.mono' (hf.aestronglyMeasurable.mul hm.aestronglyMeasurable)
      (Eventually.of_forall fun u => by rw [norm_mul, hb u, mul_one])
  have h2 : Integrable fun u => g u * cexp (I * (r : ℂ) * (u : ℂ)) :=
    hg.norm.mono' (hg.aestronglyMeasurable.mul hm.aestronglyMeasurable)
      (Eventually.of_forall fun u => by rw [norm_mul, hb u, mul_one])
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc]
  rw [integral_add h1 (by simpa [mul_assoc] using h2.const_mul c), integral_const_mul]

theorem polarization_four (a b : ℂ) :
    (1 / 4 : ℂ) * ∑ k : Fin 4, I ^ (k : ℕ) * ((‖a + I ^ (k : ℕ) * b‖ ^ 2 : ℝ) : ℂ) = a * conj b := by
  simp only [Fin.sum_univ_four, Complex.sq_norm, ← Complex.mul_conj, map_add, map_mul, map_pow,
    Complex.conj_I]
  norm_num
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_four]
  ring_nf
  rw [show I ^ 3 = -I by rw [pow_succ, Complex.I_sq]; ring]
  ring

/-- **Polarized spectral representation.** `W_lam(f ⋆ g̃) = ∫ f̂ · conj ĝ dμ_lam`. -/
theorem weilFullFunctional_weilTest_eq_integral {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    weilFullFunctional lam (EF.weilTest f g) =
      ∫ r, paperFT f r * conj (paperFT g r) ∂boundaryMeasure hW := by
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hfc
  have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have hhd : ∀ k : Fin 4, ContDiff ℝ 2 (f + I ^ (k : ℕ) • g) := fun k => hf.add (hg.const_smul _)
  have hhc : ∀ k : Fin 4, HasCompactSupport (f + I ^ (k : ℕ) • g) := fun k =>
    hfc.add hgc.smul_left
  rw [weilTest_polarization hf.continuous hfc hg.continuous hgc, weilFullFunctional_smul,
    weilFullFunctional_sum lam (fun k _ => (admissible_weilTest (hhd k) (hhc k)).smul _)]
  simp_rw [weilFullFunctional_smul, weilFullFunctional_weilTest_self_eq_integral hW (hhd _) (hhc _)]
  have hint : ∀ k : Fin 4, Integrable (fun r : ℝ => I ^ (k : ℕ) *
      ((‖paperFT (f + I ^ (k : ℕ) • g) r‖ ^ 2 : ℝ) : ℂ)) (boundaryMeasure hW) := fun k =>
    ((integrable_norm_sq_paperFT hW (hhd k) (hhc k)).ofReal).const_mul _
  rw [← integral_const_mul]
  simp_rw [← integral_const_mul]
  rw [← integral_finset_sum _ fun k _ => hint k, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  simp_rw [paperFT_add_smul_real hfi hgi]
  exact polarization_four _ _

/-- **Translated polarized representation.** -/
theorem weilFullFunctional_transl_weilTest_eq_integral {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (y : ℝ) :
    weilFullFunctional lam (transl y (EF.weilTest f g)) =
      ∫ r, cexp (I * (r : ℂ) * y) * (paperFT f r * conj (paperFT g r)) ∂boundaryMeasure hW := by
  have hshift : transl y (EF.weilTest f g) = EF.weilTest (transl y f) g := by
    funext x
    rw [transl, weilTest_apply, weilTest_apply]
    rw [← integral_add_right_eq_self (μ := volume)
      (fun u : ℝ => transl y f u * conj (g (u - x))) y]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [transl, add_sub_cancel_right]
    congr 3
    ring
  have hfy : ContDiff ℝ 2 (transl y f) := hf.comp (contDiff_id.sub contDiff_const)
  have hfyc : HasCompactSupport (transl y f) := hfc.comp_homeomorph (Homeomorph.subRight y)
  rw [hshift, weilFullFunctional_weilTest_eq_integral hW hfy hfyc hg hgc]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  rw [paperFT_transl]
  ring

/-- **Cauchy–Schwarz bound.**  `|W_lam(transl_y(f ⋆ g̃))| ≤ (∫|f̂|²dμ ∫|ĝ|²dμ)^{1/2}`. -/
theorem norm_weilFullFunctional_transl_weilTest_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (y : ℝ) :
    ‖weilFullFunctional lam (transl y (EF.weilTest f g))‖ ≤
      ∫ r, ‖paperFT f r‖ * ‖paperFT g r‖ ∂boundaryMeasure hW := by
  rw [weilFullFunctional_transl_weilTest_eq_integral hW hf hfc hg hgc]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  rw [norm_mul, norm_mul, norm_conj, show I * (r : ℂ) * y = ((r * y : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul]

end RHTower.WeilSpectral

end
