import GaloisForLFunctions.RHTower.EvenSectorSingleSourceFibreRecovery
import GaloisForLFunctions.RHTower.SuzukiTitchmarshUniqueness
import GaloisForLFunctions.RHTower.ArchimedeanNodeValueFunction

/-!
# Compact sources cannot occupy a nontrivial lower energy boundary

The Xi zero set is a uniqueness set for transforms of compact sources.
Consequently, whenever the arithmetic energy fibres are bounded below, their
canonical lower boundary contains only mixtures of zero sources. Every other
actual mixture admits strictly lower energy in its exact whole trace fibre.
-/

open Complex MeasureTheory Set Finsupp Zeta23
open scoped ComplexConjugate FourierTransform
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower.EvenSector
open WeilOneSided

/-- A compact source whose transform vanishes at every actual zeta zero is zero.
The multiplicities and the critical-line location play no role in this uniqueness law. -/
theorem compact_source_eq_zero_of_transform_zero (f : WeilTestFn)
    (hz : ∀ ρ : zetaZeroConfig.carrier, paperFT f.1 (gammaOf ρ) = 0) : f.1 = 0 := by
  obtain ⟨R, hR⟩ := f.2.2.isCompact.isBounded.subset_closedBall 0
  let M := ∫ u : ℝ, ‖f.1 u‖
  have hM : 0 ≤ M := integral_nonneg fun _ => norm_nonneg _
  have hs (u : ℝ) (hu : |R| < |u|) : f.1 u = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have hh := hR hm
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hh
    linarith [le_abs_self R]
  have hb (z : ℂ) : ‖paperFT f.1 z‖ ≤ M * Real.exp (|R| * ‖z‖) := by
    have h := norm_testTransform_le_exp f.2.1.continuous f.2.2
      (abs_nonneg R) hs z (Complex.abs_im_le_norm z)
    simpa only [testTransform, paperFT, mul_comm, M] using h
  have hF : Differentiable ℂ (fun z => paperFT f.1 (-z)) :=
    (differentiable_paperFT_of_compact f.2.1.continuous f.2.2).comp
      differentiable_neg
  have hzero := suzuki_exponentialType_uniqueness hF 0 (abs_nonneg R)
    (show 1 ≤ M + 1 by linarith) (fun z => ?_) (fun z hxi => ?_)
  · have hFT (t : ℝ) : paperFT f.1 t = 0 := by
      simpa only [neg_neg] using congrFun hzero (-(t : ℂ))
    have hfourier : 𝓕 f.1 = 0 := by
      funext w
      rw [Zeta23.fourier_eq_paperFT]
      have h := hFT (-(2 * Real.pi * w))
      push_cast at h
      exact h
    have hinv := Continuous.fourierInv_fourier_eq f.2.1.continuous
      (f.2.1.continuous.integrable_of_hasCompactSupport f.2.2)
      (by rw [hfourier]; exact integrable_zero _ _ _)
    rw [← hinv, hfourier]
    funext w
    rw [Real.fourierInv_eq]
    simp
  · calc
      ‖paperFT f.1 (-z)‖ ≤ M * Real.exp (|R| * ‖z‖) :=
        by simpa only [norm_neg] using hb (-z)
      _ ≤ (M + 1) * Real.exp (|R| * ‖z‖) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)
  · have hstrip := xi_zero_re_mem_open_unit hxi
    have hmem : (1 / 2 - I * z) ∈ zetaZeroConfig.carrier :=
      ⟨(xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hxi).1, hstrip⟩
    have hg : gammaOf (1 / 2 - I * z) = -z := by
      unfold gammaOf
      apply (div_eq_iff Complex.I_ne_zero).mpr
      ring
    simpa only [hg] using hz ⟨_, hmem⟩

theorem re_Wsummand_eq_norm_sq_of_RH (hRH : RiemannHypothesis)
    (f : WeilTestFn) (ρ : zetaZeroConfig.carrier) :
    (zetaZeroConfig.Wsummand f.1 f.1 ρ).re =
      (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT f.1 (gammaOf ρ)‖ ^ 2 := by
  rw [ZeroConfig.Wsummand, ZeroSide.gammaOf_of_re_eq_half (RH_implies_on_line hRH ρ.2),
    Complex.conj_ofReal, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- Under the bounded-fibre branch, zero Weil energy forces the literal source to vanish. -/
theorem compact_source_eq_zero_of_re_W_eq_zero (hRH : RiemannHypothesis)
    (f : WeilTestFn) (hzero : (zetaZeroConfig.W f.1 f.1).re = 0) : f.1 = 0 := by
  have hs := summable_Wsummand_of_contDiff_two f.2.1 f.2.2 f.2.1 f.2.2
  have hr := Complex.reCLM.summable hs
  have hn (ρ : zetaZeroConfig.carrier) : 0 ≤ (zetaZeroConfig.Wsummand f.1 f.1 ρ).re := by
    rw [re_Wsummand_eq_norm_sq_of_RH hRH]
    positivity
  rw [ZeroConfig.W, Complex.re_tsum hs] at hzero
  apply compact_source_eq_zero_of_transform_zero f
  intro ρ
  have hle := hr.le_tsum ρ (fun η _ => hn η)
  change (zetaZeroConfig.Wsummand f.1 f.1 ρ).re ≤
    ∑' η : zetaZeroConfig.carrier, (zetaZeroConfig.Wsummand f.1 f.1 η).re at hle
  rw [hzero, re_Wsummand_eq_norm_sq_of_RH hRH] at hle
  have hm : (0 : ℝ) < zetaZeroConfig.mult ρ := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (zetaZeroConfig.one_le_mult ρ ρ.2))
  have hnorm : ‖paperFT f.1 (gammaOf ρ)‖ ^ 2 ≤ 0 := by
    by_contra hh
    exact (not_lt_of_ge hle) (mul_pos hm (lt_of_not_ge hh))
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (paperFT f.1 (gammaOf ρ))])

theorem compact_re_W_pos (hRH : RiemannHypothesis) (f : WeilTestFn) (hf : f.1 ≠ 0) :
    0 < (zetaZeroConfig.W f.1 f.1).re := by
  have hs := summable_Wsummand_of_contDiff_two f.2.1 f.2.2 f.2.1 f.2.2
  have hn : 0 ≤ (zetaZeroConfig.W f.1 f.1).re := by
    rw [ZeroConfig.W, Complex.re_tsum hs]
    apply tsum_nonneg
    intro ρ
    rw [re_Wsummand_eq_norm_sq_of_RH hRH]
    positivity
  exact lt_of_le_of_ne hn (fun h => hf (compact_source_eq_zero_of_re_W_eq_zero hRH f h.symm))

theorem full_mixture_strict_canonical_energy (hRH : RiemannHypothesis)
    (c : WeilTestFn →₀ ℝ) (hc : ∀ f, 0 ≤ c f)
    (hne : ∃ f, 0 < c f ∧ f.1 ≠ 0) :
    vonMangoldtPairing (linearCombination ℝ logVector c) < fullMixtureEnergy c := by
  have hp : 0 < c.sum (fun f t =>
      t * (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest f.1 f.1)).re) := by
    classical
    apply Finset.sum_pos'
    · intro f _
      exact mul_nonneg (hc f)
        ((riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH) f.1 f.2.1 f.2.2)
    · obtain ⟨f, hcf, hf⟩ := hne
      refine ⟨f, Finsupp.mem_support_iff.mpr hcf.ne', mul_pos hcf ?_⟩
      rw [← zeta_W_eq_weilFullFunctional f.2.1 f.2.2]
      exact compact_re_W_pos hRH f hf
  rw [sum_re_weilFullFunctional] at hp
  exact sub_pos.mp hp

/-- **Unconditional strict descent inside each nontrivial actual fibre.**
This resolves the endpoint obstruction without presuming which RH branch holds. -/
theorem exists_full_mixture_strict_descent (c : WeilTestFn →₀ ℝ)
    (hc : ∀ f, 0 ≤ c f) (hne : ∃ f, 0 < c f ∧ f.1 ≠ 0) :
    ∃ d : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ d f) ∧
      linearCombination ℝ logVector d = linearCombination ℝ logVector c ∧
      fullMixtureEnergy d < fullMixtureEnergy c := by
  let v := linearCombination ℝ logVector c
  have hex : ∃ E ∈ nodeFibre v, E < fullMixtureEnergy c := by
    by_cases hRH : RiemannHypothesis
    · apply exists_lt_of_csInf_lt (nodeFibre_nonempty v)
      change nodeValue v < _
      rw [nodeValue_eq_vonMangoldtPairing hRH]
      exact full_mixture_strict_canonical_energy hRH c hc hne
    · exact not_bddBelow_iff.mp (not_bddBelow_nodeFibre hRH v) _
  obtain ⟨E, ⟨d, hd, hv, hE⟩, hlt⟩ := hex
  exact ⟨d, hd, hv, hE.trans_lt hlt⟩

end RHTower.EvenSector
