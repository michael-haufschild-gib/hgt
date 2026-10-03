import GaloisForLFunctions.RHTower.WeilFullConeExposedPoint
import GaloisForLFunctions.RHTower.WeilFullConePolarizedRepresentation
import GaloisForLFunctions.RHTower.WeilFullConeHorizontalPotential

/-!
# A Weil-positive system carried by the critical zeros of `ζ` is `Λ`

Let `lam` be full-cone Weil-positive with boundary measure `μ_lam`, and let
`Z = {r ∈ ℝ : ζ(½ + ir) = 0}` be the set of ordinates of the zeros of `ζ` on the critical line.

**Theorem** (`eq_vonMangoldt_of_boundaryMeasure_criticalZeros`, unconditional).  If `μ_lam` is
carried by `Z`, i.e. `μ_lam(ℝ ∖ Z) = 0`, then `lam(n) = Λ(n)` for every `n ≥ 2`.  Hence `Λ` is
Weil-positive and the Riemann hypothesis holds
(`riemannHypothesis_of_boundaryMeasure_criticalZeros`).

No assumption is made on the masses `μ_lam({γ})`: they may be arbitrary nonnegative numbers, and
they need not be bounded relative to the multiplicities of the zeros.  Off-line zeros are not
excluded a priori; they are excluded by the conclusion.

**Spectral uniqueness on the zeros** (`eq_zero_of_signedMeasure_criticalZeros`).  More generally,
a real measure `ν = ν₊ − ν₋` carried by `Z` (with `∫ (1 + r²)⁻¹ d|ν| < ∞`) whose Fourier transform
is a discrete measure on `±log ℕ_{≥2}`, with weights `w(n) n^{−1/2}`, `Σ |w(n)| n^{−2} < ∞`, is
zero.  So the critical zero set of `ζ` carries no measure with spectrum in the logarithms of the
integers, of any sign.  With a frequency-zero term allowed
(`eq_zero_of_signedMeasure_criticalZeros_density`), the density vanishes as well: the critical zeros carry no measure of nonzero density whose
Fourier transform is supported on `{0} ∪ ±log ℕ_{≥2}`.

**Proof.**  Put `v = lam − Λ` and `T_v(F, G) = Σ_{n ≥ 2} v(n) n^{−1/2} (k(log n) + k(−log n))`,
`k = F ⋆ G̃`.  For a real `C²` compactly supported test `F`, the explicit formula and the spectral
representation give
`T_v(F, F) = Re W_ζ(F, F) − ∫ |F̂|² dμ_lam`,
where `W_ζ` is the zero side of the explicit formula for `ζ`.  Both terms are controlled by the
size of `F̂` at the zeros of `ζ`: if `(1 + |γ|)|F̂(γ)| ≤ E` at every zero, then
`|W_ζ(F, F)| ≤ (5/4) S E²` and, because `μ_lam` lives on `Z`,
`∫ |F̂|² dμ_lam ≤ E² ∫ (1 + r²)⁻¹ dμ_lam`.  So `|T_v(F, F)| ≤ K E²`.

Apply this to `F = Φχ_L + εH`, where `Φ` is the Riemann kernel (`Φ̂ = Ξ`, which vanishes at every
zero of `ζ`), `χ_L` a cutoff and `H` an arbitrary test.  At the zeros,
`(1 + |γ|)|F̂(γ)| ≤ E_L + |ε| E_H`, with `E_L → 0` as `L → ∞`
(`exists_truncatedRiemannTailEnergy_le`).
The first-order term in `ε` then shows `T_v(Φ, H) = 0` for every `H`, and the injectivity of the
Riemann-kernel transform (Hamburger) gives `v = 0`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.WeilSpectral

/-! ## The tail energy of the truncated Riemann kernel tends to zero -/

theorem tendsto_integral_indicator_abs_ge {g : ℝ → ℝ} (hg : Integrable g) :
    Tendsto (fun R : ℝ => ∫ u, {u : ℝ | R ≤ |u|}.indicator g u) atTop (𝓝 0) := by
  have hmeas : ∀ R : ℝ, MeasurableSet {u : ℝ | R ≤ |u|} := fun R =>
    measurableSet_le measurable_const continuous_abs.measurable
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
    (F := fun R : ℝ => {u : ℝ | R ≤ |u|}.indicator g) (f := fun _ => (0 : ℝ)) (fun u => ‖g u‖)
    (Eventually.of_forall fun R => (hg.indicator (hmeas R)).aestronglyMeasurable)
    (Eventually.of_forall fun R => Eventually.of_forall fun u => by
      by_cases hu : u ∈ {u : ℝ | R ≤ |u|}
      · rw [Set.indicator_of_mem hu]
      · rw [Set.indicator_of_notMem hu, norm_zero]; exact norm_nonneg _)
    hg.norm
    (Eventually.of_forall fun u => tendsto_const_nhds.congr' <|
      (eventually_gt_atTop |u|).mono fun R hR =>
        (Set.indicator_of_notMem (show u ∉ {u : ℝ | R ≤ |u|} by simpa using hR) g).symm)
  simpa using h

/-- The tail energy `E_L` of the truncated Riemann kernel `Φχ_L` tends to `0`. -/
theorem exists_truncatedRiemannTailEnergy_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → truncatedRiemannTailEnergy L ≤ δ := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  set a : Fin 1 → ℂ := fun _ => 1 with ha
  have hF := superExpDecay_kernelComb a
  have hF' := superExpDecay_kernelCombDeriv a
  set g₁ : ℝ → ℝ := fun u => ‖kernelComb a u‖ * Real.exp (1 / 2 * |u|) with hg₁
  set g₂ : ℝ → ℝ := fun u =>
    ‖kernelCombDeriv a u‖ * Real.exp (1 / 2 * |u|) +
      2 * Λ * (‖kernelComb a u‖ * Real.exp (1 / 2 * |u|)) with hg₂
  have i₁ : Integrable g₁ := hF.2 (1 / 2)
  have i₂ : Integrable g₂ := (hF'.2 (1 / 2)).add ((hF.2 (1 / 2)).const_mul (2 * Λ))
  have t := (tendsto_integral_indicator_abs_ge i₁).add (tendsto_integral_indicator_abs_ge i₂)
  rw [add_zero] at t
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 ((tendsto_order.1 t).2 δ hδ)
  refine ⟨R₀ + 1, fun L hL => ?_⟩
  have hb := hR₀ (L - 1) (by linarith)
  have hmeas : MeasurableSet {u : ℝ | L - 1 ≤ |u|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hχ : ∀ u, |u| < L - 1 → bulkCutoff L u = 1 ∧ bulkCutoffDeriv L u = 0 := fun u hu =>
    ⟨bulkCutoff_eq_one hu.le, bulkCutoffDeriv_eq_zero hu⟩
  have h1 : (∫ u : ℝ, ‖nearRadicalTail L a u‖ * Real.exp (1 / 2 * |u|)) ≤
      ∫ u, {u : ℝ | L - 1 ≤ |u|}.indicator g₁ u := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity)
      (i₁.indicator hmeas) (Eventually.of_forall fun u => ?_)
    by_cases hu : L - 1 ≤ |u|
    · rw [Set.indicator_of_mem (show u ∈ {u : ℝ | L - 1 ≤ |u|} from hu)]
      simp only [hg₁, nearRadicalTail, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h0 := bulkCutoff_nonneg L u
      have h1 := bulkCutoff_le_one L u
      have : |1 - bulkCutoff L u| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have hn := norm_nonneg (kernelComb a u)
      have he := (Real.exp_pos (1 / 2 * |u|)).le
      calc ‖kernelComb a u‖ * |1 - bulkCutoff L u| * Real.exp (1 / 2 * |u|)
          ≤ ‖kernelComb a u‖ * 1 * Real.exp (1 / 2 * |u|) := by gcongr
        _ = _ := by ring
    · rw [Set.indicator_of_notMem (show u ∉ {u : ℝ | L - 1 ≤ |u|} from hu)]
      simp only [nearRadicalTail, (hχ u (not_le.mp hu)).1, sub_self, Complex.ofReal_zero, mul_zero,
        norm_zero, zero_mul, le_refl]
  have h2 : (∫ u : ℝ, ‖nearRadicalTailDeriv L a u‖ * Real.exp (1 / 2 * |u|)) ≤
      ∫ u, {u : ℝ | L - 1 ≤ |u|}.indicator g₂ u := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity)
      (i₂.indicator hmeas) (Eventually.of_forall fun u => ?_)
    by_cases hu : L - 1 ≤ |u|
    · rw [Set.indicator_of_mem (show u ∈ {u : ℝ | L - 1 ≤ |u|} from hu)]
      simp only [hg₂, nearRadicalTailDeriv]
      have h0 := bulkCutoff_nonneg L u
      have h1 := bulkCutoff_le_one L u
      have hab : |1 - bulkCutoff L u| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have hd := abs_bulkCutoffDeriv_le hΛ L u
      have he := (Real.exp_pos (1 / 2 * |u|)).le
      have hn := norm_nonneg (kernelComb a u)
      have hn' := norm_nonneg (kernelCombDeriv a u)
      have hnorm : ‖kernelCombDeriv a u * ((1 - bulkCutoff L u : ℝ) : ℂ) -
          kernelComb a u * (bulkCutoffDeriv L u : ℂ)‖ ≤
            ‖kernelCombDeriv a u‖ + 2 * Λ * ‖kernelComb a u‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
        have e1 : ‖kernelCombDeriv a u‖ * |1 - bulkCutoff L u| ≤ ‖kernelCombDeriv a u‖ := by
          nlinarith
        have e2 : ‖kernelComb a u‖ * |bulkCutoffDeriv L u| ≤ ‖kernelComb a u‖ * (2 * Λ) := by
          gcongr
        linarith
      calc ‖kernelCombDeriv a u * ((1 - bulkCutoff L u : ℝ) : ℂ) -
            kernelComb a u * (bulkCutoffDeriv L u : ℂ)‖ * Real.exp (1 / 2 * |u|)
          ≤ (‖kernelCombDeriv a u‖ + 2 * Λ * ‖kernelComb a u‖) * Real.exp (1 / 2 * |u|) := by
            gcongr
        _ = _ := by ring
    · rw [Set.indicator_of_notMem (show u ∉ {u : ℝ | L - 1 ≤ |u|} from hu)]
      obtain ⟨e1, e2⟩ := hχ u (not_le.mp hu)
      simp only [nearRadicalTailDeriv, e1, e2, sub_self, Complex.ofReal_zero, mul_zero,
        norm_zero, zero_mul, le_refl]
  calc truncatedRiemannTailEnergy L
      = (∫ u : ℝ, ‖nearRadicalTail L a u‖ * Real.exp (1 / 2 * |u|)) +
          ∫ u : ℝ, ‖nearRadicalTailDeriv L a u‖ * Real.exp (1 / 2 * |u|) := rfl
    _ ≤ (∫ u, {u : ℝ | L - 1 ≤ |u|}.indicator g₁ u) + ∫ u, {u : ℝ | L - 1 ≤ |u|}.indicator g₂ u :=
        add_le_add h1 h2
    _ ≤ δ := hb.le

/-! ## Size of the perturbed kernel at the critical zeros -/

theorem gammaOf_half_add (r : ℝ) : gammaOf ((1 / 2 : ℂ) + r * I) = r := by
  unfold gammaOf
  rw [show (1 / 2 : ℂ) + r * I - 1 / 2 = r * I by ring, mul_div_assoc, div_self I_ne_zero, mul_one]

/-- The zero `½ + ir` of `ζ` as a point of the zero configuration. -/
def criticalZero {r : ℝ} (hr : riemannZeta ((1 / 2 : ℂ) + r * I) = 0) :
    zetaZeroConfig.carrier :=
  ⟨(1 / 2 : ℂ) + r * I,
    show IsNontrivialZero ((1 / 2 : ℂ) + r * I) from ⟨hr, by norm_num, by norm_num⟩⟩

theorem paperFT_perturbedKernel (L ε : ℝ) {H : ℝ → ℝ} (hH : Continuous H)
    (hHc : HasCompactSupport H) (z : ℂ) :
    paperFT (fun u => (perturbedKernel L ε H u : ℂ)) z =
      paperFT (truncatedRiemannKernel L) z + (ε : ℂ) * paperFT (fun u => (H u : ℂ)) z := by
  rw [ofReal_perturbedKernel]
  unfold paperFT
  have h0 : Integrable fun u : ℝ => truncatedRiemannKernel L u * Complex.exp (I * z * u) := by
    simpa using integrable_translate_mul_cexp L 0 z
  have h1 := (integrable_ofReal_mul_cexp_of_hasCompactSupport hH hHc z).const_mul (ε : ℂ)
  rw [← integral_const_mul, ← integral_add h0 h1]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only; ring

/-- At a critical zero `½ + ir`: `(1 + |r|) |(Φχ_L + εH)^(r)| ≤ E_L + |ε| E_H`. -/
theorem perturbedKernel_criticalZero_le (L ε : ℝ) {H : ℝ → ℝ} (hH : ContDiff ℝ 2 H)
    (hHc : HasCompactSupport H) {r : ℝ} (hr : riemannZeta ((1 / 2 : ℂ) + r * I) = 0) :
    (1 + |r|) * ‖paperFT (fun u => (perturbedKernel L ε H u : ℂ)) r‖ ≤
      truncatedRiemannTailEnergy L + |ε| * testEnergy H := by
  obtain ⟨Λ', -, hΛ'⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  have hγ : gammaOf ((criticalZero hr : zetaZeroConfig.carrier) : ℂ) = r := gammaOf_half_add r
  have him : ((criticalZero hr : zetaZeroConfig.carrier) : ℂ).im = r := by
    simp [criticalZero]
  have hu1 := (truncatedRiemannKernel_zero_bound L hΛ' (criticalZero hr)).1
  have hh1 := (test_zero_bound hH hHc (criticalZero hr)).1
  rw [hγ, him] at hu1 hh1
  rw [paperFT_perturbedKernel L ε hH.continuous hHc]
  have hd : 0 ≤ 1 + |r| := by positivity
  calc (1 + |r|) * ‖paperFT (truncatedRiemannKernel L) r + (ε : ℂ) * paperFT (fun u => (H u : ℂ)) r‖
      ≤ (1 + |r|) * ‖paperFT (truncatedRiemannKernel L) r‖ +
          |ε| * ((1 + |r|) * ‖paperFT (fun u => (H u : ℂ)) r‖) := by
        have := norm_add_le (paperFT (truncatedRiemannKernel L) r)
          ((ε : ℂ) * paperFT (fun u => (H u : ℂ)) r)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at this
        nlinarith
    _ ≤ _ := by nlinarith [abs_nonneg ε]

/-! ## The pairing is controlled by the size of the test at the zeros -/

/-- `∫ (1 + r²)⁻¹ dμ_lam = Re Φ_lam(3/2)`. -/
theorem integrable_inv_one_add_sq_boundaryMeasure {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Integrable (fun r : ℝ => 1 / (1 + r ^ 2)) (boundaryMeasure hW) ∧
      ∫ r, 1 / (1 + r ^ 2) ∂boundaryMeasure hW =
        (weilContinuation hW (((3 / 2 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I)).re := by
  have h := ofReal_re_weilContinuation_eq hW (3 / 2) 0 (by norm_num)
  have e : ∀ r : ℝ, ((3 / 2 : ℝ) - 1 / 2) / (((3 / 2 : ℝ) - 1 / 2) ^ 2 + (r - 0) ^ 2) =
      1 / (1 + r ^ 2) := fun r => by norm_num
  simp only [e] at h
  have hfin : ∫⁻ r, ENNReal.ofReal (1 / (1 + r ^ 2)) ∂boundaryMeasure hW ≠ ⊤ := by
    rw [← h]; exact ENNReal.ofReal_ne_top
  have hmeas : Measurable fun r : ℝ => 1 / (1 + r ^ 2) := by fun_prop
  have hint : Integrable (fun r : ℝ => 1 / (1 + r ^ 2)) (boundaryMeasure hW) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun r => by positivity)]
    exact lt_of_le_of_ne le_top hfin
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun r => by positivity)
    hmeas.aestronglyMeasurable, ← h, ENNReal.toReal_ofReal]
  have := re_weilContinuation_nonneg hW
    (show (1 / 2 : ℝ) < (((3 / 2 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I).re by simp; norm_num)
  exact this

/-- On a measure carried by the critical zeros, a test small at the zeros has small energy:
if `(1 + |r|)|f̂(r)| ≤ E` at every critical zero, then `∫ |f̂|² dμ ≤ E² ∫ (1 + r²)⁻¹ dμ`. -/
theorem integral_norm_sq_paperFT_le_of_carried {μ : Measure ℝ}
    (hZ : μ {r : ℝ | riemannZeta ((1 / 2 : ℂ) + r * I) ≠ 0} = 0)
    (hint : Integrable (fun r : ℝ => 1 / (1 + r ^ 2)) μ) {f : ℝ → ℂ} (hf : Integrable f) {E : ℝ}
    (hE : ∀ r : ℝ, riemannZeta ((1 / 2 : ℂ) + r * I) = 0 → (1 + |r|) * ‖paperFT f r‖ ≤ E) :
    Integrable (fun r : ℝ => ‖paperFT f r‖ ^ 2) μ ∧
      ∫ r, ‖paperFT f r‖ ^ 2 ∂μ ≤ E ^ 2 * ∫ r, 1 / (1 + r ^ 2) ∂μ := by
  have hae : ∀ᵐ (r : ℝ) ∂μ, riemannZeta ((1 / 2 : ℂ) + (r : ℂ) * I) = 0 := by
    rw [ae_iff]; simpa using hZ
  have hbound : ∀ᵐ (r : ℝ) ∂μ, ‖paperFT f r‖ ^ 2 ≤ E ^ 2 * (1 / (1 + r ^ 2)) := by
    filter_upwards [hae] with r hr
    have h1 := hE r hr
    have hn := norm_nonneg (paperFT f r)
    have h2 : ‖paperFT f r‖ ≤ E / (1 + |r|) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h3 : ‖paperFT f r‖ ^ 2 ≤ (E / (1 + |r|)) ^ 2 := pow_le_pow_left₀ hn h2 2
    have h4 : (E / (1 + |r|)) ^ 2 ≤ E ^ 2 * (1 / (1 + r ^ 2)) := by
      rw [div_pow, mul_one_div]
      have hsq : 1 + r ^ 2 ≤ (1 + |r|) ^ 2 := by nlinarith [abs_nonneg r, sq_abs r]
      exact div_le_div_of_nonneg_left (sq_nonneg E) (by positivity) hsq
    linarith
  have hmeas : AEStronglyMeasurable (fun r : ℝ => ‖paperFT f r‖ ^ 2) μ :=
    ((WeilHerglotz.continuous_paperFT_real hf).norm.pow 2).aestronglyMeasurable
  have hi : Integrable (fun r : ℝ => ‖paperFT f r‖ ^ 2) μ :=
    (hint.const_mul (E ^ 2)).mono' hmeas (hbound.mono fun r hr => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hr)
  refine ⟨hi, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono_ae hi (hint.const_mul _) hbound

/-- **The pairing at a test small on the zeros.**  If `μ_lam` is carried by the critical zeros
and `(1 + |r|)|F̂(r)| ≤ E` at every critical zero `½ + ir`, then
`|T_v(F, F)| ≤ ‖W_ζ(F, F)‖ + E² ∫ (1 + r²)⁻¹ dμ_lam`, with `v = lam − Λ`. -/
theorem abs_atomPairing_le_of_carried {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hZ : boundaryMeasure hW {r : ℝ | riemannZeta ((1 / 2 : ℂ) + r * I) ≠ 0} = 0)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 2 fun u => (F u : ℂ)) (hFc : HasCompactSupport F) {E : ℝ}
    (hE : ∀ r : ℝ, riemannZeta ((1 / 2 : ℂ) + r * I) = 0 →
      (1 + |r|) * ‖paperFT (fun u => (F u : ℂ)) r‖ ≤ E) :
    |atomPairing (fun n => lam n - ArithmeticFunction.vonMangoldt n) (crossCorr F F)| ≤
      ‖zetaZeroConfig.W (fun u => (F u : ℂ)) (fun u => (F u : ℂ))‖ +
        E ^ 2 * ∫ r, 1 / (1 + r ^ 2) ∂boundaryMeasure hW := by
  set μ := boundaryMeasure hW
  set f : ℝ → ℂ := fun u => (F u : ℂ) with hf
  have hfc : HasCompactSupport f := hFc.comp_left Complex.ofReal_zero
  obtain ⟨hint, -⟩ := integrable_inv_one_add_sq_boundaryMeasure hW
  -- the explicit formula for `Λ + (lam − Λ) = lam`
  have h := re_weilFullFunctional_add_eq (fun n => lam n - ArithmeticFunction.vonMangoldt n) hF hFc
  simp only [add_sub_cancel] at h
  rw [weilFullFunctional_weilTest_self_eq_integral hW hF hfc, integral_complex_ofReal,
    Complex.ofReal_re] at h
  -- the spectral side is small
  have hI := (integral_norm_sq_paperFT_le_of_carried hZ hint
    (hF.continuous.integrable_of_hasCompactSupport hfc) hE).2
  have hI0 : 0 ≤ ∫ r, ‖paperFT f r‖ ^ 2 ∂μ := integral_nonneg fun _ => by positivity
  have hW0 := Complex.abs_re_le_norm (zetaZeroConfig.W f f)
  rw [abs_le] at hW0 ⊢
  constructor <;> linarith [hW0.1, hW0.2]

/-! ## The first-order inequality -/

/-- An abstract pairing `T` on correlation functions that expands to second order along
`Φχ_L + εH`.  If `|T(Φχ_L + eH, Φχ_L + eH)| ≤ K (E_L + |e| E_H)²` for every `e`, then
`2ε |T(Φχ_L, H)| ≤ K E_L² + K (E_L + εE_H)² + ε² |T(H, H)|`. -/
theorem two_mul_abs_pairing_le_of_bound {T : (ℝ → ℝ) → ℝ} {K : ℝ} {H : ℝ → ℝ} (L : ℝ)
    (hexp : ∀ e : ℝ, T (crossCorr (perturbedKernel L e H) (perturbedKernel L e H)) =
      T (crossCorr (truncatedRiemannKernelReal L) (truncatedRiemannKernelReal L)) +
        2 * e * T (crossCorr (truncatedRiemannKernelReal L) H) + e ^ 2 * T (crossCorr H H))
    (bound : ∀ e : ℝ, |T (crossCorr (perturbedKernel L e H) (perturbedKernel L e H))| ≤
      K * (truncatedRiemannTailEnergy L + |e| * testEnergy H) ^ 2) {ε : ℝ} (hε : 0 < ε) :
    2 * ε * |T (crossCorr (truncatedRiemannKernelReal L) H)| ≤
      K * truncatedRiemannTailEnergy L ^ 2 +
        K * (truncatedRiemannTailEnergy L + ε * testEnergy H) ^ 2 +
        ε ^ 2 * |T (crossCorr H H)| := by
  have b0 := bound 0
  have b1 := bound ε
  rw [hexp 0] at b0
  rw [hexp ε, abs_of_pos hε] at b1
  simp only [abs_zero, zero_mul, add_zero, mul_zero, zero_pow two_ne_zero] at b0
  set T0 := T (crossCorr (truncatedRiemannKernelReal L) (truncatedRiemannKernelReal L))
  set T1 := T (crossCorr (truncatedRiemannKernelReal L) H)
  set T2 := T (crossCorr H H)
  have key : 2 * ε * T1 = (T0 + 2 * ε * T1 + ε ^ 2 * T2) - T0 - ε ^ 2 * T2 := by ring
  have hT2 : |ε ^ 2 * T2| = ε ^ 2 * |T2| := by rw [abs_mul, abs_of_nonneg (sq_nonneg ε)]
  calc 2 * ε * |T1| = |2 * ε * T1| := by rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * ε)]
    _ = |(T0 + 2 * ε * T1 + ε ^ 2 * T2) - T0 - ε ^ 2 * T2| := by rw [← key]
    _ ≤ |T0 + 2 * ε * T1 + ε ^ 2 * T2| + |T0| + |ε ^ 2 * T2| := by
        have h1 := abs_sub (T0 + 2 * ε * T1 + ε ^ 2 * T2 - T0) (ε ^ 2 * T2)
        have h2 := abs_sub (T0 + 2 * ε * T1 + ε ^ 2 * T2) T0
        linarith
    _ ≤ _ := by rw [hT2]; linarith

/-- **The pairing with `Φ` vanishes.**  Let `T` be a pairing on correlation functions that expands
to second order along `Φχ_L + εH` and whose values on `Φχ_L ⋆ H` converge to those on `Φ ⋆ H` at
rate `e^{−2(L−1)}`.  If `|T(Φχ_L + eH, Φχ_L + eH)| ≤ K (E_L + |e| E_H)²` for all tests `H` and all
`L, e`, then `T(Φ ⋆ H) = 0` for every test `H`. -/
theorem pairing_riemannKernel_eq_zero_of_bound {T : (ℝ → ℝ) → ℝ}
    (hexp : ∀ H : ℝ → ℝ, Continuous H → HasCompactSupport H → ∀ L e : ℝ,
      T (crossCorr (perturbedKernel L e H) (perturbedKernel L e H)) =
        T (crossCorr (truncatedRiemannKernelReal L) (truncatedRiemannKernelReal L)) +
          2 * e * T (crossCorr (truncatedRiemannKernelReal L) H) + e ^ 2 * T (crossCorr H H))
    (htr : ∀ H : ℝ → ℝ, Continuous H → HasCompactSupport H → ∃ Kt : ℝ, 0 ≤ Kt ∧ ∀ L : ℝ,
      |T (crossCorr (truncatedRiemannKernelReal L) H) - T (crossCorr riemannKernelReal H)| ≤
        Kt * Real.exp (-(2 * (L - 1))))
    {K : ℝ} (hK0 : 0 ≤ K)
    (hb : ∀ H : ℝ → ℝ, ContDiff ℝ 2 H → HasCompactSupport H → ∀ L e : ℝ,
      |T (crossCorr (perturbedKernel L e H) (perturbedKernel L e H))| ≤
        K * (truncatedRiemannTailEnergy L + |e| * testEnergy H) ^ 2) :
    ∀ H : ℝ → ℝ, ContDiff ℝ 2 H → HasCompactSupport H → T (crossCorr riemannKernelReal H) = 0 := by
  have hKineq : ∀ H : ℝ → ℝ, ContDiff ℝ 2 H → HasCompactSupport H → ∀ (L : ℝ) {ε : ℝ},
      0 < ε → 2 * ε * |T (crossCorr (truncatedRiemannKernelReal L) H)| ≤
        K * truncatedRiemannTailEnergy L ^ 2 +
          K * (truncatedRiemannTailEnergy L + ε * testEnergy H) ^ 2 +
          ε ^ 2 * |T (crossCorr H H)| := fun H hH hHc L _ hε =>
    two_mul_abs_pairing_le_of_bound L (hexp H hH.continuous hHc L) (hb H hH hHc L) hε
  intro H hH2 hHc
  obtain ⟨Tv, hT⟩ : ∃ Tv, Tv = T (crossCorr riemannKernelReal H) := ⟨_, rfl⟩
  rw [← hT]
  by_contra hT0
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = |Tv| := ⟨_, rfl⟩
  have hτ0 : 0 < τ := hτ ▸ abs_pos.mpr hT0
  obtain ⟨T2, hT2⟩ : ∃ T2, T2 = T (crossCorr H H) := ⟨_, rfl⟩
  obtain ⟨EH, hEH⟩ : ∃ EH, EH = testEnergy H := ⟨_, rfl⟩
  obtain ⟨M₂, hM₂⟩ : ∃ M₂, M₂ = K * (2 * EH ^ 2) + |T2| := ⟨_, rfl⟩
  have hM₂0 : 0 ≤ M₂ := by rw [hM₂]; positivity
  obtain ⟨ε, hε⟩ : ∃ ε, ε = τ / (2 * M₂ + 2) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by rw [hε]; positivity
  obtain ⟨Kt, hKt0, hKt⟩ := htr H hH2.continuous hHc
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = min 1 (ε * τ / (12 * (K + 1))) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; exact lt_min one_pos (by positivity)
  obtain ⟨L₁, hL₁⟩ := exists_truncatedRiemannTailEnergy_le hδpos
  obtain ⟨L, hL⟩ : ∃ L, L = max L₁ (1 + 2 * Kt / τ) := ⟨_, rfl⟩
  have hEL := hL₁ L (hL ▸ le_max_left _ _)
  obtain ⟨EL, hELdef⟩ : ∃ EL, EL = truncatedRiemannTailEnergy L := ⟨_, rfl⟩
  rw [← hELdef] at hEL
  have hEL0 : 0 ≤ EL := hELdef ▸ truncatedRiemannTailEnergy_nonneg L
  have hKEL : K * EL ^ 2 ≤ ε * τ / 12 := by
    have h1 : EL ≤ 1 := hEL.trans (hδ ▸ min_le_left _ _)
    have h2 : EL ≤ ε * τ / (12 * (K + 1)) := hEL.trans (hδ ▸ min_le_right _ _)
    have h3 : EL ^ 2 ≤ EL := by nlinarith
    have h4 : K * EL ≤ ε * τ / 12 := by
      have : (K + 1) * EL ≤ ε * τ / 12 := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 12 * (K + 1))] at h2
        nlinarith
      nlinarith
    nlinarith
  have hLK : Kt * Real.exp (-(2 * (L - 1))) ≤ τ / 4 := by
    have h1 : 4 * Kt / τ ≤ Real.exp (2 * (L - 1)) := by
      have := Real.add_one_le_exp (2 * (L - 1))
      have hL2 : 1 + 2 * Kt / τ ≤ L := hL ▸ le_max_right _ _
      have : 4 * Kt / τ = 2 * (2 * Kt / τ) := by ring
      linarith
    have hE : Real.exp (-(2 * (L - 1))) * Real.exp (2 * (L - 1)) = 1 := by
      rw [← Real.exp_add]; simp
    rw [div_le_iff₀ hτ0] at h1
    have hEpos := Real.exp_pos (-(2 * (L - 1)))
    nlinarith
  have hineq := hKineq H hH2 hHc L hεpos
  rw [← hELdef, ← hEH, ← hT2] at hineq
  obtain ⟨T1, hT1def⟩ : ∃ T1, T1 = T (crossCorr (truncatedRiemannKernelReal L) H) :=
    ⟨_, rfl⟩
  rw [← hT1def] at hineq
  have hsq : (EL + ε * EH) ^ 2 ≤ 2 * EL ^ 2 + 2 * (ε ^ 2 * EH ^ 2) := by
    nlinarith [sq_nonneg (EL - ε * EH)]
  have hT1 : 2 * ε * |T1| ≤ ε * τ / 4 + ε ^ 2 * M₂ := by
    have : K * (EL + ε * EH) ^ 2 ≤ 2 * (K * EL ^ 2) + ε ^ 2 * (K * (2 * EH ^ 2)) := by
      have h := mul_le_mul_of_nonneg_left hsq hK0
      linarith
    rw [hM₂]
    nlinarith [abs_nonneg T2]
  have hT1' : |T1| ≤ τ / 8 + ε * M₂ / 2 := by
    have : 2 * ε * |T1| ≤ 2 * ε * (τ / 8 + ε * M₂ / 2) := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  have hεM : ε * M₂ ≤ τ / 2 := by
    rw [hε, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hdiff : |T1 - Tv| ≤ τ / 4 := by rw [hT1def, hT]; exact (hKt L).trans hLK
  have htri : |Tv| - |T1| ≤ |Tv - T1| := abs_sub_abs_le_abs_sub Tv T1
  rw [abs_sub_comm] at htri
  rw [← hτ] at htri
  linarith

/-- **The pairing on the perturbed Riemann kernel forces `w = 0`.**  If
`|T_w(Φχ_L + eH, Φχ_L + eH)| ≤ K (E_L + |e| E_H)²` for all tests `H` and all `L, e`, then
`w(n) = 0` for every `n ≥ 2`. -/
theorem eq_zero_of_perturbedKernel_bound {w : ℕ → ℝ}
    (hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2) {K : ℝ} (hK0 : 0 ≤ K)
    (hb : ∀ H : ℝ → ℝ, ContDiff ℝ 2 H → HasCompactSupport H → ∀ L e : ℝ,
      |atomPairing w (crossCorr (perturbedKernel L e H) (perturbedKernel L e H))| ≤
        K * (truncatedRiemannTailEnergy L + |e| * testEnergy H) ^ 2) :
    ∀ n, 2 ≤ n → w n = 0 :=
  eq_zero_of_forall_atomPairing_riemannKernel_eq_zero hw2
    (pairing_riemannKernel_eq_zero_of_bound (T := atomPairing w)
      (fun _ hH hHc L e => atomPairing_perturbedKernel w L e hH hHc)
      (fun _ hH hHc => exists_abs_atomPairing_truncated_sub_le hw2 hH hHc) hK0 hb)

/-! ## The theorem -/

/-- **A Weil-positive system carried by the critical zeros is `Λ`.**  If the boundary measure of a
full-cone Weil-positive `lam` gives no mass to `{r : ζ(½ + ir) ≠ 0}`, then `lam(n) = Λ(n)` for
every `n ≥ 2`.  Unconditional; no bound on the atoms of `μ_lam` is assumed. -/
theorem eq_vonMangoldt_of_boundaryMeasure_criticalZeros {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hZ : boundaryMeasure hW {r : ℝ | riemannZeta ((1 / 2 : ℂ) + r * I) ≠ 0} = 0) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ, w = fun n => lam n - ArithmeticFunction.vonMangoldt n := ⟨_, rfl⟩
  have hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2 := hw ▸ summable_sub_vonMangoldt_div_sq hW
  have hM0 : 0 ≤ ∫ r, 1 / (1 + r ^ 2) ∂boundaryMeasure hW := integral_nonneg fun r => by positivity
  have hS0 := zetaInvSqSum_nonneg
  have hzero := eq_zero_of_perturbedKernel_bound hw2
    (K := (5 / 4) * zetaInvSqSum + ∫ r, 1 / (1 + r ^ 2) ∂boundaryMeasure hW) (by positivity)
    fun H hH hHc L e => by
      have h := abs_atomPairing_le_of_carried hW hZ (contDiff_perturbedKernel L e hH)
        (hasCompactSupport_perturbedKernel L e hHc)
        (fun r hr => perturbedKernel_criticalZero_le L e hH hHc hr)
      have hZW := norm_W_perturbedKernel_le L e hH hHc
      rw [← hw] at h
      nlinarith [sq_nonneg (truncatedRiemannTailEnergy L + |e| * testEnergy H)]
  intro n hn
  have := hzero n hn
  rw [hw] at this
  linarith

/-! ## Signed measures carried by the critical zeros -/

/-- **No signed spectral measure on the critical zeros has its spectrum on `±log ℕ`.**  Let
`ν = ν₊ − ν₋` with `ν±` carried by the critical zeros and `∫ (1 + r²)⁻¹ dν± < ∞`, and suppose that
for every real `C²` compactly supported test `F`,
`∫ |F̂|² dν₊ − ∫ |F̂|² dν₋ = Σ_{n ≥ 2} w(n) n^{−1/2} (k_F(log n) + k_F(−log n))`, `k_F = F ⋆ F̃`,
with `Σ |w(n)| n^{−2} < ∞`.  Then `w(n) = 0` for every `n ≥ 2`.

That is, a measure carried by `{r : ζ(½ + ir) = 0}` whose Fourier transform is a discrete measure
on `±log ℕ_{≥2}` vanishes.  No sign or size condition is placed on the atoms of `ν`. -/
theorem eq_zero_of_signedMeasure_criticalZeros {w : ℕ → ℝ}
    (hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2) {νp νm : Measure ℝ}
    (hZp : νp {r : ℝ | riemannZeta ((1 / 2 : ℂ) + r * I) ≠ 0} = 0)
    (hZm : νm {r : ℝ | riemannZeta ((1 / 2 : ℂ) + r * I) ≠ 0} = 0)
    (hip : Integrable (fun r : ℝ => 1 / (1 + r ^ 2)) νp)
    (him : Integrable (fun r : ℝ => 1 / (1 + r ^ 2)) νm)
    (hrep : ∀ F : ℝ → ℝ, ContDiff ℝ 2 (fun u => (F u : ℂ)) → HasCompactSupport F →
      atomPairing w (crossCorr F F) =
        (∫ r, ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2 ∂νp) -
          ∫ r, ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2 ∂νm) :
    ∀ n, 2 ≤ n → w n = 0 := by
  have hMp : 0 ≤ ∫ r, 1 / (1 + r ^ 2) ∂νp := integral_nonneg fun r => by positivity
  have hMm : 0 ≤ ∫ r, 1 / (1 + r ^ 2) ∂νm := integral_nonneg fun r => by positivity
  refine eq_zero_of_perturbedKernel_bound hw2
    (K := (∫ r, 1 / (1 + r ^ 2) ∂νp) + ∫ r, 1 / (1 + r ^ 2) ∂νm) (by positivity)
    fun H hH hHc L e => ?_
  have hF := contDiff_perturbedKernel L e hH
  have hFc := hasCompactSupport_perturbedKernel L e hHc
  have hfi : Integrable fun u => (perturbedKernel L e H u : ℂ) :=
    hF.continuous.integrable_of_hasCompactSupport (hFc.comp_left Complex.ofReal_zero)
  have hE : ∀ r : ℝ, riemannZeta ((1 / 2 : ℂ) + r * I) = 0 →
      (1 + |r|) * ‖paperFT (fun u => (perturbedKernel L e H u : ℂ)) r‖ ≤
        truncatedRiemannTailEnergy L + |e| * testEnergy H := fun r hr =>
    perturbedKernel_criticalZero_le L e hH hHc hr
  obtain ⟨-, hp⟩ := integral_norm_sq_paperFT_le_of_carried hZp hip hfi hE
  obtain ⟨-, hm⟩ := integral_norm_sq_paperFT_le_of_carried hZm him hfi hE
  have pp : 0 ≤ ∫ r, ‖paperFT (fun u => (perturbedKernel L e H u : ℂ)) r‖ ^ 2 ∂νp :=
    integral_nonneg fun _ => by positivity
  have pm : 0 ≤ ∫ r, ‖paperFT (fun u => (perturbedKernel L e H u : ℂ)) r‖ ^ 2 ∂νm :=
    integral_nonneg fun _ => by positivity
  rw [hrep _ hF hFc, abs_le]
  constructor <;> nlinarith

/-! ## Measures with a density term -/

/-- `2c g(0) + T_w(g)`: the pairing of a measure whose Fourier transform is
`c δ₀ + Σ_{n ≥ 2} w(n) n^{−1/2} (δ_{log n} + δ_{−log n})` with a correlation function `g`. -/
def densityPairing (c : ℝ) (w : ℕ → ℝ) (g : ℝ → ℝ) : ℝ := 2 * c * g 0 + atomPairing w g

theorem densityPairing_perturbedKernel (c : ℝ) (w : ℕ → ℝ) (L ε : ℝ) {H : ℝ → ℝ}
    (hH : Continuous H) (hHc : HasCompactSupport H) :
    densityPairing c w (crossCorr (perturbedKernel L ε H) (perturbedKernel L ε H)) =
      densityPairing c w
          (crossCorr (truncatedRiemannKernelReal L) (truncatedRiemannKernelReal L)) +
        2 * ε * densityPairing c w (crossCorr (truncatedRiemannKernelReal L) H) +
        ε ^ 2 * densityPairing c w (crossCorr H H) := by
  unfold densityPairing
  rw [atomPairing_perturbedKernel w L ε hH hHc, crossCorr_perturbedKernel L ε hH hHc 0]
  have hswap : crossCorr H (truncatedRiemannKernelReal L) 0 =
      crossCorr (truncatedRiemannKernelReal L) H 0 := by
    rw [crossCorr_swap, neg_zero]
  rw [hswap]; ring

/-- **Truncation limit for the density pairing.** -/
theorem exists_abs_densityPairing_truncated_sub_le (c : ℝ) {w : ℕ → ℝ}
    (hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2) {H : ℝ → ℝ} (hH : Continuous H)
    (hHc : HasCompactSupport H) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℝ,
      |densityPairing c w (crossCorr (truncatedRiemannKernelReal L) H) -
        densityPairing c w (crossCorr riemannKernelReal H)| ≤ K * Real.exp (-(2 * (L - 1))) := by
  obtain ⟨K₁, hK₁, h₁⟩ := exists_abs_atomPairing_truncated_sub_le hw2 hH hHc
  obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le
  obtain ⟨R, hR0, hR⟩ := exists_vanish_of_hasCompactSupport hHc
  obtain ⟨M, hM⟩ : ∃ M, ∀ t, |H t| ≤ M := by
    obtain ⟨M, hM⟩ := hH.bounded_above_of_compact_support hHc
    exact ⟨M, fun t => by rw [← Real.norm_eq_abs]; exact hM t⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine ⟨K₁ + 2 * |c| * (M * C * (2 * R) * Real.exp (2 * R)), by positivity, fun L => ?_⟩
  have h0 : |crossCorr (truncatedRiemannKernelReal L) H 0 - crossCorr riemannKernelReal H 0| ≤
      M * C * (2 * R) * Real.exp (2 * R) * Real.exp (-(2 * (L - 1))) := by
    have e : crossCorr (truncatedRiemannKernelReal L) H 0 - crossCorr riemannKernelReal H 0 =
        ∫ t, (truncatedRiemannKernelReal L t - riemannKernelReal t) * H (t - 0) := by
      simp only [crossCorr]
      rw [← integral_sub
        (integrable_mul_translate_right (continuous_truncatedRiemannKernelReal L) hH hHc 0)
        (integrable_mul_translate_right continuous_riemannKernelReal hH hHc 0)]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only; ring
    rw [e]
    have h := abs_integral_mul_translate_le (A := C * Real.exp (-(2 * (L - 1))))
      (Z := fun t => truncatedRiemannKernelReal L t - riemannKernelReal t) (by positivity) hM0
      hR0 (fun t => by
        obtain ⟨h1, h2⟩ := riemannKernelReal_sub_truncated_le hC L t
        rw [abs_sub_comm, abs_of_nonneg h1]; exact h2) hM hR 0
    rw [abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at h
    calc _ ≤ _ := h
      _ = _ := by ring
  unfold densityPairing
  have hat := h₁ L
  have e2 : 2 * c * crossCorr (truncatedRiemannKernelReal L) H 0 +
        atomPairing w (crossCorr (truncatedRiemannKernelReal L) H) -
      (2 * c * crossCorr riemannKernelReal H 0 + atomPairing w (crossCorr riemannKernelReal H)) =
      2 * c * (crossCorr (truncatedRiemannKernelReal L) H 0 - crossCorr riemannKernelReal H 0) +
        (atomPairing w (crossCorr (truncatedRiemannKernelReal L) H) -
          atomPairing w (crossCorr riemannKernelReal H)) := by ring
  rw [e2]
  have hE := (Real.exp_pos (-(2 * (L - 1)))).le
  calc _ ≤ |2 * c * (crossCorr (truncatedRiemannKernelReal L) H 0 -
          crossCorr riemannKernelReal H 0)| + |atomPairing w
            (crossCorr (truncatedRiemannKernelReal L) H) -
          atomPairing w (crossCorr riemannKernelReal H)| := abs_add_le _ _
    _ ≤ 2 * |c| * (M * C * (2 * R) * Real.exp (2 * R) * Real.exp (-(2 * (L - 1)))) +
          K₁ * Real.exp (-(2 * (L - 1))) := by
        rw [abs_mul, abs_mul, abs_two]
        gcongr
    _ = _ := by ring

/-- **Injectivity with a density term.**  If `2c (Φ ⋆ H)(0) + T_w(Φ ⋆ H) = 0` for every test `H`,
then `c = 0` and `w(n) = 0` for every `n ≥ 2`. -/
theorem eq_zero_of_forall_densityPairing_riemannKernel_eq_zero {c : ℝ} {w : ℕ → ℝ}
    (hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2)
    (hstep : ∀ H : ℝ → ℝ, ContDiff ℝ 2 H → HasCompactSupport H →
      densityPairing c w (crossCorr riemannKernelReal H) = 0) :
    c = 0 ∧ ∀ n, 2 ≤ n → w n = 0 := by
  have hWc := continuous_weightKernelTransform hw2
  have hGc : Continuous fun s => 2 * c * riemannKernelReal s + weightKernelTransform w s :=
    (continuous_const.mul continuous_riemannKernelReal).add hWc
  have hG : ∀ s, 2 * c * riemannKernelReal s + weightKernelTransform w s = 0 := by
    have hae : ∀ᵐ x ∂(volume : Measure ℝ),
        2 * c * riemannKernelReal x + weightKernelTransform w x = 0 := by
      refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hGc.locallyIntegrable fun g hg hgc => ?_
      have h := hstep g (hg.of_le (WithTop.coe_le_coe.mpr le_top)) hgc
      unfold densityPairing at h
      rw [atomPairing_riemannKernel_eq_integral hw2 hg.continuous hgc] at h
      have e0 : crossCorr riemannKernelReal g 0 = ∫ s, g s * riemannKernelReal s := by
        simp only [crossCorr, sub_zero]
        congr 1; ext s; ring
      rw [e0] at h
      have i1 : Integrable fun s => g s * riemannKernelReal s :=
        (hg.continuous.mul continuous_riemannKernelReal).integrable_of_hasCompactSupport
          hgc.mul_right
      have i2 : Integrable fun s => g s * weightKernelTransform w s :=
        (hg.continuous.mul hWc).integrable_of_hasCompactSupport hgc.mul_right
      simp only [smul_eq_mul]
      rw [show (fun x => g x * (2 * c * riemannKernelReal x + weightKernelTransform w x)) =
          fun x => 2 * c * (g x * riemannKernelReal x) + g x * weightKernelTransform w x from
          funext fun x => by ring, integral_add (i1.const_mul _) i2, integral_const_mul]
      linarith
    exact fun s => congrFun ((hGc.ae_eq_iff_eq volume continuous_const).mp hae) s
  -- the transform with weight `c` at `n = 1`
  set w' : ℕ → ℝ := fun n => if n = 1 then c else if 2 ≤ n then w n else 0 with hw'
  have hsum' : Summable fun n : ℕ => |w' (n + 1)| / ((n : ℝ) + 1) ^ (2 : ℝ) := by
    have h := (summable_nat_add_iff 1).mpr hw2
    have hfin : Summable fun n : ℕ => if n = 0 then |c| else 0 :=
      summable_of_ne_finset_zero (s := {0}) fun n hn => by
        rw [Finset.mem_singleton] at hn; simp [hn]
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) (h.add hfin)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    simp only [hw']
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have h1 : n + 1 ≠ 1 := by omega
      have h2 : 2 ≤ n + 1 := by omega
      simp only [h1, if_false, h2, if_true, hn.ne', if_false, add_zero]
      push_cast; exact le_rfl
  have hG' : ∀ y : ℝ, ∑' n : ℕ, w' (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ) *
      (riemannKernelReal (y - Real.log ((n + 1 : ℕ) : ℝ)) +
        riemannKernelReal (y + Real.log ((n + 1 : ℕ) : ℝ))) = 0 := by
    intro y
    set g : ℕ → ℝ := fun m => w' m / Real.sqrt (m : ℝ) *
      (riemannKernelReal (y - Real.log (m : ℝ)) + riemannKernelReal (y + Real.log (m : ℝ)))
      with hgdef
    set h : ℕ → ℝ := fun m => (if 2 ≤ m then w m / Real.sqrt m else 0) *
      (riemannKernelReal (y + Real.log m) + riemannKernelReal (y - Real.log m)) with hhdef
    have hgh : ∀ m, g m = h m + if m = 1 then 2 * c * riemannKernelReal y else 0 := by
      intro m
      simp only [hgdef, hhdef, hw']
      rcases Nat.lt_or_ge m 2 with hm | hm
      · interval_cases m
        · simp
        · simp; ring
      · have h1 : m ≠ 1 := by omega
        simp only [h1, if_false, hm, if_true, add_zero]
        ring
    have hs : Summable g := by
      have hfin : Summable fun m : ℕ => if m = 1 then 2 * c * riemannKernelReal y else 0 :=
        summable_of_ne_finset_zero (s := {1}) fun m hm => by
          rw [Finset.mem_singleton] at hm; simp [hm]
      exact ((summable_weightTerm hw2 y).add hfin).congr fun m => (hgh m).symm
    have hshift : ∑' n : ℕ, g (n + 1) = ∑' m, g m := by
      rw [hs.tsum_eq_zero_add]
      have : g 0 = 0 := by simp [hgdef, hw']
      rw [this, zero_add]
    have htot : ∑' m, g m = weightKernelTransform w y + 2 * c * riemannKernelReal y := by
      have hfin : Summable fun m : ℕ => if m = 1 then 2 * c * riemannKernelReal y else 0 :=
        summable_of_ne_finset_zero (s := {1}) fun m hm => by
          rw [Finset.mem_singleton] at hm; simp [hm]
      rw [tsum_congr hgh, (summable_weightTerm hw2 y).tsum_add hfin, tsum_ite_eq]
      rfl
    have e : (∑' n : ℕ, w' (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ) *
        (riemannKernelReal (y - Real.log ((n + 1 : ℕ) : ℝ)) +
          riemannKernelReal (y + Real.log ((n + 1 : ℕ) : ℝ)))) = ∑' n : ℕ, g (n + 1) := rfl
    rw [e, hshift, htot]
    linarith [hG y]
  have hz := eq_zero_of_riemannKernelTransform_eq_zero_of_sq hsum' hG'
  refine ⟨by simpa [hw'] using hz 0, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := hz m
  have h1 : m + 1 ≠ 1 := by omega
  have hm0 : m ≠ 0 := by omega
  simpa [hw', h1, hn, hm0] using this

/-- **No measure with spectrum in `{0} ∪ ±log ℕ` lives on the critical zeros.**  Let `ν = ν₊ − ν₋`
with `ν±` carried by the critical zeros and `∫ (1 + r²)⁻¹ dν± < ∞`, and suppose that for every real
`C²` compactly supported test `F`,
`∫ |F̂|² dν₊ − ∫ |F̂|² dν₋ = 2c k_F(0) + Σ_{n ≥ 2} w(n) n^{−1/2} (k_F(log n) + k_F(−log n))`, with
`Σ |w(n)| n^{−2} < ∞`.  Then `c = 0` and `w(n) = 0` for every `n ≥ 2`.

The coefficient `c` is `π` times the density of `ν`.  So the critical zeros of `ζ` carry no
measure of nonzero density whose Fourier transform is supported on `{0} ∪ ±log ℕ_{≥2}`. -/
theorem eq_zero_of_signedMeasure_criticalZeros_density {c : ℝ} {w : ℕ → ℝ}
    (hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2) {νp νm : Measure ℝ}
    (hZp : νp {r : ℝ | riemannZeta ((1 / 2 : ℂ) + r * I) ≠ 0} = 0)
    (hZm : νm {r : ℝ | riemannZeta ((1 / 2 : ℂ) + r * I) ≠ 0} = 0)
    (hip : Integrable (fun r : ℝ => 1 / (1 + r ^ 2)) νp)
    (him : Integrable (fun r : ℝ => 1 / (1 + r ^ 2)) νm)
    (hrep : ∀ F : ℝ → ℝ, ContDiff ℝ 2 (fun u => (F u : ℂ)) → HasCompactSupport F →
      densityPairing c w (crossCorr F F) =
        (∫ r, ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2 ∂νp) -
          ∫ r, ‖paperFT (fun u => (F u : ℂ)) r‖ ^ 2 ∂νm) :
    c = 0 ∧ ∀ n, 2 ≤ n → w n = 0 := by
  have hMp : 0 ≤ ∫ r, 1 / (1 + r ^ 2) ∂νp := integral_nonneg fun r => by positivity
  have hMm : 0 ≤ ∫ r, 1 / (1 + r ^ 2) ∂νm := integral_nonneg fun r => by positivity
  refine eq_zero_of_forall_densityPairing_riemannKernel_eq_zero hw2
    (pairing_riemannKernel_eq_zero_of_bound (T := densityPairing c w)
      (fun _ hH hHc L e => densityPairing_perturbedKernel c w L e hH hHc)
      (fun _ hH hHc => exists_abs_densityPairing_truncated_sub_le c hw2 hH hHc)
      (K := (∫ r, 1 / (1 + r ^ 2) ∂νp) + ∫ r, 1 / (1 + r ^ 2) ∂νm) (by positivity)
      fun H hH hHc L e => ?_)
  have hF := contDiff_perturbedKernel L e hH
  have hFc := hasCompactSupport_perturbedKernel L e hHc
  have hfi : Integrable fun u => (perturbedKernel L e H u : ℂ) :=
    hF.continuous.integrable_of_hasCompactSupport (hFc.comp_left Complex.ofReal_zero)
  have hE : ∀ r : ℝ, riemannZeta ((1 / 2 : ℂ) + r * I) = 0 →
      (1 + |r|) * ‖paperFT (fun u => (perturbedKernel L e H u : ℂ)) r‖ ≤
        truncatedRiemannTailEnergy L + |e| * testEnergy H := fun r hr =>
    perturbedKernel_criticalZero_le L e hH hHc hr
  obtain ⟨-, hp⟩ := integral_norm_sq_paperFT_le_of_carried hZp hip hfi hE
  obtain ⟨-, hm⟩ := integral_norm_sq_paperFT_le_of_carried hZm him hfi hE
  have pp : 0 ≤ ∫ r, ‖paperFT (fun u => (perturbedKernel L e H u : ℂ)) r‖ ^ 2 ∂νp :=
    integral_nonneg fun _ => by positivity
  have pm : 0 ≤ ∫ r, ‖paperFT (fun u => (perturbedKernel L e H u : ℂ)) r‖ ^ 2 ∂νm :=
    integral_nonneg fun _ => by positivity
  rw [hrep _ hF hFc, abs_le]
  constructor <;> nlinarith

/-- **RH from a producer carried by the critical zeros.** -/
theorem riemannHypothesis_of_boundaryMeasure_criticalZeros {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam)
    (hZ : boundaryMeasure hW {r : ℝ | riemannZeta ((1 / 2 : ℂ) + r * I) ≠ 0} = 0) :
    RiemannHypothesis := by
  have h := eq_vonMangoldt_of_boundaryMeasure_criticalZeros hW hZ
  refine riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr fun f hf hfc => ?_
  rw [weilFullFunctional_congr (fun n hn => (h n hn).symm)]
  exact hW f hf hfc

end RHTower.WeilSpectral
