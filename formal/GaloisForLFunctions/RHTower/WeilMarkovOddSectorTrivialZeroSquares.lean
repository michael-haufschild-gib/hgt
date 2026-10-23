import GaloisForLFunctions.RHTower.WeilMarkovOnePoleHyperplane
import GaloisForLFunctions.RHTower.WeilArchReLevyPoleForm

/-!
# The odd sector of the archimedean-minus-prime form: trivial-zero squares and the product pairing

Let `f` be a real `C²` test supported in `[ε, ∞)` with `ε > 0`, and let `F(x) = f(x) − f(−x)` be its
odd extension. The archimedean-minus-prime form `M` is a quadratic form, so
`M(F) = 2 M(f) − 2 M(f, f̃)`, and the cross term is the Weil functional of the convolution square
`(f⋆f)(y) = ∫ f(t) f(y − t) dt`, which is supported in `[2ε, ∞)`.

* Its prime part is the product pairing `Π(f) = Σ_n Λ(n) n^{−1/2} (f⋆f)(log n)`, a sum over the
  factorizations `n = e^{x} e^{y}` of the integers.
* Its archimedean part is `−∫_0^∞ ω(x) (f⋆f)(x) dx` with the Lévy density
  `ω(x) = e^{−x/2}/(1 − e^{−2x}) = Σ_{k ≥ 0} e^{−(2k+1/2)x}`, hence equals
  `−Σ_{k ≥ 0} (∫ f(x) e^{−(2k+1/2)x} dx)²`, minus the sum of the squares of the Mellin transform of
  `f` at the trivial zeros `s = −2k` of `ζ`.

The identity
`M(f − f̃) = 2 M(f) + 2 Σ_{k ≥ 0} (∫ f(x) e^{−(2k+1/2)x} dx)² + 2 Σ_n Λ(n) n^{−1/2} (f⋆f)(log n)`
follows (`markovEnergy_oddExtension_eq`). The reflected archimedean kernel of the odd sector is a
manifest sum of squares indexed by the trivial zeros, and the product-prime pairing is nonnegative
for nonnegative `f`.

The archimedean part is handled by polarizing the Lévy form of the archimedean symbol between the
even and the odd extension of `f`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate FourierTransform Convolution
open Zeta23

namespace RHTower

noncomputable section

theorem exp_neg_two_mul_lt_one {x : ℝ} (hx : 0 < x) : Real.exp (-(2 * x)) < 1 := by
  have := Real.exp_lt_exp.mpr (show -(2 * x) < (0 : ℝ) by linarith)
  rwa [Real.exp_zero] at this

/-! ## Definitions -/

/-- The convolution square `(f⋆f)(y) = ∫ f(t) f(y − t) dt`. -/
def convSquare (f : ℝ → ℝ) (y : ℝ) : ℝ := ∫ t, f t * f (y - t)

/-- The Mellin value of `f` at the trivial zero `s = −2k`: `∫ f(x) e^{−(2k+1/2)x} dx`. -/
def trivialZeroMoment (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∫ x, f x * Real.exp (-((2 * (k : ℝ) + 1 / 2) * x))

/-- The product-prime pairing `Σ_n Λ(n) n^{−1/2} (f⋆f)(log n)`. -/
def productPrimePairing (f : ℝ → ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldtAtom n * convSquare f (Real.log n)

/-- The archimedean form of a real test, `(1/2π) ∫ |f̂(r)|² Ω(r) dr`. -/
def archForm (g : ℝ → ℝ) : ℝ :=
  1 / (2 * π) * ∫ r : ℝ, ‖paperFT (fun u => (g u : ℂ)) r‖ ^ 2 * EF.gammaBracket r

/-- The Lévy energy `∫_0^∞ ω(x) ∫ (g(u) − g(u+x))² du dx` of a real test. -/
def levyEnergy (g : ℝ → ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), archLevyDensity x * ∫ u, (g u - g (u + x)) ^ 2

/-- The prime sum of a real test, `Σ_n Λ(n) n^{−1/2} (g⋆g̃(log n) + g⋆g̃(−log n))`. -/
def primeSum (g : ℝ → ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldtAtom n *
    ((∫ t, g t * g (t - Real.log n)) + ∫ t, g t * g (t + Real.log n))

/-! ## Support lemmas -/

section Support

variable {f : ℝ → ℝ} {ε : ℝ}

/-- `f(t) f(y − t) = 0` for every `t` once `y < 2ε`. -/
theorem mul_sub_eq_zero_of_lt (hsupp : ∀ x, x < ε → f x = 0) {y : ℝ} (hy : y < 2 * ε)
    (t : ℝ) : f t * f (y - t) = 0 := by
  by_cases ht : t < ε
  · rw [hsupp t ht, zero_mul]
  · rw [hsupp (y - t) (by linarith), mul_zero]

/-- `f(t) f(−t) = 0` for every `t`. -/
theorem mul_neg_self_eq_zero (hε : 0 < ε) (hsupp : ∀ x, x < ε → f x = 0) (t : ℝ) :
    f t * f (-t) = 0 := by
  have := mul_sub_eq_zero_of_lt hsupp (y := 0) (by linarith) t
  simpa using this

theorem convSquare_eq_zero_of_lt (hsupp : ∀ x, x < ε → f x = 0) {y : ℝ} (hy : y < 2 * ε) :
    convSquare f y = 0 := by
  unfold convSquare
  simp only [mul_sub_eq_zero_of_lt hsupp hy]
  exact integral_zero _ _

theorem convSquare_eq_zero_of_nonpos (hε : 0 < ε) (hsupp : ∀ x, x < ε → f x = 0) {y : ℝ}
    (hy : y ≤ 0) : convSquare f y = 0 :=
  convSquare_eq_zero_of_lt hsupp (by linarith)

end Support

/-! ## The convolution square as a convolution -/

section ConvSquare

variable {f : ℝ → ℝ}

theorem convSquare_eq_convolution (f : ℝ → ℝ) :
    convSquare f = f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f := by
  funext y
  simp only [convSquare, convolution, ContinuousLinearMap.mul_apply']

theorem continuous_convSquare (hf : Continuous f) (hfc : HasCompactSupport f) :
    Continuous (convSquare f) := by
  rw [convSquare_eq_convolution]
  exact hfc.continuous_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (hf.integrable_of_hasCompactSupport hfc).locallyIntegrable hf

theorem hasCompactSupport_convSquare (hfc : HasCompactSupport f) :
    HasCompactSupport (convSquare f) := by
  rw [convSquare_eq_convolution]
  exact hfc.convolution (ContinuousLinearMap.mul ℝ ℝ) hfc

/-- The real cross-correlation of two real tests, as a Weil test. -/
theorem weilTest_ofReal_ofReal_eq (X Y : ℝ → ℝ) (y : ℝ) :
    EF.weilTest (fun u => (X u : ℂ)) (fun u => (Y u : ℂ)) y = ((∫ t, X t * Y (t - y) : ℝ) : ℂ) := by
  unfold EF.weilTest convolution EF.tilde
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.mul_apply', Complex.conj_ofReal]
  rw [show -(y - t) = t - y by ring]
  push_cast
  ring

/-- The convolution square is the Weil test of `f` against its reflection. -/
theorem weilTest_ofReal_reflect_eq (f : ℝ → ℝ) (y : ℝ) :
    EF.weilTest (fun u => (f u : ℂ)) (fun u => (f (-u) : ℂ)) y = ((convSquare f y : ℝ) : ℂ) := by
  rw [weilTest_ofReal_ofReal_eq f (fun u => f (-u)) y]
  unfold convSquare
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [show -(t - y) = y - t by ring]

end ConvSquare

/-! ## The cross-correlation of the odd extension -/

section OddExtension

variable {f : ℝ → ℝ}

theorem integrable_mul_comp_sub (hf : Continuous f) (hfc : HasCompactSupport f) (g : ℝ → ℝ)
    (hg : Continuous g) (y : ℝ) : Integrable fun t => f t * g (t - y) :=
  (hf.mul (hg.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
    hfc.mul_right

theorem integrable_mul_comp_add (hf : Continuous f) (hfc : HasCompactSupport f) (g : ℝ → ℝ)
    (hg : Continuous g) (y : ℝ) : Integrable fun t => f t * g (t + y) :=
  (hf.mul (hg.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
    hfc.mul_right

theorem integrable_neg_mul_comp_sub (hf : Continuous f) (hfc : HasCompactSupport f) (y : ℝ) :
    Integrable fun t => f (-t) * f (t - y) := by
  have hfn : Continuous fun t : ℝ => f (-t) := hf.comp continuous_neg
  have hfnc : HasCompactSupport fun t : ℝ => f (-t) := hfc.comp_homeomorph (Homeomorph.neg ℝ)
  exact (hfn.mul (hf.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
    hfnc.mul_right

theorem integrable_neg_mul_comp_sub' (hf : Continuous f) (hfc : HasCompactSupport f) (y : ℝ) :
    Integrable fun t => f (-t) * f (y - t) := by
  have hfn : Continuous fun t : ℝ => f (-t) := hf.comp continuous_neg
  have hfnc : HasCompactSupport fun t : ℝ => f (-t) := hfc.comp_homeomorph (Homeomorph.neg ℝ)
  exact (hfn.mul (hf.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
    hfnc.mul_right

/-- `∫ f(−t) f(t − y) dt = (f⋆f)(−y)`. -/
theorem integral_neg_mul_sub_eq_convSquare_neg (f : ℝ → ℝ) (y : ℝ) :
    ∫ t, f (-t) * f (t - y) = convSquare f (-y) := by
  unfold convSquare
  rw [← integral_neg_eq_self (fun t => f (-t) * f (t - y)) volume]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [neg_neg]
  rw [show -t - y = -y - t by ring]

/-- `∫ f(−t) f(y − t) dt = ∫ f(t) f(t + y) dt`. -/
theorem integral_neg_mul_sub_eq_add (f : ℝ → ℝ) (y : ℝ) :
    ∫ t, f (-t) * f (y - t) = ∫ t, f t * f (t + y) := by
  rw [← integral_neg_eq_self (fun t => f (-t) * f (y - t)) volume]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [neg_neg]
  rw [show y - -t = t + y by ring]

/-- The cross-correlation of the odd extension `F = f − f̃` in terms of `f`. -/
theorem crossCorr_oddExt (hf : Continuous f) (hfc : HasCompactSupport f) (y : ℝ) :
    (∫ t, (f t - f (-t)) * (f (t - y) - f (-(t - y)))) =
      ((∫ t, f t * f (t - y)) + ∫ t, f t * f (t + y)) - convSquare f y - convSquare f (-y) := by
  have h1 := integrable_mul_comp_sub hf hfc f hf y
  have h2 : Integrable fun t => f t * f (y - t) :=
    (hf.mul (hf.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hfc.mul_right
  have h3 := integrable_neg_mul_comp_sub hf hfc y
  have h4 := integrable_neg_mul_comp_sub' hf hfc y
  have hexp : (fun t => (f t - f (-t)) * (f (t - y) - f (-(t - y)))) =
      fun t => f t * f (t - y) - f t * f (y - t) - f (-t) * f (t - y) + f (-t) * f (y - t) := by
    funext t
    rw [show -(t - y) = y - t by ring]
    ring
  have h12 : Integrable fun t => f t * f (t - y) - f t * f (y - t) := h1.sub h2
  have h123 : Integrable fun t => f t * f (t - y) - f t * f (y - t) - f (-t) * f (t - y) :=
    h12.sub h3
  rw [hexp, integral_add h123 h4, integral_sub h12 h3, integral_sub h1 h2,
    integral_neg_mul_sub_eq_convSquare_neg, integral_neg_mul_sub_eq_add]
  unfold convSquare
  ring

end OddExtension

/-! ## The archimedean form and its Lévy energy -/

section Levy

variable {g : ℝ → ℝ}

theorem integrable_gammaHardy_normSq_fourier_ofReal (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    Integrable fun ξ : ℝ => gammaHardyPhaseRate (2 * π * ξ) * ‖𝓕 (fun u => (g u : ℂ)) ξ‖ ^ 2 := by
  set G : ℝ → ℂ := fun u => (g u : ℂ) with hG
  have hG2 : ContDiff ℝ 2 G := Complex.ofRealCLM.contDiff.comp hg
  have hGc : HasCompactSupport G := hgc.comp_left Complex.ofReal_zero
  have hintC := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket hG2 hGc hG2 hGc
  have hintR : Integrable fun r : ℝ => ‖paperFT G r‖ ^ 2 * EF.gammaBracket r := by
    refine hintC.re.congr (Eventually.of_forall fun r => ?_)
    show (paperFT (EF.weilTest G G) r * (EF.gammaBracket r : ℂ)).re = _
    rw [paperFT_weilTest_self_ofReal hG2.continuous hGc, ← Complex.ofReal_mul, Complex.ofReal_re]
  have h := (hintR.comp_mul_left' (R := -(2 * π)) (by
    have := Real.pi_pos; intro h; linarith)).div_const 2
  refine h.congr (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [fourier_eq_paperFT_neg_two_pi_mul, WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate,
    show -(2 * π) * ξ = -(2 * π * ξ) by ring, gammaHardyPhaseRate_neg]
  ring

theorem integrable_normSq_paperFT_mul_gammaBracket (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    Integrable fun r : ℝ => ‖paperFT (fun u => (g u : ℂ)) r‖ ^ 2 * EF.gammaBracket r := by
  set G : ℝ → ℂ := fun u => (g u : ℂ) with hG
  have hG2 : ContDiff ℝ 2 G := Complex.ofRealCLM.contDiff.comp hg
  have hGc : HasCompactSupport G := hgc.comp_left Complex.ofReal_zero
  have hintC := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket hG2 hGc hG2 hGc
  refine hintC.re.congr (Eventually.of_forall fun r => ?_)
  show (paperFT (EF.weilTest G G) r * (EF.gammaBracket r : ℂ)).re = _
  rw [paperFT_weilTest_self_ofReal hG2.continuous hGc, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The Lévy integrand of a continuous test is measurable on `(0, ∞)`. -/
theorem aestronglyMeasurable_levyIntegrand (hg : Continuous g) :
    AEStronglyMeasurable (fun x : ℝ => archLevyDensity x * ∫ u, (g u - g (u + x)) ^ 2)
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hc : Continuous fun p : ℝ × ℝ => (g p.2 - g (p.2 + p.1)) ^ 2 := by fun_prop
  have hm : StronglyMeasurable fun x : ℝ => ∫ u, (g u - g (u + x)) ^ 2 :=
    hc.stronglyMeasurable.integral_prod_right'
  exact (measurable_archLevyDensity.aestronglyMeasurable.mul hm.aestronglyMeasurable)

theorem levyIntegrand_nonneg (g : ℝ → ℝ) :
    0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun x : ℝ => archLevyDensity x * ∫ u, (g u - g (u + x)) ^ 2 := by
  refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
  exact mul_nonneg (archLevyDensity_pos hx).le (integral_nonneg fun u => sq_nonneg _)

/-- The Lévy lintegral of the corpus, for a real test, in real form. -/
theorem lintegral_levy_eq (g : ℝ → ℝ) :
    (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity x *
        ∫ u : ℝ, ‖(g u : ℂ) - (g (u + x) : ℂ)‖ ^ 2)) =
      ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity x * ∫ u : ℝ, (g u - g (u + x)) ^ 2) := by
  refine lintegral_congr fun x => ?_
  congr 3
  funext u
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The Lévy integrand is integrable on `(0, ∞)`. -/
theorem integrableOn_levyIntegrand (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    IntegrableOn (fun x : ℝ => archLevyDensity x * ∫ u, (g u - g (u + x)) ^ 2) (Ioi 0) := by
  set G : ℝ → ℂ := fun u => (g u : ℂ) with hG
  have hGc : Continuous G := Complex.continuous_ofReal.comp hg.continuous
  have hGcs : HasCompactSupport G := hgc.comp_left Complex.ofReal_zero
  have hG1 : Integrable G := hGc.integrable_of_hasCompactSupport hGcs
  have hGL2 : MemLp G 2 := hGc.memLp_of_hasCompactSupport hGcs
  have hne := lintegral_archLevyDirichlet_ne_top hG1 hGL2
    (integrable_gammaHardy_normSq_fourier_ofReal hg hgc)
  rw [lintegral_levy_eq] at hne
  refine ⟨aestronglyMeasurable_levyIntegrand hg.continuous, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (levyIntegrand_nonneg g)]
  exact lt_top_iff_ne_top.2 hne

/-- **The archimedean form in Lévy form.** `A(g) = 2θ′(0)‖g‖² + ∫_0^∞ ω(x)‖g − g(·+x)‖² dx`. -/
theorem archForm_eq_levyEnergy (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    archForm g = 2 * gammaHardyPhaseRate 0 * (∫ u, g u ^ 2) + levyEnergy g := by
  have hGc : Continuous fun u => (g u : ℂ) := Complex.continuous_ofReal.comp hg.continuous
  have hGcs : HasCompactSupport fun u => (g u : ℂ) := hgc.comp_left Complex.ofReal_zero
  have hG1 : Integrable fun u => (g u : ℂ) := hGc.integrable_of_hasCompactSupport hGcs
  have hGL2 : MemLp (fun u => (g u : ℂ)) 2 := hGc.memLp_of_hasCompactSupport hGcs
  have hsplit := integral_archSymbol_mul_normSq_fourier_eq hG1 hGL2
    (integrable_gammaHardy_normSq_fourier_ofReal hg hgc)
  have hnorm : (∫ u : ℝ, ‖(g u : ℂ)‖ ^ 2) = ∫ u, g u ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp [Complex.norm_real, sq_abs]
  unfold archForm levyEnergy
  rw [WeilLevyPole.integral_paperFT_sq_mul_gammaBracket, hsplit, lintegral_levy_eq, hnorm,
    ← integral_eq_lintegral_of_nonneg_ae (levyIntegrand_nonneg g)
      (aestronglyMeasurable_levyIntegrand hg.continuous)]

end Levy

/-! ## Polarization between the even and the odd extension -/

section Polarization

variable {f : ℝ → ℝ} {ε : ℝ}

theorem contDiff_evenExt (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 fun x => f x + f (-x) :=
  hf.add (hf.comp contDiff_neg)

theorem contDiff_oddExt (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 fun x => f x - f (-x) :=
  hf.sub (hf.comp contDiff_neg)

theorem hasCompactSupport_reflect (hfc : HasCompactSupport f) :
    HasCompactSupport fun x => f (-x) :=
  hfc.comp_homeomorph (Homeomorph.neg ℝ)

theorem hasCompactSupport_evenExt (hfc : HasCompactSupport f) :
    HasCompactSupport fun x => f x + f (-x) :=
  hfc.add (hasCompactSupport_reflect hfc)

theorem hasCompactSupport_oddExt (hfc : HasCompactSupport f) :
    HasCompactSupport fun x => f x - f (-x) :=
  hfc.sub (hasCompactSupport_reflect hfc)

/-- The pointwise polarization of the Lévy integrand for `x > 0`. -/
theorem levy_polarization_pointwise (hε : 0 < ε) (hsupp : ∀ x, x < ε → f x = 0) {x : ℝ}
    (hx : 0 < x) (u : ℝ) :
    ((f u + f (-u)) - (f (u + x) + f (-(u + x)))) ^ 2 -
        ((f u - f (-u)) - (f (u + x) - f (-(u + x)))) ^ 2 =
      -4 * (f (u + x) * f (-u)) := by
  have h1 := mul_neg_self_eq_zero hε hsupp u
  have h2 := mul_neg_self_eq_zero hε hsupp (u + x)
  have h3 : f u * f (-(u + x)) = 0 := by
    have := mul_sub_eq_zero_of_lt hsupp (y := -x) (by linarith) u
    rwa [show -x - u = -(u + x) by ring] at this
  linear_combination (4 : ℝ) * h1 - 4 * h3 + 4 * h2

/-- `∫ f(u + x) f(−u) du = (f⋆f)(x)`. -/
theorem integral_add_mul_neg_eq_convSquare (f : ℝ → ℝ) (x : ℝ) :
    ∫ u, f (u + x) * f (-u) = convSquare f x := by
  unfold convSquare
  rw [← integral_neg_eq_self (fun u => f (u + x) * f (-u)) volume]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [neg_neg]
  rw [show -u + x = x - u by ring, mul_comm]

theorem levyEnergy_evenExt_sub_oddExt (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hε : 0 < ε) (hsupp : ∀ x, x < ε → f x = 0) :
    levyEnergy (fun x => f x + f (-x)) - levyEnergy (fun x => f x - f (-x)) =
      -4 * ∫ x in Ioi (0 : ℝ), archLevyDensity x * convSquare f x := by
  unfold levyEnergy
  rw [← integral_sub (integrableOn_levyIntegrand (contDiff_evenExt hf) (hasCompactSupport_evenExt hfc))
    (integrableOn_levyIntegrand (contDiff_oddExt hf) (hasCompactSupport_oddExt hfc)),
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hfe : Continuous fun x => f x + f (-x) := (contDiff_evenExt hf).continuous
  have hfo : Continuous fun x => f x - f (-x) := (contDiff_oddExt hf).continuous
  have hfec := hasCompactSupport_evenExt hfc
  have hfoc := hasCompactSupport_oddExt hfc
  have ie : Integrable fun u => ((f u + f (-u)) - (f (u + x) + f (-(u + x)))) ^ 2 := by
    have : Continuous fun u => ((f u + f (-u)) - (f (u + x) + f (-(u + x)))) ^ 2 := by fun_prop
    have hD : HasCompactSupport fun u => (f u + f (-u)) - (f (u + x) + f (-(u + x))) :=
      hfec.sub (hfec.comp_homeomorph (Homeomorph.addRight x))
    exact this.integrable_of_hasCompactSupport (hD.comp_left (g := fun y : ℝ => y ^ 2) (by simp))
  have io : Integrable fun u => ((f u - f (-u)) - (f (u + x) - f (-(u + x)))) ^ 2 := by
    have : Continuous fun u => ((f u - f (-u)) - (f (u + x) - f (-(u + x)))) ^ 2 := by fun_prop
    have hD : HasCompactSupport fun u => (f u - f (-u)) - (f (u + x) - f (-(u + x))) :=
      hfoc.sub (hfoc.comp_homeomorph (Homeomorph.addRight x))
    exact this.integrable_of_hasCompactSupport (hD.comp_left (g := fun y : ℝ => y ^ 2) (by simp))
  have hpt : ∀ u : ℝ, ((f u + f (-u)) - (f (u + x) + f (-(u + x)))) ^ 2 -
      ((f u - f (-u)) - (f (u + x) - f (-(u + x)))) ^ 2 = -4 * (f (u + x) * f (-u)) :=
    levy_polarization_pointwise hε hsupp hx
  rw [← mul_sub, ← integral_sub ie io]
  simp_rw [hpt]
  rw [integral_const_mul, integral_add_mul_neg_eq_convSquare]
  ring

/-- The even and the odd extension have the same `L²` norm. -/
theorem integral_sq_evenExt_eq_oddExt (hε : 0 < ε) (hsupp : ∀ x, x < ε → f x = 0) :
    (∫ u, (f u + f (-u)) ^ 2) = ∫ u, (f u - f (-u)) ^ 2 := by
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  have := mul_neg_self_eq_zero hε hsupp u
  nlinarith [this]

/-- Fourier transforms of the even and odd extensions: `p ± conj p`. -/
theorem paperFT_evenExt (hf : Continuous f) (hfc : HasCompactSupport f) (r : ℝ) :
    paperFT (fun u => ((f u + f (-u) : ℝ) : ℂ)) r =
      paperFT (fun u => (f u : ℂ)) r + conj (paperFT (fun u => (f u : ℂ)) r) := by
  set U : ℝ → ℂ := fun u => (f u : ℂ) with hU
  have hUc : Continuous U := Complex.continuous_ofReal.comp hf
  have hUcs : HasCompactSupport U := hfc.comp_left Complex.ofReal_zero
  have htilde : (fun u => ((f u + f (-u) : ℝ) : ℂ)) = fun u => 1 * U u + 1 * EF.tilde U u := by
    funext u
    simp only [hU, EF.tilde, Complex.conj_ofReal]
    push_cast; ring
  have htc : Continuous (EF.tilde U) := by
    unfold EF.tilde
    exact Complex.continuous_conj.comp (hUc.comp continuous_neg)
  have htcs : HasCompactSupport (EF.tilde U) := by
    unfold EF.tilde
    exact (hUcs.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (map_zero _)
  rw [htilde, paperFT_smul_add_smul 1 1 _ (integrable_mul_cexp_of_compact hUc hUcs _)
    (integrable_mul_cexp_of_compact htc htcs _), EF.paperFT_tilde, Complex.conj_ofReal]
  ring

theorem paperFT_oddExt (hf : Continuous f) (hfc : HasCompactSupport f) (r : ℝ) :
    paperFT (fun u => ((f u - f (-u) : ℝ) : ℂ)) r =
      paperFT (fun u => (f u : ℂ)) r - conj (paperFT (fun u => (f u : ℂ)) r) := by
  set U : ℝ → ℂ := fun u => (f u : ℂ) with hU
  have hUc : Continuous U := Complex.continuous_ofReal.comp hf
  have hUcs : HasCompactSupport U := hfc.comp_left Complex.ofReal_zero
  have htilde : (fun u => ((f u - f (-u) : ℝ) : ℂ)) = fun u => 1 * U u + (-1) * EF.tilde U u := by
    funext u
    simp only [hU, EF.tilde, Complex.conj_ofReal]
    push_cast; ring
  have htc : Continuous (EF.tilde U) := by
    unfold EF.tilde
    exact Complex.continuous_conj.comp (hUc.comp continuous_neg)
  have htcs : HasCompactSupport (EF.tilde U) := by
    unfold EF.tilde
    exact (hUcs.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (map_zero _)
  rw [htilde, paperFT_smul_add_smul 1 (-1) _ (integrable_mul_cexp_of_compact hUc hUcs _)
    (integrable_mul_cexp_of_compact htc htcs _), EF.paperFT_tilde, Complex.conj_ofReal]
  ring

/-- `|p − p̄|² = 2|p|² − (|p + p̄|² − |p − p̄|²)/2`. -/
theorem normSq_sub_conj_eq (p : ℂ) :
    ‖p - conj p‖ ^ 2 = 2 * ‖p‖ ^ 2 - (‖p + conj p‖ ^ 2 - ‖p - conj p‖ ^ 2) / 2 := by
  have h1 : p - conj p = ((2 * p.im : ℝ) : ℂ) * I :=
    Complex.ext (by simp) (by simp; ring)
  have h2 : p + conj p = ((2 * p.re : ℝ) : ℂ) :=
    Complex.ext (by simp; ring) (by simp)
  rw [h1, h2, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, Complex.sq_norm, Complex.normSq_apply, sq_abs, sq_abs]
  ring

/-- **The archimedean form of the odd extension.**
`A(f − f̃) = 2A(f) + 2∫_0^∞ ω(x)(f⋆f)(x) dx`. -/
theorem archForm_oddExt_eq (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hε : 0 < ε)
    (hsupp : ∀ x, x < ε → f x = 0) :
    archForm (fun x => f x - f (-x)) =
      2 * archForm f + 2 * ∫ x in Ioi (0 : ℝ), archLevyDensity x * convSquare f x := by
  have hAe := archForm_eq_levyEnergy (contDiff_evenExt hf) (hasCompactSupport_evenExt hfc)
  have hAo := archForm_eq_levyEnergy (contDiff_oddExt hf) (hasCompactSupport_oddExt hfc)
  have hL := levyEnergy_evenExt_sub_oddExt hf hfc hε hsupp
  have hN := integral_sq_evenExt_eq_oddExt hε hsupp
  -- the pointwise identity integrated against the symbol
  have i1 := integrable_normSq_paperFT_mul_gammaBracket hf hfc
  have i2 := integrable_normSq_paperFT_mul_gammaBracket (contDiff_evenExt hf)
    (hasCompactSupport_evenExt hfc)
  have i3 := integrable_normSq_paperFT_mul_gammaBracket (contDiff_oddExt hf)
    (hasCompactSupport_oddExt hfc)
  have key : (∫ r : ℝ, ‖paperFT (fun u => ((f u - f (-u) : ℝ) : ℂ)) r‖ ^ 2 * EF.gammaBracket r) =
      2 * (∫ r : ℝ, ‖paperFT (fun u => (f u : ℂ)) r‖ ^ 2 * EF.gammaBracket r) -
        ((∫ r : ℝ, ‖paperFT (fun u => ((f u + f (-u) : ℝ) : ℂ)) r‖ ^ 2 * EF.gammaBracket r) -
          ∫ r : ℝ, ‖paperFT (fun u => ((f u - f (-u) : ℝ) : ℂ)) r‖ ^ 2 * EF.gammaBracket r) / 2 := by
    have j1 : Integrable fun r : ℝ =>
        2 * (‖paperFT (fun u => (f u : ℂ)) r‖ ^ 2 * EF.gammaBracket r) := i1.const_mul 2
    have j2 : Integrable fun r : ℝ =>
        (‖paperFT (fun u => ((f u + f (-u) : ℝ) : ℂ)) r‖ ^ 2 * EF.gammaBracket r -
          ‖paperFT (fun u => ((f u - f (-u) : ℝ) : ℂ)) r‖ ^ 2 * EF.gammaBracket r) / 2 :=
      (i2.sub i3).div_const 2
    rw [← integral_sub i2 i3, ← integral_const_mul, ← integral_div, ← integral_sub j1 j2]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only
    rw [paperFT_evenExt hf.continuous hfc, paperFT_oddExt hf.continuous hfc]
    have h := normSq_sub_conj_eq (paperFT (fun u => (f u : ℂ)) r)
    linear_combination (EF.gammaBracket r) * h
  have hpt : archForm (fun x => f x - f (-x)) = 2 * archForm f -
      (archForm (fun x => f x + f (-x)) - archForm (fun x => f x - f (-x))) / 2 := by
    simp only [archForm]
    linear_combination (1 / (2 * π)) * key
  have hdiff : archForm (fun x => f x + f (-x)) - archForm (fun x => f x - f (-x)) =
      -4 * ∫ x in Ioi (0 : ℝ), archLevyDensity x * convSquare f x := by
    rw [hAe, hAo, hN, ← hL]; ring
  rw [hpt, hdiff]; ring

end Polarization

/-! ## The geometric series over the trivial zeros -/

section Geometric

variable {f : ℝ → ℝ} {ε : ℝ}

/-- The Lévy density as a geometric series, for `x > 0`. -/
theorem archLevyDensity_eq_tsum {x : ℝ} (hx : 0 < x) :
    archLevyDensity x = ∑' k : ℕ, Real.exp (-((2 * (k : ℝ) + 1 / 2) * x)) := by
  have hr : Real.exp (-(2 * x)) < 1 := exp_neg_two_mul_lt_one hx
  have hterm : ∀ k : ℕ, Real.exp (-((2 * (k : ℝ) + 1 / 2) * x)) =
      Real.exp (-x / 2) * Real.exp (-(2 * x)) ^ k := by
    intro k
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; ring
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le hr]
  unfold archLevyDensity
  rw [div_eq_mul_inv, show (-2 : ℝ) * x = -(2 * x) by ring]

theorem integrable_exp_neg_mul_convSquare (hf : Continuous f) (hfc : HasCompactSupport f) (c : ℝ) :
    Integrable fun x => Real.exp (-(c * x)) * convSquare f x :=
  ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
    (continuous_convSquare hf hfc)).integrable_of_hasCompactSupport
    (hasCompactSupport_convSquare hfc).mul_left

/-- The Lévy density times the convolution square is integrable (the support stays away from `0`). -/
theorem integrable_archLevyDensity_mul_convSquare (hf : Continuous f) (hfc : HasCompactSupport f)
    (hε : 0 < ε) (hsupp : ∀ x, x < ε → f x = 0) :
    Integrable fun x => archLevyDensity x * convSquare f x := by
  have hcs := continuous_convSquare hf hfc
  have hcsc := hasCompactSupport_convSquare hfc
  -- continuity: the convolution square vanishes below `2ε`, where the density is singular
  have hcont : Continuous fun x => archLevyDensity x * convSquare f x := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x < 2 * ε
    · have hev : (fun y => archLevyDensity y * convSquare f y) =ᶠ[nhds x] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds hx] with y hy
        rw [convSquare_eq_zero_of_lt hsupp hy, mul_zero]
      exact (continuousAt_const).congr hev.symm
    · push Not at hx
      have hx0 : 0 < x := by linarith
      have hd : ContinuousAt archLevyDensity x := by
        have hne : (1 - Real.exp (-2 * x)) ≠ 0 := by
          rw [show (-2 : ℝ) * x = -(2 * x) by ring]
          have := exp_neg_two_mul_lt_one hx0
          linarith
        show ContinuousAt (fun y : ℝ => Real.exp (-y / 2) / (1 - Real.exp (-2 * y))) x
        exact ((Real.continuous_exp.comp (continuous_id.neg.div_const 2)).continuousAt.div
          (continuous_const.sub (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousAt hne)
      exact hd.mul hcs.continuousAt
  exact hcont.integrable_of_hasCompactSupport hcsc.mul_left

/-- `∫ e^{−cx} (f⋆f)(x) dx = (∫ f(u) e^{−cu} du)²`. -/
theorem integral_exp_neg_mul_convSquare (hf : Continuous f) (hfc : HasCompactSupport f) (c : ℝ) :
    ∫ x, Real.exp (-(c * x)) * convSquare f x = (∫ u, f u * Real.exp (-(c * u))) ^ 2 := by
  unfold convSquare
  -- the integrand on the product
  have hK : IsCompact ((fun p : ℝ × ℝ => (p.1 + p.2, p.1)) '' (tsupport f ×ˢ tsupport f)) :=
    (hfc.prod hfc).image (by fun_prop)
  have hcont : Continuous fun p : ℝ × ℝ => Real.exp (-(c * p.1)) * (f p.2 * f (p.1 - p.2)) := by
    fun_prop
  have hsupp2 : HasCompactSupport fun p : ℝ × ℝ => Real.exp (-(c * p.1)) * (f p.2 * f (p.1 - p.2)) := by
    refine HasCompactSupport.intro hK fun p hp => ?_
    by_contra hne
    apply hp
    have h1 : f p.2 ≠ 0 := fun h => hne (by simp [h])
    have h2 : f (p.1 - p.2) ≠ 0 := fun h => hne (by simp [h])
    refine ⟨(p.2, p.1 - p.2), ⟨subset_tsupport f h1, subset_tsupport f h2⟩, ?_⟩
    simp
  have hint : Integrable (fun p : ℝ × ℝ => Real.exp (-(c * p.1)) * (f p.2 * f (p.1 - p.2)))
      (volume.prod volume) := by
    have : Integrable (fun p : ℝ × ℝ => Real.exp (-(c * p.1)) * (f p.2 * f (p.1 - p.2))) volume :=
      hcont.integrable_of_hasCompactSupport hsupp2
    rwa [Measure.volume_eq_prod] at this
  calc ∫ x, Real.exp (-(c * x)) * ∫ t, f t * f (x - t)
      = ∫ x, ∫ t, Real.exp (-(c * x)) * (f t * f (x - t)) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only
        rw [← integral_const_mul]
    _ = ∫ t, ∫ x, Real.exp (-(c * x)) * (f t * f (x - t)) := integral_integral_swap hint
    _ = ∫ t, f t * Real.exp (-(c * t)) * ∫ u, f u * Real.exp (-(c * u)) := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        simp only
        have hsub : ∫ x, Real.exp (-(c * x)) * (f t * f (x - t)) =
            ∫ u, Real.exp (-(c * (u + t))) * (f t * f u) := by
          rw [← integral_add_right_eq_self (fun x => Real.exp (-(c * x)) * (f t * f (x - t))) t]
          refine integral_congr_ae (Eventually.of_forall fun u => ?_)
          simp only
          rw [show u + t - t = u by ring]
        rw [hsub, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only
        rw [show -(c * (u + t)) = -(c * u) + -(c * t) by ring, Real.exp_add]
        ring
    _ = (∫ u, f u * Real.exp (-(c * u))) ^ 2 := by
        rw [integral_mul_const, sq]

/-- **The Lévy–convolution pairing is the sum of the trivial-zero squares.**
`∫_0^∞ ω(x)(f⋆f)(x) dx = Σ_{k ≥ 0} (∫ f(x) e^{−(2k+1/2)x} dx)²`. -/
theorem integral_archLevyDensity_mul_convSquare_eq_tsum (hf : Continuous f)
    (hfc : HasCompactSupport f) (hε : 0 < ε) (hsupp : ∀ x, x < ε → f x = 0) :
    ∫ x in Ioi (0 : ℝ), archLevyDensity x * convSquare f x =
      ∑' k : ℕ, (trivialZeroMoment f k) ^ 2 := by
  -- rewrite the integrand as a series on `(0, ∞)`
  have hpt : ∀ x ∈ Ioi (0 : ℝ), archLevyDensity x * convSquare f x =
      ∑' k : ℕ, Real.exp (-((2 * (k : ℝ) + 1 / 2) * x)) * convSquare f x := by
    intro x hx
    rw [archLevyDensity_eq_tsum hx, tsum_mul_right]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  -- each term vanishes off `(0, ∞)`, so the set integral is the full integral
  have hterm0 : ∀ k : ℕ, ∀ x ∉ Ioi (0 : ℝ),
      Real.exp (-((2 * (k : ℝ) + 1 / 2) * x)) * convSquare f x = 0 := by
    intro k x hx
    rw [convSquare_eq_zero_of_nonpos hε hsupp (by simpa using hx), mul_zero]
  have hsum0 : ∀ x ∉ Ioi (0 : ℝ),
      (∑' k : ℕ, Real.exp (-((2 * (k : ℝ) + 1 / 2) * x)) * convSquare f x) = 0 := by
    intro x hx
    simp_rw [hterm0 _ x hx]
    exact tsum_zero
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsum0]
  -- swap the series and the integral
  have hmeas : ∀ k : ℕ, AEStronglyMeasurable
      (fun x => Real.exp (-((2 * (k : ℝ) + 1 / 2) * x)) * convSquare f x) volume := fun k =>
    (integrable_exp_neg_mul_convSquare hf hfc _).aestronglyMeasurable
  have hsumm : ∀ x : ℝ, 0 < x → Summable fun k : ℕ => Real.exp (-((2 * (k : ℝ) + 1 / 2) * x)) := by
    intro x hx
    have hr : Real.exp (-(2 * x)) < 1 := exp_neg_two_mul_lt_one hx
    have hterm : ∀ k : ℕ, Real.exp (-((2 * (k : ℝ) + 1 / 2) * x)) =
        Real.exp (-x / 2) * Real.exp (-(2 * x)) ^ k := by
      intro k
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1; ring
    simp_rw [hterm]
    exact (summable_geometric_of_lt_one (Real.exp_pos _).le hr).mul_left _
  have hbound : ∀ x : ℝ, (∑' k : ℕ, ‖Real.exp (-((2 * (k : ℝ) + 1 / 2) * x)) * convSquare f x‖ₑ) =
      ‖archLevyDensity x * convSquare f x‖ₑ := by
    intro x
    by_cases hx : 0 < x
    · have hs := (hsumm x hx).mul_right |convSquare f x|
      have hpos : ∀ k : ℕ, 0 ≤ Real.exp (-((2 * (k : ℝ) + 1 / 2) * x)) * |convSquare f x| :=
        fun k => mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
      have h1 : ∀ k : ℕ, ‖Real.exp (-((2 * (k : ℝ) + 1 / 2) * x)) * convSquare f x‖ₑ =
          ENNReal.ofReal (Real.exp (-((2 * (k : ℝ) + 1 / 2) * x)) * |convSquare f x|) := by
        intro k
        rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      simp_rw [h1]
      rw [← ENNReal.ofReal_tsum_of_nonneg hpos hs, tsum_mul_right, ← archLevyDensity_eq_tsum hx,
        Real.enorm_eq_ofReal_abs, abs_mul, abs_of_pos (archLevyDensity_pos hx)]
    · push Not at hx
      have h0 : convSquare f x = 0 := convSquare_eq_zero_of_nonpos hε hsupp hx
      simp [h0]
  have hfin : (∑' k : ℕ, ∫⁻ x, ‖Real.exp (-((2 * (k : ℝ) + 1 / 2) * x)) * convSquare f x‖ₑ) ≠ ⊤ := by
    rw [← lintegral_tsum fun k => (hmeas k).enorm]
    simp_rw [hbound]
    exact (integrable_archLevyDensity_mul_convSquare hf hfc hε hsupp).hasFiniteIntegral.ne
  rw [integral_tsum hmeas hfin]
  refine tsum_congr fun k => ?_
  rw [integral_exp_neg_mul_convSquare hf hfc]
  rfl

end Geometric

/-! ## Assembly -/

section Assembly

variable {f g : ℝ → ℝ} {ε : ℝ}

/-- The archimedean-minus-prime form of a real test is its archimedean form minus its prime sum. -/
theorem markovEnergy_ofReal_eq_archForm_sub_primeSum (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    markovEnergy (fun x => (g x : ℂ)) = archForm g - primeSum g := by
  have hGc : Continuous fun x => (g x : ℂ) := Complex.continuous_ofReal.comp hg.continuous
  have hGcs : HasCompactSupport fun x => (g x : ℂ) := hgc.comp_left Complex.ofReal_zero
  rw [markovEnergy_eq_arch_sub_primes_atom]
  have harch : (∫ r : ℝ, paperFT (EF.weilTest (fun x => (g x : ℂ)) (fun x => (g x : ℂ))) r *
      (EF.gammaBracket r : ℂ)) =
      ((∫ r : ℝ, ‖paperFT (fun x => (g x : ℂ)) r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only
    rw [paperFT_weilTest_self_ofReal hGc hGcs]
    push_cast
    ring
  have hprime : (∑' n : ℕ, ((vonMangoldtAtom n : ℝ) : ℂ) *
      (EF.weilTest (fun x => (g x : ℂ)) (fun x => (g x : ℂ)) (Real.log n) +
        EF.weilTest (fun x => (g x : ℂ)) (fun x => (g x : ℂ)) (-Real.log n))) =
      ((∑' n : ℕ, vonMangoldtAtom n *
        ((∫ t, g t * g (t - Real.log n)) + ∫ t, g t * g (t + Real.log n)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [weilTest_ofReal_eq, weilTest_ofReal_eq]
    push_cast
    simp only [sub_neg_eq_add]
  rw [harch, hprime, show ((1 / (2 * π) : ℂ)) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.ofReal_re]
  rfl

/-- Summability of the ratio prime sum of a real test. -/
theorem summable_primeSum_terms (hgc : HasCompactSupport g) :
    Summable fun n : ℕ => vonMangoldtAtom n *
      ((∫ t, g t * g (t - Real.log n)) + ∫ t, g t * g (t + Real.log n)) := by
  have hGcs : HasCompactSupport fun x => (g x : ℂ) := hgc.comp_left Complex.ofReal_zero
  have h := summable_primeAtoms vonMangoldtAtom (EF.weilTest_hasCompactSupport hGcs hGcs)
  have h' : Summable fun n : ℕ => ((vonMangoldtAtom n *
      ((∫ t, g t * g (t - Real.log n)) + ∫ t, g t * g (t + Real.log n)) : ℝ) : ℂ) := by
    refine h.congr fun n => ?_
    rw [weilTest_ofReal_eq, weilTest_ofReal_eq]
    push_cast
    simp only [sub_neg_eq_add]
  exact Complex.summable_ofReal.mp h'

/-- Summability of the product-prime pairing of a half-line test. -/
theorem summable_productPrimePairing_terms (hfc : HasCompactSupport f)
    (hε : 0 < ε) (hsupp : ∀ x, x < ε → f x = 0) :
    Summable fun n : ℕ => vonMangoldtAtom n * convSquare f (Real.log n) := by
  have hUcs : HasCompactSupport fun x => (f x : ℂ) := hfc.comp_left Complex.ofReal_zero
  have hRcs : HasCompactSupport fun x => (f (-x) : ℂ) :=
    (hasCompactSupport_reflect hfc).comp_left Complex.ofReal_zero
  have h := summable_primeAtoms vonMangoldtAtom (EF.weilTest_hasCompactSupport hUcs hRcs)
  have h' : Summable fun n : ℕ => ((vonMangoldtAtom n * convSquare f (Real.log n) : ℝ) : ℂ) := by
    refine h.congr fun n => ?_
    rw [weilTest_ofReal_reflect_eq, weilTest_ofReal_reflect_eq,
      convSquare_eq_zero_of_nonpos hε hsupp (neg_nonpos.mpr (Real.log_natCast_nonneg n))]
    push_cast
    ring
  exact Complex.summable_ofReal.mp h'

/-- **The prime sum of the odd extension.** `P(f − f̃) = 2P(f) − 2Π(f)`. -/
theorem primeSum_oddExt (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hε : 0 < ε)
    (hsupp : ∀ x, x < ε → f x = 0) :
    primeSum (fun x => f x - f (-x)) = 2 * primeSum f - 2 * productPrimePairing f := by
  unfold primeSum productPrimePairing
  have hs1 := summable_primeSum_terms hfc
  have hs2 := summable_productPrimePairing_terms hfc hε hsupp
  rw [← tsum_mul_left, ← tsum_mul_left, ← (hs1.mul_left 2).tsum_sub (hs2.mul_left 2)]
  refine tsum_congr fun n => ?_
  have hA := crossCorr_oddExt hf.continuous hfc (Real.log n)
  have hB := crossCorr_oddExt hf.continuous hfc (-Real.log n)
  have h0 : convSquare f (-Real.log n) = 0 :=
    convSquare_eq_zero_of_nonpos hε hsupp (neg_nonpos.mpr (Real.log_natCast_nonneg n))
  simp only [neg_neg, sub_neg_eq_add, ← sub_eq_add_neg] at hB
  simp only
  rw [hA, hB, h0]
  ring

/-- **The odd sector of the archimedean-minus-prime form.** For a real `C²` test `f` supported in
`[ε, ∞)` with `ε > 0`,
`M(f − f̃) = 2 M(f) + 2 Σ_{k ≥ 0} (∫ f(x) e^{−(2k+1/2)x} dx)² + 2 Σ_n Λ(n) n^{−1/2} (f⋆f)(log n)`:
the reflected archimedean kernel is the sum of the squares of the Mellin transform of `f` at the
trivial zeros of `ζ`, and the reflected prime atoms form the product pairing. -/
theorem markovEnergy_oddExtension_eq (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hε : 0 < ε) (hsupp : ∀ x, x < ε → f x = 0) :
    markovEnergy (fun x => ((f x - f (-x) : ℝ) : ℂ)) =
      2 * markovEnergy (fun x => (f x : ℂ)) + 2 * (∑' k : ℕ, (trivialZeroMoment f k) ^ 2) +
        2 * productPrimePairing f := by
  have h1 := markovEnergy_ofReal_eq_archForm_sub_primeSum (contDiff_oddExt hf)
    (hasCompactSupport_oddExt hfc)
  have h2 := markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc
  rw [h1, h2, archForm_oddExt_eq hf hfc hε hsupp, primeSum_oddExt hf hfc hε hsupp,
    integral_archLevyDensity_mul_convSquare_eq_tsum hf.continuous hfc hε hsupp]
  ring

/-- For a nonnegative test the product pairing is nonnegative. -/
theorem productPrimePairing_nonneg (hpos : ∀ x, 0 ≤ f x) : 0 ≤ productPrimePairing f := by
  unfold productPrimePairing
  refine tsum_nonneg fun n => mul_nonneg ?_ (integral_nonneg fun t => mul_nonneg (hpos t) (hpos _))
  unfold vonMangoldtAtom
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · exact le_rfl

/-- **Under RH, `M(f) + Σ_k f̃(−2k)² + Π(f) ≥ 0` for every half-line test.** This is the odd
positivity criterion read through the odd-sector decomposition. -/
theorem halfLine_markovEnergy_add_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hε : 0 < ε)
    (hsupp : ∀ x, x < ε → f x = 0) :
    0 ≤ markovEnergy (fun x => (f x : ℂ)) + (∑' k : ℕ, (trivialZeroMoment f k) ^ 2) +
      productPrimePairing f := by
  have hodd := (riemannHypothesis_iff_forall_odd_markovEnergy_nonneg.mp hRH)
    (fun x => f x - f (-x)) (contDiff_oddExt hf) (hasCompactSupport_oddExt hfc)
    (fun x => by show f (-x) - f (- -x) = -(f x - f (-x)); rw [neg_neg]; ring)
  have := markovEnergy_oddExtension_eq hf hfc hε hsupp
  linarith

/-! ### The even extension -/

/-- The cross-correlation of the even extension `f + f̃` in terms of `f`. -/
theorem crossCorr_evenExt (hf : Continuous f) (hfc : HasCompactSupport f) (y : ℝ) :
    (∫ t, (f t + f (-t)) * (f (t - y) + f (-(t - y)))) =
      ((∫ t, f t * f (t - y)) + ∫ t, f t * f (t + y)) + convSquare f y + convSquare f (-y) := by
  have h1 := integrable_mul_comp_sub hf hfc f hf y
  have h2 : Integrable fun t => f t * f (y - t) :=
    (hf.mul (hf.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hfc.mul_right
  have h3 := integrable_neg_mul_comp_sub hf hfc y
  have h4 := integrable_neg_mul_comp_sub' hf hfc y
  have hexp : (fun t => (f t + f (-t)) * (f (t - y) + f (-(t - y)))) =
      fun t => f t * f (t - y) + f t * f (y - t) + f (-t) * f (t - y) + f (-t) * f (y - t) := by
    funext t
    rw [show -(t - y) = y - t by ring]
    ring
  have h12 : Integrable fun t => f t * f (t - y) + f t * f (y - t) := h1.add h2
  have h123 : Integrable fun t => f t * f (t - y) + f t * f (y - t) + f (-t) * f (t - y) :=
    h12.add h3
  rw [hexp, integral_add h123 h4, integral_add h12 h3, integral_add h1 h2,
    integral_neg_mul_sub_eq_convSquare_neg, integral_neg_mul_sub_eq_add]
  unfold convSquare
  ring

/-- **The archimedean form of the even extension.**
`A(f + f̃) = 2A(f) − 2∫_0^∞ ω(x)(f⋆f)(x) dx`. -/
theorem archForm_evenExt_eq (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hε : 0 < ε)
    (hsupp : ∀ x, x < ε → f x = 0) :
    archForm (fun x => f x + f (-x)) =
      2 * archForm f - 2 * ∫ x in Ioi (0 : ℝ), archLevyDensity x * convSquare f x := by
  have hAe := archForm_eq_levyEnergy (contDiff_evenExt hf) (hasCompactSupport_evenExt hfc)
  have hAo := archForm_eq_levyEnergy (contDiff_oddExt hf) (hasCompactSupport_oddExt hfc)
  have hL := levyEnergy_evenExt_sub_oddExt hf hfc hε hsupp
  have hN := integral_sq_evenExt_eq_oddExt hε hsupp
  have ho := archForm_oddExt_eq hf hfc hε hsupp
  have hdiff : archForm (fun x => f x + f (-x)) - archForm (fun x => f x - f (-x)) =
      -4 * ∫ x in Ioi (0 : ℝ), archLevyDensity x * convSquare f x := by
    rw [hAe, hAo, hN, ← hL]; ring
  linarith

/-- **The prime sum of the even extension.** `P(f + f̃) = 2P(f) + 2Π(f)`. -/
theorem primeSum_evenExt (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hε : 0 < ε)
    (hsupp : ∀ x, x < ε → f x = 0) :
    primeSum (fun x => f x + f (-x)) = 2 * primeSum f + 2 * productPrimePairing f := by
  unfold primeSum productPrimePairing
  have hs1 := summable_primeSum_terms hfc
  have hs2 := summable_productPrimePairing_terms hfc hε hsupp
  rw [← tsum_mul_left, ← tsum_mul_left, ← (hs1.mul_left 2).tsum_add (hs2.mul_left 2)]
  refine tsum_congr fun n => ?_
  have hA := crossCorr_evenExt hf.continuous hfc (Real.log n)
  have hB := crossCorr_evenExt hf.continuous hfc (-Real.log n)
  have h0 : convSquare f (-Real.log n) = 0 :=
    convSquare_eq_zero_of_nonpos hε hsupp (neg_nonpos.mpr (Real.log_natCast_nonneg n))
  simp only [neg_neg, sub_neg_eq_add, ← sub_eq_add_neg] at hB
  simp only
  rw [hA, hB, h0]
  ring

/-- **The even sector of the archimedean-minus-prime form.** For a real `C²` test `f` supported in
`[ε, ∞)` with `ε > 0`,
`M(f + f̃) = 2 M(f) − 2 Σ_{k ≥ 0} (∫ f(x) e^{−(2k+1/2)x} dx)² − 2 Σ_n Λ(n) n^{−1/2} (f⋆f)(log n)`:
the trivial-zero squares and the product pairing enter the even sector with the opposite sign. -/
theorem markovEnergy_evenExtension_eq (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hε : 0 < ε) (hsupp : ∀ x, x < ε → f x = 0) :
    markovEnergy (fun x => ((f x + f (-x) : ℝ) : ℂ)) =
      2 * markovEnergy (fun x => (f x : ℂ)) - 2 * (∑' k : ℕ, (trivialZeroMoment f k) ^ 2) -
        2 * productPrimePairing f := by
  have h1 := markovEnergy_ofReal_eq_archForm_sub_primeSum (contDiff_evenExt hf)
    (hasCompactSupport_evenExt hfc)
  have h2 := markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc
  rw [h1, h2, archForm_evenExt_eq hf hfc hε hsupp, primeSum_evenExt hf hfc hε hsupp,
    integral_archLevyDensity_mul_convSquare_eq_tsum hf.continuous hfc hε hsupp]
  ring

/-- The cosh-moment of the even extension is twice that of `f`. -/
theorem integral_evenExt_mul_cosh (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∫ x, (f x + f (-x)) * Real.cosh (x / 2) = 2 * ∫ x, f x * Real.cosh (x / 2) := by
  have hi : Integrable fun x => f x * Real.cosh (x / 2) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  have hi2 : Integrable fun x => f (-x) * Real.cosh (x / 2) :=
    ((hf.comp continuous_neg).mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_reflect hfc).mul_right
  have hrefl : ∫ x, f (-x) * Real.cosh (x / 2) = ∫ x, f x * Real.cosh (x / 2) := by
    rw [← integral_neg_eq_self (fun x => f (-x) * Real.cosh (x / 2)) volume]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [neg_neg]
    rw [show -x / 2 = -(x / 2) by ring, Real.cosh_neg]
  simp only [add_mul]
  rw [integral_add hi hi2, hrefl]
  ring

/-- **Under RH, `M(f) ≥ Σ_k f̃(−2k)² + Π(f)` for every half-line test with vanishing
cosh-moment.** This is the primitive-hyperplane criterion applied to the even extension. -/
theorem halfLine_markovEnergy_ge_of_riemannHypothesis (hRH : RiemannHypothesis)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hε : 0 < ε)
    (hsupp : ∀ x, x < ε → f x = 0) (hC : ∫ x, f x * Real.cosh (x / 2) = 0) :
    (∑' k : ℕ, (trivialZeroMoment f k) ^ 2) + productPrimePairing f ≤
      markovEnergy (fun x => (f x : ℂ)) := by
  have heven := (riemannHypothesis_iff_forall_cosh_moment_zero_markovEnergy_nonneg.mp hRH)
    (fun x => f x + f (-x)) (contDiff_evenExt hf) (hasCompactSupport_evenExt hfc)
    (by rw [integral_evenExt_mul_cosh hf.continuous hfc, hC, mul_zero])
  have := markovEnergy_evenExtension_eq hf hfc hε hsupp
  linarith

/-- **Two-sided law under RH.** For a half-line test with vanishing cosh-moment,
`|Σ_k f̃(−2k)² + Π(f)| ≤ M(f)`: the Markov form dominates the trivial-zero squares plus the product
pairing in absolute value. -/
theorem abs_trivialZero_add_product_le_markovEnergy_of_riemannHypothesis (hRH : RiemannHypothesis)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hε : 0 < ε)
    (hsupp : ∀ x, x < ε → f x = 0) (hC : ∫ x, f x * Real.cosh (x / 2) = 0) :
    |(∑' k : ℕ, (trivialZeroMoment f k) ^ 2) + productPrimePairing f| ≤
      markovEnergy (fun x => (f x : ℂ)) := by
  have h1 := halfLine_markovEnergy_ge_of_riemannHypothesis hRH hf hfc hε hsupp hC
  have h2 := halfLine_markovEnergy_add_nonneg_of_riemannHypothesis hRH hf hfc hε hsupp
  exact abs_le.mpr ⟨by linarith, h1⟩

end Assembly

/-! ## The holomorphic zero sum of a half-line test -/

section Holomorphic

variable {f : ℝ → ℝ} {ε : ℝ}

/-- **The bilinear explicit formula.** `W(f, g)` is the full Weil functional of `f ⋆ g̃`. -/
theorem zetaZeroConfig_W_eq_weilFullFunctional_bilinear {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    zetaZeroConfig.W f g =
      weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (EF.weilTest f g) := by
  rw [weilFullFunctional_vonMangoldt]
  set k := EF.weilTest f g with hk
  have hkd : ContDiff ℝ 2 k := EF.weilTest_contDiff hf hg.continuous hfc
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hgc
  obtain ⟨-, heq⟩ := WeilEF.EF_lit_zetaZeroConfig k hkd hkc
  have hfac := EF.paperFT_weilTest hf.continuous hg.continuous hfc hgc
  have hterm : (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℂ) * paperFT k (gammaOf ρ)) =
      fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f g ρ := by
    ext ρ; simp only [ZeroConfig.Wsummand, hk, hfac, mul_assoc]
  rw [ZeroConfig.W, ← hterm, heq]

/-- The reflection of a real test is its Weil tilde. -/
theorem ofReal_reflect_eq_tilde (f : ℝ → ℝ) :
    (fun u => (f (-u) : ℂ)) = EF.tilde fun u => (f u : ℂ) := by
  funext u
  simp [EF.tilde, Complex.conj_ofReal]

/-- The pole term of the convolution square: `ℓ₀² + ℓ₁²`. -/
theorem pole_convSquare_re (hf : Continuous f) (hfc : HasCompactSupport f) :
    (paperFT (fun y => (convSquare f y : ℂ)) (I / 2) +
        paperFT (fun y => (convSquare f y : ℂ)) (-I / 2)).re =
      (∫ x, f x * Real.exp (-(x / 2))) ^ 2 + (∫ x, f x * Real.exp (x / 2)) ^ 2 := by
  rw [paperFT_ofReal_I_half_eq_integral, paperFT_ofReal_neg_I_half_eq_integral,
    ← Complex.ofReal_add, Complex.ofReal_re]
  have h1 : ∫ x, convSquare f x * Real.exp (-(x / 2)) = (∫ x, f x * Real.exp (-(x / 2))) ^ 2 := by
    have e1 : (fun x => convSquare f x * Real.exp (-(x / 2))) =
        fun x => Real.exp (-(1 / 2 * x)) * convSquare f x := by
      funext x; rw [mul_comm, show -(x / 2) = -(1 / 2 * x) by ring]
    have e2 : (fun u => f u * Real.exp (-(u / 2))) = fun u => f u * Real.exp (-(1 / 2 * u)) := by
      funext u; rw [show -(u / 2) = -(1 / 2 * u) by ring]
    rw [e1, e2, integral_exp_neg_mul_convSquare hf hfc (1 / 2)]
  have h2 : ∫ x, convSquare f x * Real.exp (x / 2) = (∫ x, f x * Real.exp (x / 2)) ^ 2 := by
    have e1 : (fun x => convSquare f x * Real.exp (x / 2)) =
        fun x => Real.exp (-(-(1 / 2) * x)) * convSquare f x := by
      funext x; rw [mul_comm, show x / 2 = -(-(1 / 2) * x) by ring]
    have e2 : (fun u => f u * Real.exp (u / 2)) = fun u => f u * Real.exp (-(-(1 / 2) * u)) := by
      funext u; rw [show u / 2 = -(-(1 / 2) * u) by ring]
    rw [e1, e2, integral_exp_neg_mul_convSquare hf hfc (-(1 / 2))]
  rw [h1, h2]

/-- The prime term of the convolution square is the product pairing. -/
theorem primes_convSquare_eq (hε : 0 < ε) (hsupp : ∀ x, x < ε → f x = 0) :
    (∑' n : ℕ, ((if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0 : ℝ) : ℂ)
      * ((convSquare f (Real.log n) : ℂ) + (convSquare f (-Real.log n) : ℂ))) =
      ((productPrimePairing f : ℝ) : ℂ) := by
  unfold productPrimePairing
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [convSquare_eq_zero_of_nonpos hε hsupp (neg_nonpos.mpr (Real.log_natCast_nonneg n))]
  unfold vonMangoldtAtom
  push_cast
  ring

/-- `Re(p²) = (|p + p̄|² − |p − p̄|²)/4`. -/
private theorem re_sq_eq (p : ℂ) : (p ^ 2).re = (‖p + conj p‖ ^ 2 - ‖p - conj p‖ ^ 2) / 4 := by
  have h1 : p - conj p = ((2 * p.im : ℝ) : ℂ) * I :=
    Complex.ext (by simp) (by simp; ring)
  have h2 : p + conj p = ((2 * p.re : ℝ) : ℂ) :=
    Complex.ext (by simp; ring) (by simp)
  rw [h1, h2, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, sq, Complex.mul_re]
  ring

/-- The difference of the archimedean forms of the even and odd extensions. -/
theorem archForm_evenExt_sub_oddExt (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hε : 0 < ε)
    (hsupp : ∀ x, x < ε → f x = 0) :
    archForm (fun x => f x + f (-x)) - archForm (fun x => f x - f (-x)) =
      -4 * ∑' k : ℕ, trivialZeroMoment f k ^ 2 := by
  rw [archForm_evenExt_eq hf hfc hε hsupp, archForm_oddExt_eq hf hfc hε hsupp,
    integral_archLevyDensity_mul_convSquare_eq_tsum hf.continuous hfc hε hsupp]
  ring

/-- The archimedean term of the convolution square: minus the trivial-zero squares. -/
theorem arch_convSquare_re (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hε : 0 < ε)
    (hsupp : ∀ x, x < ε → f x = 0) :
    ((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (fun y => (convSquare f y : ℂ)) r *
        (EF.gammaBracket r : ℂ)).re = -∑' k : ℕ, trivialZeroMoment f k ^ 2 := by
  have hU : ContDiff ℝ 2 fun u => (f u : ℂ) := Complex.ofRealCLM.contDiff.comp hf
  have hUc : HasCompactSupport fun u => (f u : ℂ) := hfc.comp_left Complex.ofReal_zero
  have hR : ContDiff ℝ 2 fun u => (f (-u) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (hf.comp contDiff_neg)
  have hRc : HasCompactSupport fun u => (f (-u) : ℂ) :=
    (hasCompactSupport_reflect hfc).comp_left Complex.ofReal_zero
  have hk : (fun y => (convSquare f y : ℂ)) =
      EF.weilTest (fun u => (f u : ℂ)) (fun u => (f (-u) : ℂ)) :=
    (funext (weilTest_ofReal_reflect_eq f)).symm
  -- the transform of the convolution square is the square of the transform
  have hsq : ∀ r : ℝ, paperFT (fun y => (convSquare f y : ℂ)) r =
      (paperFT (fun u => (f u : ℂ)) r) ^ 2 := by
    intro r
    rw [hk, EF.paperFT_weilTest hU.continuous hR.continuous hUc hRc, ofReal_reflect_eq_tilde,
      EF.paperFT_tilde]
    simp only [Complex.conj_conj, Complex.conj_ofReal, sq]
  have hint : Integrable fun r : ℝ => paperFT (fun y => (convSquare f y : ℂ)) r *
      (EF.gammaBracket r : ℂ) := by
    rw [hk]
    exact LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket hU hUc hR hRc
  have i2 := integrable_normSq_paperFT_mul_gammaBracket (contDiff_evenExt hf)
    (hasCompactSupport_evenExt hfc)
  have i3 := integrable_normSq_paperFT_mul_gammaBracket (contDiff_oddExt hf)
    (hasCompactSupport_oddExt hfc)
  rw [show ((1 / (2 * π) : ℂ)) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul,
    show (∫ r : ℝ, paperFT (fun y => (convSquare f y : ℂ)) r * (EF.gammaBracket r : ℂ)).re =
      ∫ r : ℝ, (paperFT (fun y => (convSquare f y : ℂ)) r * (EF.gammaBracket r : ℂ)).re from
      (integral_re hint).symm]
  have hre : ∀ r : ℝ, (paperFT (fun y => (convSquare f y : ℂ)) r * (EF.gammaBracket r : ℂ)).re =
      ((‖paperFT (fun u => ((f u + f (-u) : ℝ) : ℂ)) r‖ ^ 2 * EF.gammaBracket r -
        ‖paperFT (fun u => ((f u - f (-u) : ℝ) : ℂ)) r‖ ^ 2 * EF.gammaBracket r) / 4) := by
    intro r
    rw [Complex.re_mul_ofReal, hsq, re_sq_eq, paperFT_evenExt hf.continuous hfc,
      paperFT_oddExt hf.continuous hfc]
    ring
  simp_rw [hre]
  rw [integral_div, integral_sub i2 i3]
  have hd := archForm_evenExt_sub_oddExt hf hfc hε hsupp
  unfold archForm at hd
  linear_combination (1 / 4 : ℝ) * hd

/-- **The holomorphic zero sum of a half-line test is archimedean-free.**
`Re Σ_ρ m_ρ f̂(γ_ρ)² = ℓ₀² + ℓ₁² − Π(f) − Σ_{k ≥ 0} f̃(−2k)²`, with `ℓ₀ = f̃(−0)` the `k = 0`
trivial-zero moment: the pairing `W(f, f̃)` of a half-line test with its reflection is the square of
the `e^{x/2}`-moment minus the product pairing minus the trivial-zero squares at `k ≥ 1`. -/
theorem W_reflect_re_eq (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hε : 0 < ε)
    (hsupp : ∀ x, x < ε → f x = 0) :
    (zetaZeroConfig.W (fun u => (f u : ℂ)) (fun u => (f (-u) : ℂ))).re =
      (∫ x, f x * Real.exp (-(x / 2))) ^ 2 + (∫ x, f x * Real.exp (x / 2)) ^ 2 -
        productPrimePairing f - ∑' k : ℕ, trivialZeroMoment f k ^ 2 := by
  have hU : ContDiff ℝ 2 fun u => (f u : ℂ) := Complex.ofRealCLM.contDiff.comp hf
  have hUc : HasCompactSupport fun u => (f u : ℂ) := hfc.comp_left Complex.ofReal_zero
  have hR : ContDiff ℝ 2 fun u => (f (-u) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (hf.comp contDiff_neg)
  have hRc : HasCompactSupport fun u => (f (-u) : ℂ) :=
    (hasCompactSupport_reflect hfc).comp_left Complex.ofReal_zero
  have hk : EF.weilTest (fun u => (f u : ℂ)) (fun u => (f (-u) : ℂ)) =
      fun y => (convSquare f y : ℂ) := funext (weilTest_ofReal_reflect_eq f)
  rw [zetaZeroConfig_W_eq_weilFullFunctional_bilinear hU hUc hR hRc]
  unfold weilFullFunctional
  rw [hk, Complex.add_re, Complex.sub_re, pole_convSquare_re hf.continuous hfc,
    primes_convSquare_eq hε hsupp, Complex.ofReal_re, arch_convSquare_re hf hfc hε hsupp]
  ring

end Holomorphic

end

end RHTower
