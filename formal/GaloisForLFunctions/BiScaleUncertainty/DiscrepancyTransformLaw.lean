import GaloisForLFunctions.BiScaleUncertainty.BandLimitedLaplaceEnergy

/-!
# The discrepancy transform law: `ν̂_N` as the Fourier transform of the Chebyshev error

Summation by parts against `ψ(e^t)` (the Stieltjes identity of the hyperbolic gauge) applied to the
frequency character `χ_ξ(t) = e^{−2πiξt}` expresses the Fourier transform of the signed prime–polar
measure through the normalized Chebyshev error `Ẽ(t) = e^{−t/2}(ψ(e^t) − e^t)` alone:

`ν̂_N(ξ) = s(ξ) · ∫_0^L Ẽ(t) e^{−2πiξt} dt + Ẽ(L) e^{−2πiξL} + 1 − (1 − e^{−s(ξ)L})/s(ξ)`,  `s(ξ) = ½ + 2πiξ`.

Dividing by `s(ξ)`: the transform of the causal response is the transform of the windowed Chebyshev
error plus an explicit boundary term,

`𝓕 R_N (ξ) = 𝓕(Ẽ·1_{[0,L]})(ξ) + B_N(ξ)`,  `‖B_N(ξ)‖ ≤ (|Ẽ(L)| + 5)/‖s(ξ)‖`.

The boundary term is the Fourier shadow of the endpoint jump of height `Ẽ(L)` that a sharp window
creates and that the causal continuation of `R_N` past `L` removes; its high-frequency energy is
`≍ Ẽ(L)²/ξ₀`, so the Laplace energy, not the windowed Chebyshev energy, is the band-limited object.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators CompactlySupported Real FourierTransform

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

noncomputable section
set_option autoImplicit false

/-! ## The Stieltjes form of the pairing for a general `C¹` function -/

/-- **Stieltjes form of the pairing** (no compact support needed): for `C¹` `f`,
`pairing N f = f(0) + Ẽ(L) f(L) − ∫_0^L Ẽ (f' − f/2) − ∫_0^L e^{−t/2} f`. -/
theorem pairing_eq_stieltjes_gauge (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (N : ℕ) :
    pairing N f = f 0 + normalizedLogError (cutoff N) * f (cutoff N) -
      (∫ t in Icc 0 (cutoff N), normalizedLogError t * gaugeDerivative f t) -
      ∫ t in Icc 0 (cutoff N), Real.exp (-t / 2) * f t := by
  have hexp : Continuous fun t : ℝ => Real.exp (-t / 2) :=
    Real.continuous_exp.comp (continuous_id.neg.div_const 2)
  have hQc : Continuous fun t => Real.exp (-t / 2) * gaugeDerivative f t :=
    hexp.mul (continuous_gaugeDerivative hf)
  have hGd : ∀ t, HasDerivAt (fun t => Real.exp (-t / 2) * f t)
      (Real.exp (-t / 2) * gaugeDerivative f t) t := by
    intro t
    have := hasDerivAt_exp_neg_half_mul hf 0 t
    simpa only [zero_add] using this
  have hst := stieltjes_vonMangoldt_identity _ _ hQc hGd N
  -- the atomic part
  have hatom : (∑ n ∈ Finset.Icc 1 (N + 2), primeWeight n * f (Real.log n)) =
      ∑ n ∈ Finset.Icc 1 (N + 2),
        ArithmeticFunction.vonMangoldt n * (Real.exp (-Real.log n / 2) * f (Real.log n)) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [primeWeight]
    rw [exp_neg_half_log_eq (Finset.mem_Icc.mp hn).1]
    ring
  -- the polar part
  have hpolar : (∫ t in Icc 0 (cutoff N), polarDensity t * f t) =
      (∫ x in Icc 0 (cutoff N), Real.exp (-x / 2) * f x * Real.exp x) +
        ∫ t in Icc 0 (cutoff N), Real.exp (-t / 2) * f t := by
    have h1 : IntegrableOn (fun x => Real.exp (-x / 2) * f x * Real.exp x) (Icc 0 (cutoff N)) :=
      ((hexp.mul hf.continuous).mul Real.continuous_exp).integrableOn_Icc
    have h2 : IntegrableOn (fun t => Real.exp (-t / 2) * f t) (Icc 0 (cutoff N)) :=
      (hexp.mul hf.continuous).integrableOn_Icc
    rw [← integral_add h1 h2]
    refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
    simp only [polarDensity, Real.cosh_eq]
    have he : Real.exp (-t / 2) * Real.exp t = Real.exp (t / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [show -(t / 2) = -t / 2 by ring]
    nlinarith only [congrArg (fun z : ℝ => z * f t) he]
  have hconv : (∫ x in Icc 0 (cutoff N), Real.exp (-x / 2) * gaugeDerivative f x * logError x) =
      ∫ t in Icc 0 (cutoff N), normalizedLogError t * gaugeDerivative f t := by
    refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
    unfold normalizedLogError; ring
  unfold pairing
  rw [hatom, hpolar]
  have hG0 : Real.exp (-0 / 2) * f 0 = f 0 := by simp
  have hGL : Real.exp (-cutoff N / 2) * f (cutoff N) * logError (cutoff N) =
      normalizedLogError (cutoff N) * f (cutoff N) := by
    unfold normalizedLogError; ring
  rw [hG0, hGL, hconv] at hst
  linarith only [hst]

/-! ## The complex pairing through real and imaginary parts -/

theorem pairingC_add (N : ℕ) {h₁ h₂ : ℝ → ℂ} (hc₁ : Continuous h₁) (hc₂ : Continuous h₂) :
    pairingC N (fun s => h₁ s + h₂ s) = pairingC N h₁ + pairingC N h₂ := by
  have i₁ : IntegrableOn (fun x => (polarDensity x : ℂ) * h₁ x) (Icc 0 (cutoff N)) :=
    ((Complex.continuous_ofReal.comp continuous_polarDensity).mul hc₁).integrableOn_Icc
  have i₂ : IntegrableOn (fun x => (polarDensity x : ℂ) * h₂ x) (Icc 0 (cutoff N)) :=
    ((Complex.continuous_ofReal.comp continuous_polarDensity).mul hc₂).integrableOn_Icc
  have hs : (∑ n ∈ Finset.Icc 1 (N + 2), (primeWeight n : ℂ) * (h₁ (Real.log n) + h₂ (Real.log n))) =
      (∑ n ∈ Finset.Icc 1 (N + 2), (primeWeight n : ℂ) * h₁ (Real.log n)) +
        ∑ n ∈ Finset.Icc 1 (N + 2), (primeWeight n : ℂ) * h₂ (Real.log n) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hi : (∫ x in Icc 0 (cutoff N), (polarDensity x : ℂ) * (h₁ x + h₂ x)) =
      (∫ x in Icc 0 (cutoff N), (polarDensity x : ℂ) * h₁ x) +
        ∫ x in Icc 0 (cutoff N), (polarDensity x : ℂ) * h₂ x := by
    rw [← integral_add i₁ i₂]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  unfold pairingC
  show (∑ n ∈ Finset.Icc 1 (N + 2), (primeWeight n : ℂ) * (h₁ (Real.log n) + h₂ (Real.log n))) -
    (∫ x in Icc 0 (cutoff N), (polarDensity x : ℂ) * (h₁ x + h₂ x)) = _
  rw [hs, hi]
  ring

/-- Real and imaginary parts of the complex pairing. -/
theorem pairingC_eq_re_add_im (N : ℕ) (f₁ f₂ : ℝ → ℝ) (hc₁ : Continuous f₁) (hc₂ : Continuous f₂) :
    pairingC N (fun t => (f₁ t : ℂ) + Complex.I * (f₂ t : ℂ)) =
      (pairing N f₁ : ℂ) + Complex.I * (pairing N f₂ : ℂ) := by
  rw [pairingC_add N (h₁ := fun t => (f₁ t : ℂ)) (h₂ := fun t => Complex.I * (f₂ t : ℂ))
    (by fun_prop) (by fun_prop), pairingC_const_mul, pairingC_ofReal, pairingC_ofReal]

/-- Splitting a complex set integral of the form `∫ (a + I b)` into real integrals. -/
theorem integral_ofReal_add_I_mul_ofReal {s : Set ℝ} (a b : ℝ → ℝ) (ha : IntegrableOn a s)
    (hb : IntegrableOn b s) :
    (∫ t in s, (a t : ℂ) + Complex.I * (b t : ℂ)) =
      ((∫ t in s, a t : ℝ) : ℂ) + Complex.I * ((∫ t in s, b t : ℝ) : ℂ) := by
  refine (integral_add ha.ofReal (hb.ofReal.const_mul Complex.I)).trans ?_
  rw [integral_const_mul, ← integral_complex_ofReal, ← integral_complex_ofReal]
  rfl

/-- **Complex Stieltjes form of the pairing** for `h = f₁ + i f₂` with `f₁, f₂ ∈ C¹`. -/
theorem pairingC_eq_stieltjes_gauge (f₁ f₂ : ℝ → ℝ) (h₁ : ContDiff ℝ 1 f₁) (h₂ : ContDiff ℝ 1 f₂)
    (N : ℕ) :
    pairingC N (fun t => (f₁ t : ℂ) + Complex.I * (f₂ t : ℂ)) =
      ((f₁ 0 : ℂ) + Complex.I * (f₂ 0 : ℂ)) +
        (normalizedLogError (cutoff N) : ℂ) *
          ((f₁ (cutoff N) : ℂ) + Complex.I * (f₂ (cutoff N) : ℂ)) -
        (∫ t in Icc 0 (cutoff N), (normalizedLogError t : ℂ) *
          ((gaugeDerivative f₁ t : ℂ) + Complex.I * (gaugeDerivative f₂ t : ℂ))) -
        ∫ t in Icc 0 (cutoff N), (Real.exp (-t / 2) : ℂ) * ((f₁ t : ℂ) + Complex.I * (f₂ t : ℂ)) := by
  have hexp : Continuous fun t : ℝ => Real.exp (-t / 2) :=
    Real.continuous_exp.comp (continuous_id.neg.div_const 2)
  have hE : ∀ g : ℝ → ℝ, Continuous (gaugeDerivative g) →
      IntegrableOn (fun t => normalizedLogError t * gaugeDerivative g t) (Icc 0 (cutoff N)) := by
    intro g hg
    have := integrable_mul_logError (fun t => Real.exp (-t / 2) * gaugeDerivative g t)
      (hexp.mul hg) N
    refine this.congr_fun (fun t _ => ?_) measurableSet_Icc
    unfold normalizedLogError; ring
  have hF : ∀ g : ℝ → ℝ, Continuous g →
      IntegrableOn (fun t => Real.exp (-t / 2) * g t) (Icc 0 (cutoff N)) :=
    fun g hg => (hexp.mul hg).integrableOn_Icc
  rw [pairingC_eq_re_add_im N f₁ f₂ h₁.continuous h₂.continuous,
    pairing_eq_stieltjes_gauge f₁ h₁ N, pairing_eq_stieltjes_gauge f₂ h₂ N]
  have e1 : (∫ t in Icc 0 (cutoff N), (normalizedLogError t : ℂ) *
      ((gaugeDerivative f₁ t : ℂ) + Complex.I * (gaugeDerivative f₂ t : ℂ))) =
      ((∫ t in Icc 0 (cutoff N), normalizedLogError t * gaugeDerivative f₁ t : ℝ) : ℂ) +
        Complex.I * ((∫ t in Icc 0 (cutoff N), normalizedLogError t * gaugeDerivative f₂ t : ℝ) : ℂ) := by
    rw [← integral_ofReal_add_I_mul_ofReal _ _ (hE f₁ (continuous_gaugeDerivative h₁))
      (hE f₂ (continuous_gaugeDerivative h₂))]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    push_cast; ring
  have e2 : (∫ t in Icc 0 (cutoff N), (Real.exp (-t / 2) : ℂ) * ((f₁ t : ℂ) + Complex.I * (f₂ t : ℂ))) =
      ((∫ t in Icc 0 (cutoff N), Real.exp (-t / 2) * f₁ t : ℝ) : ℂ) +
        Complex.I * ((∫ t in Icc 0 (cutoff N), Real.exp (-t / 2) * f₂ t : ℝ) : ℂ) := by
    rw [← integral_ofReal_add_I_mul_ofReal _ _ (hF f₁ h₁.continuous) (hF f₂ h₂.continuous)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    push_cast; ring
  rw [e1, e2]
  push_cast
  ring

/-! ## The frequency character in real and imaginary parts -/

theorem frequencyCharacter_re (ξ t : ℝ) :
    (frequencyCharacter ξ t).re = Real.cos (2 * π * t * ξ) := by
  unfold frequencyCharacter
  rw [← Complex.ofReal_neg, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

theorem frequencyCharacter_im (ξ t : ℝ) :
    (frequencyCharacter ξ t).im = -Real.sin (2 * π * t * ξ) := by
  unfold frequencyCharacter
  rw [← Complex.ofReal_neg, Complex.exp_ofReal_mul_I_im, Real.sin_neg]

theorem frequencyCharacter_eq_cos_add_I_mul (ξ t : ℝ) :
    frequencyCharacter ξ t =
      (Real.cos (2 * π * t * ξ) : ℂ) + Complex.I * ((-Real.sin (2 * π * t * ξ) : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, frequencyCharacter_re]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, frequencyCharacter_im]
    ring

theorem contDiff_cos_freq (ξ : ℝ) : ContDiff ℝ 1 fun t : ℝ => Real.cos (2 * π * t * ξ) := by
  fun_prop

theorem contDiff_neg_sin_freq (ξ : ℝ) : ContDiff ℝ 1 fun t : ℝ => -Real.sin (2 * π * t * ξ) := by
  fun_prop

theorem hasDerivAt_freq (ξ t : ℝ) :
    HasDerivAt (fun t : ℝ => 2 * π * t * ξ) (2 * π * ξ) t := by
  have := ((hasDerivAt_id t).const_mul (2 * π)).mul_const ξ
  simpa using this

theorem gaugeDerivative_cos_freq (ξ t : ℝ) :
    gaugeDerivative (fun t : ℝ => Real.cos (2 * π * t * ξ)) t =
      -(2 * π * ξ) * Real.sin (2 * π * t * ξ) - Real.cos (2 * π * t * ξ) / 2 := by
  unfold gaugeDerivative
  rw [((hasDerivAt_freq ξ t).cos).deriv]
  ring

theorem gaugeDerivative_neg_sin_freq (ξ t : ℝ) :
    gaugeDerivative (fun t : ℝ => -Real.sin (2 * π * t * ξ)) t =
      -(2 * π * ξ) * Real.cos (2 * π * t * ξ) + Real.sin (2 * π * t * ξ) / 2 := by
  have h : HasDerivAt (fun t : ℝ => -Real.sin (2 * π * t * ξ))
      (-(Real.cos (2 * π * t * ξ) * (2 * π * ξ))) t := (hasDerivAt_freq ξ t).sin.neg
  unfold gaugeDerivative
  rw [h.deriv]
  ring

/-- The gauge derivative of the frequency character is `−s(ξ) χ_ξ`. -/
theorem gaugeDerivative_frequencyCharacter (ξ t : ℝ) :
    (gaugeDerivative (fun t : ℝ => Real.cos (2 * π * t * ξ)) t : ℂ) +
      Complex.I * (gaugeDerivative (fun t : ℝ => -Real.sin (2 * π * t * ξ)) t : ℂ) =
      -criticalPoint ξ * frequencyCharacter ξ t := by
  rw [gaugeDerivative_cos_freq, gaugeDerivative_neg_sin_freq]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, criticalPoint_re, criticalPoint_im,
      frequencyCharacter_re, frequencyCharacter_im]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, criticalPoint_re, criticalPoint_im,
      frequencyCharacter_re, frequencyCharacter_im]
    ring

/-- `∫_0^L e^{−t/2} χ_ξ(t) dt = (1 − e^{−s(ξ)L})/s(ξ)`. -/
theorem integral_exp_neg_half_mul_frequencyCharacter (N : ℕ) (ξ : ℝ) :
    (∫ t in Icc 0 (cutoff N), (Real.exp (-t / 2) : ℂ) * frequencyCharacter ξ t) =
      (1 - Complex.exp (-criticalPoint ξ * cutoff N)) / criticalPoint ξ := by
  have hcongr : ∀ t : ℝ, (Real.exp (-t / 2) : ℂ) * frequencyCharacter ξ t =
      Complex.exp (-criticalPoint ξ * t) := by
    intro t
    unfold frequencyCharacter
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp [criticalPoint] <;> ring
  have hc : Continuous fun x : ℝ => Complex.exp (-criticalPoint ξ * x) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  rw [setIntegral_congr_fun measurableSet_Icc fun t _ => hcongr t, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (cutoff_nonneg N),
    integral_exp_mul_complex (neg_ne_zero.2 (criticalPoint_ne_zero ξ))]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  ring

/-! ## The discrepancy transform law -/

/-- **The discrepancy transform law:**
`ν̂_N(ξ) = s(ξ) ∫_0^L Ẽ χ_ξ + Ẽ(L) χ_ξ(L) + 1 − (1 − e^{−s(ξ)L})/s(ξ)`. -/
theorem fourierPairing_eq_discrepancy_transform (N : ℕ) (ξ : ℝ) :
    fourierPairing N ξ =
      criticalPoint ξ * (∫ t in Icc 0 (cutoff N), (normalizedLogError t : ℂ) * frequencyCharacter ξ t) +
        (normalizedLogError (cutoff N) : ℂ) * frequencyCharacter ξ (cutoff N) + 1 -
        (1 - Complex.exp (-criticalPoint ξ * cutoff N)) / criticalPoint ξ := by
  have hχ : (fun s => frequencyCharacter ξ s) = fun t =>
      (Real.cos (2 * π * t * ξ) : ℂ) + Complex.I * ((-Real.sin (2 * π * t * ξ) : ℝ) : ℂ) :=
    funext fun t => frequencyCharacter_eq_cos_add_I_mul ξ t
  unfold fourierPairing
  rw [hχ, pairingC_eq_stieltjes_gauge _ _ (contDiff_cos_freq ξ) (contDiff_neg_sin_freq ξ) N]
  -- rewrite the three pieces back in terms of the character
  have hL : ((Real.cos (2 * π * cutoff N * ξ) : ℝ) : ℂ) +
      Complex.I * ((-Real.sin (2 * π * cutoff N * ξ) : ℝ) : ℂ) = frequencyCharacter ξ (cutoff N) :=
    (frequencyCharacter_eq_cos_add_I_mul ξ (cutoff N)).symm
  have h0 : ((Real.cos (2 * π * 0 * ξ) : ℝ) : ℂ) +
      Complex.I * ((-Real.sin (2 * π * 0 * ξ) : ℝ) : ℂ) = 1 := by
    rw [← frequencyCharacter_eq_cos_add_I_mul]
    unfold frequencyCharacter
    simp
  have hgauge : (∫ t in Icc 0 (cutoff N), (normalizedLogError t : ℂ) *
      ((gaugeDerivative (fun t : ℝ => Real.cos (2 * π * t * ξ)) t : ℂ) +
        Complex.I * (gaugeDerivative (fun t : ℝ => -Real.sin (2 * π * t * ξ)) t : ℂ))) =
      -criticalPoint ξ * ∫ t in Icc 0 (cutoff N), (normalizedLogError t : ℂ) * frequencyCharacter ξ t := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
    rw [gaugeDerivative_frequencyCharacter]
    ring
  have hpolar : (∫ t in Icc 0 (cutoff N), (Real.exp (-t / 2) : ℂ) *
      ((Real.cos (2 * π * t * ξ) : ℂ) + Complex.I * ((-Real.sin (2 * π * t * ξ) : ℝ) : ℂ))) =
      (1 - Complex.exp (-criticalPoint ξ * cutoff N)) / criticalPoint ξ := by
    rw [← integral_exp_neg_half_mul_frequencyCharacter N ξ]
    refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
    rw [frequencyCharacter_eq_cos_add_I_mul]
  rw [hL, h0, hgauge, hpolar]
  ring

/-! ## The transform of the causal response versus the windowed Chebyshev error -/

/-- The Fourier transform of the sharply windowed Chebyshev error. -/
theorem fourier_windowed_normalizedLogError (N : ℕ) (ξ : ℝ) :
    𝓕 (fun t => (((Icc (0 : ℝ) (cutoff N)).indicator normalizedLogError t : ℝ) : ℂ)) ξ =
      ∫ t in Icc 0 (cutoff N), (normalizedLogError t : ℂ) * frequencyCharacter ξ t := by
  rw [fourierTransform_eq_integral_exp, ← integral_indicator measurableSet_Icc]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  show Complex.exp (-(2 * π * t * ξ : ℝ) * Complex.I) *
      (((Icc (0 : ℝ) (cutoff N)).indicator normalizedLogError t : ℝ) : ℂ) =
    (Icc (0 : ℝ) (cutoff N)).indicator (fun t => (normalizedLogError t : ℂ) * frequencyCharacter ξ t) t
  by_cases ht : t ∈ Icc (0 : ℝ) (cutoff N)
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
    unfold frequencyCharacter; ring
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, Complex.ofReal_zero, mul_zero]

/-- The boundary term `B_N(ξ) = (Ẽ(L) χ_ξ(L) + 1 − (1 − e^{−sL})/s)/s`. -/
def boundaryTransform (N : ℕ) (ξ : ℝ) : ℂ :=
  ((normalizedLogError (cutoff N) : ℂ) * frequencyCharacter ξ (cutoff N) + 1 -
    (1 - Complex.exp (-criticalPoint ξ * cutoff N)) / criticalPoint ξ) / criticalPoint ξ

/-- **`𝓕 R_N = 𝓕(Ẽ·1_{[0,L]}) + B_N`.** -/
theorem fourier_causalResponse_eq_windowed_add_boundary (N : ℕ) (ξ : ℝ) :
    𝓕 (fun t => (causalResponse N t : ℂ)) ξ =
      𝓕 (fun t => (((Icc (0 : ℝ) (cutoff N)).indicator normalizedLogError t : ℝ) : ℂ)) ξ +
        boundaryTransform N ξ := by
  rw [fourier_causalResponse, fourier_windowed_normalizedLogError,
    fourierPairing_eq_discrepancy_transform]
  unfold boundaryTransform
  have hs := criticalPoint_ne_zero ξ
  field_simp
  ring

theorem norm_criticalPoint_ge_half (ξ : ℝ) : 1 / 2 ≤ ‖criticalPoint ξ‖ := by
  have h : (1 / 2 : ℝ) ^ 2 ≤ ‖criticalPoint ξ‖ ^ 2 := by
    rw [Complex.sq_norm, normSq_criticalPoint]; nlinarith [sq_nonneg (2 * π * ξ)]
  nlinarith [h, norm_nonneg (criticalPoint ξ)]

/-- **The boundary term is `O((|Ẽ(L)| + 5)/|s|)`.** -/
theorem norm_boundaryTransform_le (N : ℕ) (ξ : ℝ) :
    ‖boundaryTransform N ξ‖ ≤ (|normalizedLogError (cutoff N)| + 5) / ‖criticalPoint ξ‖ := by
  have hs0 : 0 < ‖criticalPoint ξ‖ := norm_pos_iff.2 (criticalPoint_ne_zero ξ)
  have hhalf := norm_criticalPoint_ge_half ξ
  have he : ‖Complex.exp (-criticalPoint ξ * cutoff N)‖ ≤ 1 := by
    rw [Complex.norm_exp, re_neg_criticalPoint_mul]
    exact Real.exp_le_one_iff.2 (by linarith [cutoff_nonneg N])
  have hpole : ‖(1 - Complex.exp (-criticalPoint ξ * cutoff N)) / criticalPoint ξ‖ ≤ 4 := by
    rw [norm_div]
    have : ‖1 - Complex.exp (-criticalPoint ξ * cutoff N)‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
    rw [div_le_iff₀ hs0]
    nlinarith
  unfold boundaryTransform
  rw [norm_div]
  refine div_le_div_of_nonneg_right ?_ hs0.le
  calc ‖(normalizedLogError (cutoff N) : ℂ) * frequencyCharacter ξ (cutoff N) + 1 -
        (1 - Complex.exp (-criticalPoint ξ * cutoff N)) / criticalPoint ξ‖
      ≤ ‖(normalizedLogError (cutoff N) : ℂ) * frequencyCharacter ξ (cutoff N)‖ + ‖(1 : ℂ)‖ +
          ‖(1 - Complex.exp (-criticalPoint ξ * cutoff N)) / criticalPoint ξ‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ |normalizedLogError (cutoff N)| + 1 + 4 := by
        rw [norm_mul, norm_frequencyCharacter, mul_one, Complex.norm_real, Real.norm_eq_abs, norm_one]
        linarith
    _ = |normalizedLogError (cutoff N)| + 5 := by ring

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
