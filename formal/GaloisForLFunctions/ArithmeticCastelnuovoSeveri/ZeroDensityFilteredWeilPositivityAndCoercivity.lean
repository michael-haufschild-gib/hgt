import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.AllParityCriticalDeficitAndEndpointSobolevLaws
import GaloisForLFunctions.BiScaleUncertainty.ZeroDensityFilteredCriticalDeficitLaw
import GaloisForLFunctions.RHTower.CCM.CCMZetaWeilSmoothIdentity
import GaloisForLFunctions.RHTower.OffLineDensityWeilLowerBound
import GaloisForLFunctions.RHTower.ZetaSymbolArchimedeanHorizon
import GaloisForLFunctions.RHTower.ZetaRightZeroWeightedCount
import GaloisForLFunctions.RHTower.XiLogDerivLineOneWindowLower
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTentActualZetaDetectionAndFullZeroFormBridge

/-!
# Zero-Density Filtered Weil Positivity, Sub-Power Coercivity up to `(2/3) log Γ`, and Logarithmic-Aperture Strict Positivity

Unfiltered Weil forms `fullZeroForm F` on `C²_c([-A, A])` are governed by the worst single zero
(`zetaZeroWidth`), where the sharpest unconditional pointwise saving is Vinogradov–Korobov
`O(e^{A - κ A^{3/5 - ε}})` (`AllParityCriticalDeficitAndEndpointSobolevLaws`) and single-height
positivity breaks down above doubly logarithmic aperture `A ≲ log log Γ`
(`ZetaSingleHeightPositivityAboveArchimedeanHorizon`). Meanwhile, fixed-width spectral convolution
truncates prime support to `O(1)` (`WindowedPositivityNoGoForOffLineConfigurations`).

Modulating a compactly supported `C²` envelope `F₀` on `[-A, A]` by a high-frequency carrier
`cos(γ u)` (or complex quadrature `(cosineSource F₀ γ, sineSource F₀ γ)`) at `γ ∈ [Γ, 2Γ]`
preserves exact compact prime support `[-A, A]` (`X = e^{2A}`) while localizing the zero-side
spectral sum to ordinates `|Im ρ| ≍ Γ`, replacing `zetaZeroWidth` by unconditional zero-density
estimates:

1. **Exact All-Parity Quadrature Critical-Deficit Identity (§1)**
   (`fullZeroForm_cosine_add_sine_eq_zeta_W_re`,
   `fullZeroForm_cosine_add_sine_eq_gammaBracket_add_criticalDeficit`,
   `scalingSubsurface_defect_cosine_add_sine_eq`):
   Uniting `fullZeroForm_eq_levy_add_horizon_add_criticalDeficit` with
   `biScaleLevyEnergy_cosine_sine_eq` and `zeta_W_re_eq_fullZeroForm_re_add_im`, the quadrature
   Weil sum `fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ)` equals
   `(zetaZeroConfig.W (complexModulatedSource F₀ γ) (complexModulatedSource F₀ γ)).re` and equals
   `(gammaBracket γ - 2) ∫ F₀² + archEnvelopeError F₀ γ + 4 * horizonEnergy (cosineSource F₀ γ)
     + 4 * horizonEnergy (sineSource F₀ γ)
     + 2 ∫_0^{2A} ccmPrimeDeficitIncoming t * doubleGaugeDerivative (autocorr F₀ * cos(γ ·)) t dt`,
   exhibiting the exact `2 log(γ / 2π)` archimedean main term alongside the cosine-modulated
   critical prime deficit.

2. **Sub-Power Frequency-Averaged Coercivity up to Aperture `A ≤ α log Γ`, `α < 2/3` (§2–§3)**
   (`exists_frequencyAverage_quadrature_fullZeroForm_ge_subpower`,
   `exists_frequencyAverage_fullZeroForm_cosineSource_ge_subpower`,
   `exists_frequencyAverage_fullZeroForm_ge_neg_exp_every_pos_rate`,
   `exists_volume_bad_frequencies_fullZeroForm_cosineSource_le`):
   By Plancherel on the off-line depth-difference profile
   `u ↦ F₀(u)(e^{(Re ρ - 1/2)u} - e^{-(Re ρ - 1/2)u})e^{i (Im ρ) u}` (which vanishes on `Re ρ = 1/2`
   and costs pure `L²` envelope mass `2π e^{2A|Re ρ - 1/2|} ∫ F₀²` with zero `H¹` derivative loss)
   coupled with the hybrid Ingham–Guth–Maynard–DH `4/3` linear deficit law
   (`ZeroDensityFilteredCriticalDeficitLaw`), for **every** `0 ≤ α < 2/3` (exceeding both Huxley
   `5/12` and Guth–Maynard `13/30`) and **every** `η > 0`:
   `(1 / Γ) ∫_Γ^{2Γ} fullZeroForm (cosineSource F₀ γ) dγ ≥ -C_{α,η} Γ^η ∫ F₀² - C_rem Γ^{α - 2} W(F₀)²`.
   Along `Γ = e^{λ A}` (`λ > 3/2`), the effective exponential floor rate collapses unconditionally
   from `zetaZeroWidth` to **`0`** (`∀ β > 0, O(e^{2βA})`), and Markov's inequality bounds the
   measure of bad frequencies in `[Γ, 2Γ]` by `O(Γ^{1 - η}) = o(Γ)`.

3. **Unconditional Logarithmic-Aperture Strict Positivity via Selberg Near-Line Density (§4)**
   (`exists_logarithmic_aperture_frequencyAverage_quadrature_pos`,
   `exists_logarithmic_aperture_frequencyAverage_fullZeroForm_cosineSource_pos`,
   `exists_positive_measure_frequencies_fullZeroForm_cosineSource_pos`):
   Combining Riemann–von Mangoldt (`≥ c₁ Γ log Γ` interior zeros in `(5Γ/4, 3Γ/2]`, each
   contributing `≥ (π/4) ∫ F₀² - O(Γ^{-2})` to the positive polarization square regardless of `Re ρ`)
   with quadratic near-line cancellation `(e^{δ u} - e^{-δ u})² ≤ 4 A² δ² e^{2A|δ|}` on shallow
   zeros and Selberg's log-free exponential near-line weighted count (`exists_windowZeros_weighted_le`)
   across 5 overlapping dyadic windows covering `[Γ/2, 4Γ]`, there exist explicit constants
   `κ₀ > 0`, `c₀ > 0`, `C₀ ≥ 0`, and `Γ₀ ≥ 32` such that for all `Γ ≥ Γ₀` and all `0 ≤ A ≤ κ₀ log Γ`
   (polynomial prime scale `X = e^{2A} ≤ Γ^{2κ₀}`):
   `(1 / Γ) ∫_Γ^{2Γ} fullZeroForm (cosineSource F₀ γ) dγ ≥ c₀ (log Γ) ∫ F₀² - C₀ Γ^{-4/3} W(F₀)²`,
   yielding strict positivity (and positive Lebesgue measure of strictly positive individual
   frequencies `γ ∈ [Γ, 2Γ]`) exponentially beyond single-height positivity (`A ≲ log log Γ`).
-/

open Complex MeasureTheory Real Set Filter Topology Finset
open scoped BigOperators Real ComplexConjugate ENNReal NNReal
open Zeta23 RHTower GaloisForLFunctions.ArithmeticCriticalityTheory
  GaloisForLFunctions.ArithmeticPositivityTheory
  GaloisForLFunctions.ArithmeticIncidencePositivity
  GaloisForLFunctions.ArithmeticCompensationTheory
  GaloisForLFunctions.BiScaleUncertainty
  GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
  GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

set_option autoImplicit false

/-! ## §1. Exact All-Parity Quadrature Critical-Deficit Identity -/

/-- Complex single-sideband modulated envelope `u ↦ F₀(u) e^{-i γ u}` whose real and imaginary parts
are `cosineSource F₀ γ` and `-sineSource F₀ γ`, and whose `paperFT` at `z` is `paperFT F₀ (z - γ)`. -/
def complexModulatedSource (F₀ : ℝ → ℝ) (γ u : ℝ) : ℂ :=
  (F₀ u : ℂ) * Complex.exp (-Complex.I * (γ : ℂ) * (u : ℂ))

theorem contDiff_complexModulatedSource {F₀ : ℝ → ℝ} {r : WithTop ℕ∞}
    (hF₀ : ContDiff ℝ r F₀) (γ : ℝ) :
    ContDiff ℝ r (complexModulatedSource F₀ γ) :=
  (Complex.ofRealCLM.contDiff.comp hF₀).mul
    (Complex.contDiff_exp.comp ((contDiff_const.mul Complex.ofRealCLM.contDiff)))

theorem hasCompactSupport_complexModulatedSource {F₀ : ℝ → ℝ}
    (hF₀c : HasCompactSupport F₀) (γ : ℝ) :
    HasCompactSupport (complexModulatedSource F₀ γ) :=
  (hF₀c.comp_left Complex.ofReal_zero).mul_right

theorem complexModulatedSource_re (F₀ : ℝ → ℝ) (γ u : ℝ) :
    (complexModulatedSource F₀ γ u).re = cosineSource F₀ γ u := by
  unfold complexModulatedSource cosineSource
  have hz : -Complex.I * (γ : ℂ) * (u : ℂ) = (((-(γ * u)) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hz, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Real.cos_neg]
  ring

theorem complexModulatedSource_im (F₀ : ℝ → ℝ) (γ u : ℝ) :
    (complexModulatedSource F₀ γ u).im = -sineSource F₀ γ u := by
  unfold complexModulatedSource sineSource
  have hz : -Complex.I * (γ : ℂ) * (u : ℂ) = (((-(γ * u)) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hz, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Real.sin_neg]
  ring

/-- Sign invariance of `fullZeroForm`: `fullZeroForm (-g) = fullZeroForm g`. -/
theorem fullZeroForm_neg {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    fullZeroForm (fun u => -g u) = fullZeroForm g := by
  rw [fullZeroForm_eq_zeta_W_re hg.neg hgc.neg, fullZeroForm_eq_zeta_W_re hg hgc]
  congr 1
  unfold ZeroConfig.W
  refine tsum_congr fun ρ => ?_
  have hft : ∀ z : ℂ, paperFT (fun x : ℝ => ((-g x : ℝ) : ℂ)) z =
      -paperFT (fun x : ℝ => (g x : ℂ)) z := fun z => by
    unfold paperFT
    simp_rw [Complex.ofReal_neg, neg_mul]
    exact integral_neg _
  unfold ZeroConfig.Wsummand
  rw [hft, hft, map_neg]
  ring

/-- **Quadrature Zero-Side Identity (`fullZeroForm_cosine_add_sine_eq_zeta_W_re`):**
For every `F₀ ∈ C²_c(ℝ)` and every frequency `γ ∈ ℝ`, the quadrature sum of `fullZeroForm` on
`cosineSource F₀ γ` and `sineSource F₀ γ` equals the complex Weil energy of `complexModulatedSource F₀ γ`. -/
theorem fullZeroForm_cosine_add_sine_eq_zeta_W_re {F₀ : ℝ → ℝ}
    (hF₀ : ContDiff ℝ 2 F₀) (hF₀c : HasCompactSupport F₀) (γ : ℝ) :
    fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ) =
      (zetaZeroConfig.W (complexModulatedSource F₀ γ) (complexModulatedSource F₀ γ)).re := by
  rw [zeta_W_re_eq_fullZeroForm_re_add_im (contDiff_complexModulatedSource hF₀ γ)
    (hasCompactSupport_complexModulatedSource hF₀c γ)]
  simp_rw [complexModulatedSource_re, complexModulatedSource_im]
  rw [fullZeroForm_neg (contDiff_sineSource hF₀ γ) hF₀c.mul_right]

/-- Additivity of `gaugeDerivative` on `C¹` functions. -/
theorem gaugeDerivative_add {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    gaugeDerivative (fun s => f s + g s) = fun s => gaugeDerivative f s + gaugeDerivative g s := by
  funext s
  unfold gaugeDerivative
  have hd : deriv (fun u => f u + g u) s = deriv f s + deriv g s :=
    ((hf.differentiable one_ne_zero s).hasDerivAt.add
      (hg.differentiable one_ne_zero s).hasDerivAt).deriv
  rw [hd]
  ring

/-- Additivity of `doubleGaugeDerivative` on `C²` functions. -/
theorem doubleGaugeDerivative_add {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (s : ℝ) :
    doubleGaugeDerivative (fun u => f u + g u) s =
      doubleGaugeDerivative f s + doubleGaugeDerivative g s := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hGf : ContDiff ℝ 1 (gaugeDerivative f) := contDiff_one_gaugeDerivative hf
  have hGg : ContDiff ℝ 1 (gaugeDerivative g) := contDiff_one_gaugeDerivative hg
  unfold doubleGaugeDerivative
  rw [gaugeDerivative_add hf1 hg1]
  exact congrFun (gaugeDerivative_add hGf hGg) s

/-- **Exact All-Parity Quadrature Critical-Deficit Identity
(`fullZeroForm_cosine_add_sine_eq_gammaBracket_add_criticalDeficit`):**
For every `F₀ ∈ C²_c(ℝ)` supported in `[-A, A]` (`0 ≤ A`) and every frequency `γ ∈ ℝ`,
`fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ)` equals
`(gammaBracket γ - 2) ∫ F₀² + archEnvelopeError F₀ γ + 4 * horizonEnergy (cosineSource F₀ γ)
  + 4 * horizonEnergy (sineSource F₀ γ)
  + 2 ∫_{0}^{2A} ccmPrimeDeficitIncoming t * doubleGaugeDerivative (autocorr F₀ * cos(γ ·)) t dt`. -/
theorem fullZeroForm_cosine_add_sine_eq_gammaBracket_add_criticalDeficit
    {F₀ : ℝ → ℝ} (hF₀ : ContDiff ℝ 2 F₀) (hF₀c : HasCompactSupport F₀)
    {A : ℝ} (hA : 0 ≤ A) (hsupp : ∀ x : ℝ, A < |x| → F₀ x = 0) (γ : ℝ) :
    fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ) =
      (Zeta23.EF.gammaBracket γ - 2) * (∫ x, F₀ x ^ 2) +
        archEnvelopeError F₀ γ +
        4 * horizonEnergy (cosineSource F₀ γ) + 4 * horizonEnergy (sineSource F₀ γ) +
        2 * ∫ t in Icc 0 (2 * A),
          ccmPrimeDeficitIncoming t *
            doubleGaugeDerivative
              (fun s => ArchimedeanAnomaly.autocorr F₀ s * Real.cos (γ * s)) t := by
  have hc : ContDiff ℝ 2 (cosineSource F₀ γ) := contDiff_cosineSource hF₀ γ
  have hs : ContDiff ℝ 2 (sineSource F₀ γ) := contDiff_sineSource hF₀ γ
  have hcc : HasCompactSupport (cosineSource F₀ γ) := hF₀c.mul_right
  have hsc : HasCompactSupport (sineSource F₀ γ) := hF₀c.mul_right
  have hsuppc : ∀ x : ℝ, A < |x| → cosineSource F₀ γ x = 0 := fun x hx => by
    simp [cosineSource, hsupp x hx]
  have hsupps : ∀ x : ℝ, A < |x| → sineSource F₀ γ x = 0 := fun x hx => by
    simp [sineSource, hsupp x hx]
  rw [fullZeroForm_eq_levy_add_horizon_add_criticalDeficit hc hcc hA hsuppc,
    fullZeroForm_eq_levy_add_horizon_add_criticalDeficit hs hsc hA hsupps]
  -- `L²` Pythagorean identity `(∫ cosSource²) + (∫ sinSource²) = ∫ F₀²`
  have hmass : (∫ x, cosineSource F₀ γ x ^ 2) + (∫ x, sineSource F₀ γ x ^ 2) = ∫ x, F₀ x ^ 2 := by
    have hic : Integrable fun x : ℝ => cosineSource F₀ γ x ^ 2 :=
      (hc.continuous.pow 2).integrable_of_hasCompactSupport
        ((hcc.comp_left (zero_pow two_ne_zero)))
    have his : Integrable fun x : ℝ => sineSource F₀ γ x ^ 2 :=
      (hs.continuous.pow 2).integrable_of_hasCompactSupport
        ((hsc.comp_left (zero_pow two_ne_zero)))
    rw [← integral_add hic his]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp [cosineSource, sineSource]
    linear_combination F₀ x ^ 2 * Real.cos_sq_add_sin_sq (γ * x)
  -- Archimedean Lévy energy sum
  have hlevy := biScaleLevyEnergy_cosine_sine_eq hF₀ hF₀c γ
  rw [RHTower.AutocorrelationKrein.autocorr_zero_eq F₀,
    archFrequencyCost_eq_gammaBracket_sub_zero γ] at hlevy
  -- Critical-deficit integral sum via linearity of `doubleGaugeDerivative`
  have hac_c : ContDiff ℝ 2 (ArchimedeanAnomaly.autocorr (cosineSource F₀ γ)) :=
    contDiff_autocorr hc hcc
  have hac_s : ContDiff ℝ 2 (ArchimedeanAnomaly.autocorr (sineSource F₀ γ)) :=
    contDiff_autocorr hs hsc
  have hint_c : IntegrableOn
      (fun t => ccmPrimeDeficitIncoming t *
        doubleGaugeDerivative (ArchimedeanAnomaly.autocorr (cosineSource F₀ γ)) t)
      (Icc 0 (2 * A)) :=
    (continuous_ccmPrimeDeficitIncoming.mul
      (continuous_doubleGaugeDerivative hac_c)).integrableOn_Icc
  have hint_s : IntegrableOn
      (fun t => ccmPrimeDeficitIncoming t *
        doubleGaugeDerivative (ArchimedeanAnomaly.autocorr (sineSource F₀ γ)) t)
      (Icc 0 (2 * A)) :=
    (continuous_ccmPrimeDeficitIncoming.mul
      (continuous_doubleGaugeDerivative hac_s)).integrableOn_Icc
  have hdef_sum :
      (∫ t in Icc 0 (2 * A), ccmPrimeDeficitIncoming t *
          doubleGaugeDerivative (ArchimedeanAnomaly.autocorr (cosineSource F₀ γ)) t) +
        (∫ t in Icc 0 (2 * A), ccmPrimeDeficitIncoming t *
          doubleGaugeDerivative (ArchimedeanAnomaly.autocorr (sineSource F₀ γ)) t) =
        ∫ t in Icc 0 (2 * A), ccmPrimeDeficitIncoming t *
          doubleGaugeDerivative
            (fun s => ArchimedeanAnomaly.autocorr F₀ s * Real.cos (γ * s)) t := by
    rw [← integral_add hint_c hint_s]
    refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
    have hac_eq : (fun s => ArchimedeanAnomaly.autocorr (cosineSource F₀ γ) s +
        ArchimedeanAnomaly.autocorr (sineSource F₀ γ) s) =
        fun s => ArchimedeanAnomaly.autocorr F₀ s * Real.cos (γ * s) :=
      funext (autocorr_cosineSource_add_sineSource hF₀.continuous hF₀c γ)
    rw [← mul_add, ← doubleGaugeDerivative_add hac_c hac_s t, hac_eq]
  linear_combination (Zeta23.EF.gammaBracket 0 - 2) * hmass + hlevy + 2 * hdef_sum

/-- **Castelnuovo–Severi Scaling-Subsurface Quadrature Defect Identity
(`scalingSubsurface_defect_cosine_add_sine_eq`):**
For any `F₀ ∈ realTestsAt r` (`0 ≤ r`) and any frequency `γ ∈ ℝ`, `cosineSource F₀ γ` and
`sineSource F₀ γ` belong to `realTestsAt r`, and the sum of their `scalingSubsurface` self-defects
satisfies the exact `gammaBracket γ - 2` + critical-deficit decomposition. -/
theorem cosineSource_mem_realTestsAt {r : ℝ} {F₀ : realTests} (hF₀ : F₀ ∈ realTestsAt r) (γ : ℝ) :
    (⟨cosineSource (F₀ : ℝ → ℝ) γ, contDiff_cosineSource F₀.2.1 γ, F₀.2.2.mul_right⟩ : realTests) ∈
      realTestsAt r := by
  intro x hx
  exact hF₀ (tsupport_mul_subset_left hx)

theorem sineSource_mem_realTestsAt {r : ℝ} {F₀ : realTests} (hF₀ : F₀ ∈ realTestsAt r) (γ : ℝ) :
    (⟨sineSource (F₀ : ℝ → ℝ) γ, contDiff_sineSource F₀.2.1 γ, F₀.2.2.mul_right⟩ : realTests) ∈
      realTestsAt r := by
  intro x hx
  exact hF₀ (tsupport_mul_subset_left hx)

theorem scalingSubsurface_defect_cosine_add_sine_eq
    {r : ℝ} (hr : 0 ≤ r) (F₀ : realTestsAt r) (a₁ b₁ a₂ b₂ γ : ℝ) :
    let Fc : realTestsAt r :=
      ⟨⟨cosineSource (F₀.1 : ℝ → ℝ) γ, contDiff_cosineSource F₀.1.2.1 γ, F₀.1.2.2.mul_right⟩,
        cosineSource_mem_realTestsAt F₀.2 γ⟩
    let Fs : realTestsAt r :=
      ⟨⟨sineSource (F₀.1 : ℝ → ℝ) γ, contDiff_sineSource F₀.1.2.1 γ, F₀.1.2.2.mul_right⟩,
        sineSource_mem_realTestsAt F₀.2 γ⟩
    (scalingSubsurface (realTestsAt r)).defect (a₁, b₁, Fc) (a₁, b₁, Fc) +
      (scalingSubsurface (realTestsAt r)).defect (a₂, b₂, Fs) (a₂, b₂, Fs) =
      (Zeta23.EF.gammaBracket γ - 2) * (∫ x, (F₀.1 : ℝ → ℝ) x ^ 2) +
        archEnvelopeError (F₀.1 : ℝ → ℝ) γ +
        4 * horizonEnergy (cosineSource (F₀.1 : ℝ → ℝ) γ) +
        4 * horizonEnergy (sineSource (F₀.1 : ℝ → ℝ) γ) +
        2 * ∫ t in Icc 0 (2 * r),
          ccmPrimeDeficitIncoming t *
            doubleGaugeDerivative
              (fun s => ArchimedeanAnomaly.autocorr (F₀.1 : ℝ → ℝ) s * Real.cos (γ * s)) t := by
  dsimp only
  have hsupp : ∀ u : ℝ, r < |u| → (F₀.1 : ℝ → ℝ) u = 0 := fun u hu =>
    image_eq_zero_of_notMem_tsupport fun hmem => not_le.mpr hu (abs_le.mpr (F₀.2 hmem))
  rw [scalingSubsurface_defect_self, scalingSubsurface_defect_self,
    weilPair_self_eq_fullZeroForm (contDiff_cosineSource F₀.1.2.1 γ) F₀.1.2.2.mul_right,
    weilPair_self_eq_fullZeroForm (contDiff_sineSource F₀.1.2.1 γ) F₀.1.2.2.mul_right]
  exact fullZeroForm_cosine_add_sine_eq_gammaBracket_add_criticalDeficit
    F₀.1.2.1 F₀.1.2.2 hr hsupp γ

/-! ## §2. Plancherel Off-Line Depth-Difference Majorant and Sub-Power Coercivity up to `(2/3) log Γ` -/

/-- `C²` norm of the unmodulated envelope `F₀` governing remote-ordinate Lorentzian tails. -/
def envelopeWindowNorm (F₀ : ℝ → ℝ) : ℝ :=
  (∫ u : ℝ, |F₀ u|) + ∫ u : ℝ, |deriv (deriv F₀) u|

theorem envelopeWindowNorm_nonneg (F₀ : ℝ → ℝ) : 0 ≤ envelopeWindowNorm F₀ :=
  add_nonneg (integral_nonneg fun _ => abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _)

/-- Exact complex decomposition `γ_ρ - ω = (Im ρ - ω) - (Re ρ - 1/2) * I`. -/
private theorem gammaOf_sub_real (ρ : ℂ) (ω : ℝ) :
    gammaOf ρ - (ω : ℂ) = ((ρ.im - ω : ℝ) : ℂ) - ((ρ.re - 1 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [gammaOf, Complex.div_I]
  apply Complex.ext <;> simp

private theorem conj_gammaOf_sub_real (ρ : ℂ) (ω : ℝ) :
    conj (gammaOf ρ) - (ω : ℂ) = ((ρ.im - ω : ℝ) : ℂ) + ((ρ.re - 1 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [gammaOf, Complex.div_I]
  apply Complex.ext <;> simp

/-- `paperFT` shift law for `complexModulatedSource F₀ γ`. -/
theorem paperFT_complexModulatedSource (F₀ : ℝ → ℝ) (γ : ℝ) (z : ℂ) :
    paperFT (complexModulatedSource F₀ γ) z = paperFT (fun u => (F₀ u : ℂ)) (z - (γ : ℂ)) := by
  unfold paperFT complexModulatedSource
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- `paperFT` two-shift law for `cosineSource F₀ γ`. -/
theorem paperFT_cosineSource {F₀ : ℝ → ℝ} (hF₀ : Continuous F₀)
    (hF₀c : HasCompactSupport F₀) (γ : ℝ) (z : ℂ) :
    paperFT (fun u => (cosineSource F₀ γ u : ℂ)) z =
      (paperFT (fun u => (F₀ u : ℂ)) (z - (γ : ℂ)) +
        paperFT (fun u => (F₀ u : ℂ)) (z + (γ : ℂ))) / 2 := by
  have hi1 : Integrable fun u : ℝ =>
      (F₀ u : ℂ) * Complex.exp (Complex.I * (z - (γ : ℂ)) * (u : ℂ)) :=
    ((Complex.continuous_ofReal.comp hF₀).mul (by fun_prop)).integrable_of_hasCompactSupport
      ((hF₀c.comp_left Complex.ofReal_zero).mul_right)
  have hi2 : Integrable fun u : ℝ =>
      (F₀ u : ℂ) * Complex.exp (Complex.I * (z + (γ : ℂ)) * (u : ℂ)) :=
    ((Complex.continuous_ofReal.comp hF₀).mul (by fun_prop)).integrable_of_hasCompactSupport
      ((hF₀c.comp_left Complex.ofReal_zero).mul_right)
  unfold paperFT cosineSource
  rw [← integral_add hi1 hi2, ← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  have h1 : Complex.I * z * (u : ℂ) + (-((γ * u : ℝ) : ℂ) * Complex.I) =
      Complex.I * (z - (γ : ℂ)) * (u : ℂ) := by push_cast; ring
  have h2 : Complex.I * z * (u : ℂ) + ((γ * u : ℝ) : ℂ) * Complex.I =
      Complex.I * (z + (γ : ℂ)) * (u : ℂ) := by push_cast; ring
  rw [← h1, ← h2, Complex.exp_add, Complex.exp_add]
  ring

/-- Two-integration-by-parts bound on `paperFT F₀_ℂ z` for symmetric support `[-A, A]`:
`‖paperFT F₀_ℂ z‖ ≤ e^{A |z.im|} * envelopeWindowNorm F₀ / (1 + z.re²)`. -/
theorem norm_paperFT_symm_le {F₀ : ℝ → ℝ} (hF₀ : ContDiff ℝ 2 F₀)
    (hF₀c : HasCompactSupport F₀) {A : ℝ} (_hA : 0 ≤ A)
    (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0) (z : ℂ) :
    ‖paperFT (fun u => (F₀ u : ℂ)) z‖ ≤
      Real.exp (A * |z.im|) * envelopeWindowNorm F₀ / (1 + z.re ^ 2) := by
  set g : ℝ → ℂ := fun u => (F₀ u : ℂ)
  have hg : ContDiff ℝ 2 g := Complex.ofRealCLM.contDiff.comp hF₀
  have hgc : HasCompactSupport g := hF₀c.comp_left Complex.ofReal_zero
  have h1 := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) F₀ from hF₀)
  have h2 := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (0 + 1) (deriv F₀) from h1.2.2)
  have hF''_cont : Continuous (deriv (deriv F₀)) := h2.2.2.continuous
  have hsupp'' : ∀ u : ℝ, A < |u| → deriv (deriv F₀) u = 0 := fun u hu => by
    rcases lt_abs.mp hu with hu1 | hu2
    · have heq : F₀ =ᶠ[𝓝 u] 0 := Filter.eventually_of_mem (Ioi_mem_nhds hu1) fun s hs =>
        hsupp s (lt_abs.mpr (Or.inl hs))
      exact ((heq.deriv).deriv).eq_of_nhds.trans (by simp)
    · have heq : F₀ =ᶠ[𝓝 u] 0 := Filter.eventually_of_mem (Iio_mem_nhds (by linarith : u < -A))
        fun s hs => hsupp s (lt_abs.mpr (Or.inr (by linarith [Set.mem_Iio.mp hs])))
      exact ((heq.deriv).deriv).eq_of_nhds.trans (by simp)
  have hexp_supp : ∀ u : ℝ, |u| ≤ A →
      ‖Complex.exp (Complex.I * z * (u : ℂ))‖ ≤ Real.exp (A * |z.im|) := fun u hu => by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (Complex.I * z * (u : ℂ)).re = -z.im * u := by simp [Complex.mul_re]
    rw [hre]
    calc -z.im * u ≤ |-z.im * u| := le_abs_self _
      _ = |z.im| * |u| := by rw [abs_mul, abs_neg]
      _ ≤ |z.im| * A := mul_le_mul_of_nonneg_left hu (abs_nonneg _)
      _ = A * |z.im| := by ring
  have he0 : ‖paperFT g z‖ ≤ Real.exp (A * |z.im|) * ∫ u, |F₀ u| := by
    unfold paperFT
    have hint : Integrable fun u : ℝ => |F₀ u| :=
      hF₀.continuous.abs.integrable_of_hasCompactSupport hF₀c.abs
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall fun u => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hu : |u| ≤ A
    · have := mul_le_mul_of_nonneg_left (hexp_supp u hu) (abs_nonneg (F₀ u))
      linarith
    · simp [hsupp u (not_le.mp hu)]
  have hg''_eq : deriv (deriv g) = fun u => ((deriv (deriv F₀) u : ℝ) : ℂ) := by
    have hd1 : deriv g = fun u => ((deriv F₀ u : ℝ) : ℂ) := by
      funext u
      exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u
        (h1.1 u).hasDerivAt).deriv
    rw [hd1]
    funext u
    exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u
      (h2.1 u).hasDerivAt).deriv
  have he2 : ‖paperFT (deriv (deriv g)) z‖ ≤ Real.exp (A * |z.im|) * ∫ u, |deriv (deriv F₀) u| := by
    unfold paperFT
    have hint : Integrable fun u : ℝ => |deriv (deriv F₀) u| :=
      hF''_cont.abs.integrable_of_hasCompactSupport hF₀c.deriv.deriv.abs
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall fun u => ?_)
    rw [hg''_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hu : |u| ≤ A
    · have := mul_le_mul_of_nonneg_left (hexp_supp u hu) (abs_nonneg (deriv (deriv F₀) u))
      linarith
    · simp [hsupp'' u (not_le.mp hu)]
  rw [EvenSector.paperFT_deriv_deriv_of_compact hg hgc z, norm_mul, norm_neg, norm_pow] at he2
  have hz_sq : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg z.im]
  rw [le_div_iff₀ (by positivity)]
  calc ‖paperFT g z‖ * (1 + z.re ^ 2)
      ≤ ‖paperFT g z‖ * (1 + ‖z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    _ = ‖paperFT g z‖ + ‖z‖ ^ 2 * ‖paperFT g z‖ := by ring
    _ ≤ Real.exp (A * |z.im|) * (∫ u, |F₀ u|) +
          Real.exp (A * |z.im|) * ∫ u, |deriv (deriv F₀) u| := add_le_add he0 he2
    _ = Real.exp (A * |z.im|) * envelopeWindowNorm F₀ := by unfold envelopeWindowNorm; ring

/-- Off-line depth-difference profile `h_diff F₀ ρ u = F₀(u)(e^{(Re ρ - 1/2)u} - e^{-(Re ρ - 1/2)u})e^{i Im ρ u}`
whose `paperFT` at `-ω` equals `paperFT F₀_ℂ (gammaOf ρ - ω) - paperFT F₀_ℂ (conj (gammaOf ρ) - ω)`. -/
def depthDiffProfile (F₀ : ℝ → ℝ) (ρ : ℂ) (u : ℝ) : ℂ :=
  ((F₀ u * (Real.exp ((ρ.re - 1 / 2) * u) - Real.exp (-((ρ.re - 1 / 2) * u))) : ℝ) : ℂ) *
    Complex.exp (Complex.I * (ρ.im : ℂ) * (u : ℂ))

theorem paperFT_depthDiffProfile_eq {F₀ : ℝ → ℝ} (hF₀ : Continuous F₀)
    (hF₀c : HasCompactSupport F₀) (ρ : ℂ) (ω : ℝ) :
    paperFT (depthDiffProfile F₀ ρ) (-(ω : ℂ)) =
      paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (ω : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (ω : ℂ)) := by
  have hi1 : Integrable fun u : ℝ =>
      (F₀ u : ℂ) * Complex.exp (Complex.I * (gammaOf ρ - (ω : ℂ)) * (u : ℂ)) :=
    ((Complex.continuous_ofReal.comp hF₀).mul (by fun_prop)).integrable_of_hasCompactSupport
      ((hF₀c.comp_left Complex.ofReal_zero).mul_right)
  have hi2 : Integrable fun u : ℝ =>
      (F₀ u : ℂ) * Complex.exp (Complex.I * (conj (gammaOf ρ) - (ω : ℂ)) * (u : ℂ)) :=
    ((Complex.continuous_ofReal.comp hF₀).mul (by fun_prop)).integrable_of_hasCompactSupport
      ((hF₀c.comp_left Complex.ofReal_zero).mul_right)
  unfold paperFT depthDiffProfile
  rw [← integral_sub hi1 hi2]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_exp, Complex.ofReal_exp]
  have h1 : Complex.exp (((ρ.re - 1 / 2) * u : ℝ) : ℂ) *
      Complex.exp (Complex.I * (ρ.im : ℂ) * (u : ℂ)) *
      Complex.exp (Complex.I * -(ω : ℂ) * (u : ℂ)) =
      Complex.exp (Complex.I * (gammaOf ρ - (ω : ℂ)) * (u : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, gammaOf_sub_real]
    congr 1; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have h2 : Complex.exp ((-((ρ.re - 1 / 2) * u) : ℝ) : ℂ) *
      Complex.exp (Complex.I * (ρ.im : ℂ) * (u : ℂ)) *
      Complex.exp (Complex.I * -(ω : ℂ) * (u : ℂ)) =
      Complex.exp (Complex.I * (conj (gammaOf ρ) - (ω : ℂ)) * (u : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, conj_gammaOf_sub_real]
    congr 1; push_cast; ring_nf; rw [Complex.I_sq]; ring
  calc (F₀ u : ℂ) *
        (Complex.exp (((ρ.re - 1 / 2) * u : ℝ) : ℂ) -
          Complex.exp ((-((ρ.re - 1 / 2) * u) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (ρ.im : ℂ) * (u : ℂ)) *
        Complex.exp (Complex.I * -(ω : ℂ) * (u : ℂ))
      = (F₀ u : ℂ) *
          (Complex.exp (((ρ.re - 1 / 2) * u : ℝ) : ℂ) *
            Complex.exp (Complex.I * (ρ.im : ℂ) * (u : ℂ)) *
            Complex.exp (Complex.I * -(ω : ℂ) * (u : ℂ))) -
        (F₀ u : ℂ) *
          (Complex.exp ((-((ρ.re - 1 / 2) * u) : ℝ) : ℂ) *
            Complex.exp (Complex.I * (ρ.im : ℂ) * (u : ℂ)) *
            Complex.exp (Complex.I * -(ω : ℂ) * (u : ℂ))) := by ring
    _ = (F₀ u : ℂ) * Complex.exp (Complex.I * (gammaOf ρ - (ω : ℂ)) * (u : ℂ)) -
        (F₀ u : ℂ) * Complex.exp (Complex.I * (conj (gammaOf ρ) - (ω : ℂ)) * (u : ℂ)) := by
          rw [h1, h2]

/-- Global and quadratic-near-line bounds on `(e^{δ u} - e^{-δ u})²` for `|u| ≤ A` (`0 ≤ A`). -/
theorem exp_sub_exp_neg_sq_le {A δ u : ℝ} (_hA : 0 ≤ A) (hu : |u| ≤ A) :
    (Real.exp (δ * u) - Real.exp (-(δ * u))) ^ 2 ≤ Real.exp (2 * A * |δ|) ∧
      (Real.exp (δ * u) - Real.exp (-(δ * u))) ^ 2 ≤
        4 * A ^ 2 * δ ^ 2 * Real.exp (2 * A * |δ|) := by
  set x : ℝ := |δ * u|
  have hx0 : 0 ≤ x := abs_nonneg _
  have hxr : x ≤ A * |δ| := by
    dsimp [x]; rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right hu (abs_nonneg _)
  have hsq_eq : (Real.exp (δ * u) - Real.exp (-(δ * u))) ^ 2 =
      (Real.exp x - Real.exp (-x)) ^ 2 := by
    dsimp [x]
    rcases le_total 0 (δ * u) with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h]; ring
  rw [hsq_eq]
  have hdiff_nn : 0 ≤ Real.exp x - Real.exp (-x) :=
    sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  have hdiff_le_exp : Real.exp x - Real.exp (-x) ≤ Real.exp (A * |δ|) := by
    have h1 : Real.exp x ≤ Real.exp (A * |δ|) := Real.exp_le_exp.mpr hxr
    linarith [Real.exp_pos (-x)]
  have hb1 : (Real.exp x - Real.exp (-x)) ^ 2 ≤ Real.exp (2 * A * |δ|) := by
    have hsq := pow_le_pow_left₀ hdiff_nn hdiff_le_exp 2
    refine hsq.trans_eq ?_
    rw [sq, ← Real.exp_add]; congr 1; ring
  -- Mean-value bound on `[-x, x]`: `e^x - e^{-x} ≤ 2 x e^x ≤ 2 A |δ| e^{A |δ|}`
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Real.exp) (f' := Real.exp) (s := Icc (-x) x) (x := -x) (y := x)
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    (fun t ht => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
      exact Real.exp_le_exp.mpr (ht.2.trans hxr))
    (convex_Icc (-x) x) ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hdiff_nn,
    abs_of_nonneg (by linarith : 0 ≤ x - -x), show x - -x = 2 * x by ring] at hmvt
  have hdiff_quad : Real.exp x - Real.exp (-x) ≤ 2 * A * |δ| * Real.exp (A * |δ|) :=
    hmvt.trans (by
      have := mul_le_mul_of_nonneg_left hxr (Real.exp_pos (A * |δ|)).le
      linarith)
  have hb2 : (Real.exp x - Real.exp (-x)) ^ 2 ≤ 4 * A ^ 2 * δ ^ 2 * Real.exp (2 * A * |δ|) := by
    have hsq := pow_le_pow_left₀ hdiff_nn hdiff_quad 2
    refine hsq.trans_eq ?_
    have hexp2 : Real.exp (A * |δ|) ^ 2 = Real.exp (2 * A * |δ|) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    calc (2 * A * |δ| * Real.exp (A * |δ|)) ^ 2
        = 4 * A ^ 2 * |δ| ^ 2 * Real.exp (A * |δ|) ^ 2 := by ring
      _ = 4 * A ^ 2 * δ ^ 2 * Real.exp (2 * A * |δ|) := by rw [sq_abs, hexp2]
  exact ⟨hb1, hb2⟩

private theorem integral_univ_norm_paperFT_depthDiff_sq_eq {F₀ : ℝ → ℝ} (hF₀ : Continuous F₀)
    (hF₀c : HasCompactSupport F₀) (ρ : ℂ) :
    Integrable (fun γ : ℝ =>
      ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (γ : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (γ : ℂ))‖ ^ 2) ∧
    (∫ γ : ℝ,
      ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (γ : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (γ : ℂ))‖ ^ 2) =
      2 * Real.pi * ∫ u : ℝ, ‖depthDiffProfile F₀ ρ u‖ ^ 2 := by
  let h := depthDiffProfile F₀ ρ
  have hh_cont : Continuous h := by unfold h depthDiffProfile; fun_prop
  have hh_comp : HasCompactSupport h := by
    unfold h depthDiffProfile
    exact ((hF₀c.mul_right).comp_left Complex.ofReal_zero).mul_right
  have hh1 : Integrable h := hh_cont.integrable_of_hasCompactSupport hh_comp
  have hint_h2 : Integrable fun u : ℝ => ‖h u‖ ^ 2 :=
    (hh_cont.norm.pow 2).integrable_of_hasCompactSupport
      ((hh_comp.norm).comp_left (zero_pow two_ne_zero))
  have hh2 : MemLp h 2 :=
    (memLp_two_iff_integrable_sq_norm hh_cont.aestronglyMeasurable).mpr hint_h2
  have hint_pos : Integrable fun x : ℝ => ‖paperFT h (x : ℂ)‖ ^ 2 := by
    have hfun : (fun x : ℝ => ‖paperFT h (x : ℂ)‖ ^ 2) =
        fun x => (fun ξ : ℝ => ‖FourierTransform.fourier h ξ‖ ^ 2) (x / (-(2 * Real.pi))) := by
      funext x; rw [paperFT_ofReal_eq_fourier, neg_div, ← div_neg]
    rw [hfun]
    exact (GaloisForLFunctions.RHTower.integrable_norm_sq_fourier hh1 hh2).comp_div
      (by linarith [Real.pi_pos])
  have heq_fn : (fun γ : ℝ =>
      ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (γ : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (γ : ℂ))‖ ^ 2) =
      fun γ : ℝ => ‖paperFT h ((-γ : ℝ) : ℂ)‖ ^ 2 := by
    funext γ
    rw [Complex.ofReal_neg, paperFT_depthDiffProfile_eq hF₀ hF₀c ρ γ]
  refine ⟨by rw [heq_fn]; exact hint_pos.comp_neg, ?_⟩
  rw [heq_fn, integral_neg_eq_self (fun x : ℝ => ‖paperFT h (x : ℂ)‖ ^ 2)]
  exact RHTower.KernelStrip.integral_norm_sq_paperFT_of_memLp hh1 hh2

private theorem integral_norm_depthDiffProfile_sq_bounds {F₀ : ℝ → ℝ} (hF₀ : Continuous F₀)
    (hF₀c : HasCompactSupport F₀) {A : ℝ} (hA : 0 ≤ A)
    (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0) (ρ : ℂ) :
    (∫ u : ℝ, ‖depthDiffProfile F₀ ρ u‖ ^ 2) ≤
      Real.exp (2 * A * |ρ.re - 1 / 2|) * (∫ u, F₀ u ^ 2) ∧
    (∫ u : ℝ, ‖depthDiffProfile F₀ ρ u‖ ^ 2) ≤
      4 * A ^ 2 * (ρ.re - 1 / 2) ^ 2 * Real.exp (2 * A * |ρ.re - 1 / 2|) * (∫ u, F₀ u ^ 2) := by
  have hh_cont : Continuous (depthDiffProfile F₀ ρ) := by unfold depthDiffProfile; fun_prop
  have hh_comp : HasCompactSupport (depthDiffProfile F₀ ρ) := by
    unfold depthDiffProfile
    exact ((hF₀c.mul_right).comp_left Complex.ofReal_zero).mul_right
  have hint_h2 : Integrable fun u : ℝ => ‖depthDiffProfile F₀ ρ u‖ ^ 2 :=
    (hh_cont.norm.pow 2).integrable_of_hasCompactSupport
      ((hh_comp.norm).comp_left (zero_pow two_ne_zero))
  have hint_F₀2 : Integrable fun u : ℝ => F₀ u ^ 2 :=
    (hF₀.pow 2).integrable_of_hasCompactSupport (hF₀c.comp_left (zero_pow two_ne_zero))
  have hnorm_h : ∀ u : ℝ, ‖depthDiffProfile F₀ ρ u‖ ^ 2 =
      F₀ u ^ 2 * (Real.exp ((ρ.re - 1 / 2) * u) - Real.exp (-((ρ.re - 1 / 2) * u))) ^ 2 := fun u => by
    dsimp [depthDiffProfile]
    have hexp_norm : ‖Complex.exp (Complex.I * (ρ.im : ℂ) * (u : ℂ))‖ = 1 := by
      have : Complex.I * (ρ.im : ℂ) * (u : ℂ) = ((ρ.im * u : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, hexp_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
  clear hh_cont hh_comp
  refine ⟨?_, ?_⟩
  · rw [← integral_const_mul]
    refine integral_mono hint_h2
      (hint_F₀2.const_mul (Real.exp (2 * A * |ρ.re - 1 / 2|))) fun u => ?_
    rw [hnorm_h u]
    by_cases hu : |u| ≤ A
    · have hb := (exp_sub_exp_neg_sq_le hA hu (δ := ρ.re - 1 / 2)).1
      exact (mul_le_mul_of_nonneg_left hb (sq_nonneg (F₀ u))).trans_eq (mul_comm _ _)
    · rw [hsupp u (not_le.mp hu)]
      simp only [sq, zero_mul, mul_zero, le_refl]
  · rw [← integral_const_mul]
    refine integral_mono hint_h2
      (hint_F₀2.const_mul (4 * A ^ 2 * (ρ.re - 1 / 2) ^ 2 * Real.exp (2 * A * |ρ.re - 1 / 2|)))
      fun u => ?_
    rw [hnorm_h u]
    by_cases hu : |u| ≤ A
    · have hb := (exp_sub_exp_neg_sq_le hA hu (δ := ρ.re - 1 / 2)).2
      exact (mul_le_mul_of_nonneg_left hb (sq_nonneg (F₀ u))).trans_eq (mul_comm _ _)
    · rw [hsupp u (not_le.mp hu)]
      simp only [sq, zero_mul, mul_zero, le_refl]

/-- Plancherel `L²(ℝ)` bound for the depth-difference transform across BOTH sign orientations `±γ`:
no `H¹` derivative loss enters, and the bound vanishes on `Re ρ = 1/2`. -/
theorem integral_norm_paperFT_depthDiff_sq_le {F₀ : ℝ → ℝ} (hF₀ : Continuous F₀)
    (hF₀c : HasCompactSupport F₀) {A : ℝ} (hA : 0 ≤ A)
    (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0) (ρ : ℂ) (a b : ℝ) :
    Integrable (fun γ : ℝ =>
      ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (γ : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (γ : ℂ))‖ ^ 2) ∧
    (∫ γ in Icc a b,
      ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (γ : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (γ : ℂ))‖ ^ 2) ≤
      2 * Real.pi * Real.exp (2 * A * |ρ.re - 1 / 2|) * (∫ u, F₀ u ^ 2) ∧
    (∫ γ in Icc a b,
      ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (γ : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (γ : ℂ))‖ ^ 2) ≤
      8 * Real.pi * A ^ 2 * (ρ.re - 1 / 2) ^ 2 * Real.exp (2 * A * |ρ.re - 1 / 2|) *
        (∫ u, F₀ u ^ 2) := by
  obtain ⟨hint_lhs, hwhole⟩ := integral_univ_norm_paperFT_depthDiff_sq_eq hF₀ hF₀c ρ
  obtain ⟨hu_b1, hu_b2⟩ := integral_norm_depthDiffProfile_sq_bounds hF₀ hF₀c hA hsupp ρ
  have hset_le : (∫ γ in Icc a b,
      ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (γ : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (γ : ℂ))‖ ^ 2) ≤
      2 * Real.pi * ∫ u : ℝ, ‖depthDiffProfile F₀ ρ u‖ ^ 2 :=
    (setIntegral_le_integral hint_lhs (Eventually.of_forall fun _ => sq_nonneg _)).trans_eq hwhole
  exact ⟨hint_lhs,
    hset_le.trans ((mul_le_mul_of_nonneg_left hu_b1 (by positivity)).trans_eq (by ring)),
    hset_le.trans ((mul_le_mul_of_nonneg_left hu_b2 (by positivity)).trans_eq (by ring))⟩

/-- Symmetric `+γ` orientation of `integral_norm_paperFT_depthDiff_sq_le` via `γ ↦ -γ`. -/
theorem integral_norm_paperFT_depthDiff_add_sq_le {F₀ : ℝ → ℝ} (hF₀ : Continuous F₀)
    (hF₀c : HasCompactSupport F₀) {A : ℝ} (hA : 0 ≤ A)
    (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0) (ρ : ℂ) (a b : ℝ) :
    (∫ γ in Icc a b,
      ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ + (γ : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) + (γ : ℂ))‖ ^ 2) ≤
      2 * Real.pi * Real.exp (2 * A * |ρ.re - 1 / 2|) * (∫ u, F₀ u ^ 2) ∧
    (∫ γ in Icc a b,
      ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ + (γ : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) + (γ : ℂ))‖ ^ 2) ≤
      8 * Real.pi * A ^ 2 * (ρ.re - 1 / 2) ^ 2 * Real.exp (2 * A * |ρ.re - 1 / 2|) *
        (∫ u, F₀ u ^ 2) := by
  obtain ⟨hint, hwhole_eq⟩ := integral_univ_norm_paperFT_depthDiff_sq_eq hF₀ hF₀c ρ
  obtain ⟨hu_b1, hu_b2⟩ := integral_norm_depthDiffProfile_sq_bounds hF₀ hF₀c hA hsupp ρ
  have hset_le : (∫ γ in Icc a b,
      ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ + (γ : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) + (γ : ℂ))‖ ^ 2) ≤
      2 * Real.pi * ∫ u : ℝ, ‖depthDiffProfile F₀ ρ u‖ ^ 2 := by
    have heq : (fun γ : ℝ =>
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ + (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) + (γ : ℂ))‖ ^ 2) =
        fun γ : ℝ =>
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - ((-γ : ℝ) : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - ((-γ : ℝ) : ℂ))‖ ^ 2 := by
      funext γ; simp [sub_neg_eq_add]
    rw [heq]
    exact ((setIntegral_le_integral (s := Icc a b) hint.comp_neg
      (Eventually.of_forall fun _ => sq_nonneg _)).trans_eq
      (integral_neg_eq_self (fun x : ℝ =>
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (x : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (x : ℂ))‖ ^ 2) volume)).trans_eq
      hwhole_eq
  exact ⟨hset_le.trans ((mul_le_mul_of_nonneg_left hu_b1 (by positivity)).trans_eq (by ring)),
    hset_le.trans ((mul_le_mul_of_nonneg_left hu_b2 (by positivity)).trans_eq (by ring))⟩

/-- Exact multiplicity-preserving `tsum` bridge between `XiZeroCopy` and `zetaZeroConfig.carrier`. -/
theorem summable_zetaCarrier_of_xiZeroCopy {g : ℂ → ℝ} (hg0 : ∀ z, 0 ≤ g z)
    (hg : Summable fun q : XiZeroCopy => g (q.1 : ℂ)) :
    Summable fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.mult ρ : ℝ) * g (ρ : ℂ) := by
  rw [← xiDivisorZetaCarrierEquiv.summable_iff]
  set f : XiZeroCopy → ℝ≥0 := fun q => ⟨g (q.1 : ℂ), hg0 _⟩
  have hf : Summable f := NNReal.summable_coe.mp hg
  have hsig : Summable fun ρ : XiDivisorSupport => ∑' i, f ⟨ρ, i⟩ := (NNReal.summable_sigma.mp hf).2
  have hsigR : Summable fun ρ : XiDivisorSupport => ((∑' i, f ⟨ρ, i⟩ : ℝ≥0) : ℝ) :=
    NNReal.summable_coe.mpr hsig
  refine hsigR.congr fun ρ => ?_
  have hconst : ∀ i, ((f ⟨ρ, i⟩ : ℝ≥0) : ℝ) = g (ρ : ℂ) := fun _ => rfl
  rw [Function.comp_apply, tsum_fintype, NNReal.coe_sum,
    Finset.sum_congr rfl (fun i _ => hconst i)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    xiDivisorZetaCarrierEquiv_multiplicity]
  rfl

theorem tsum_xiZeroCopy_eq_zetaCarrier {g : ℂ → ℝ}
    (hg : Summable fun q : XiZeroCopy => g (q.1 : ℂ)) :
    (∑' q : XiZeroCopy, g (q.1 : ℂ)) =
      ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * g (ρ : ℂ) := by
  rw [hg.tsum_sigma, ← xiDivisorZetaCarrierEquiv.tsum_eq
    (fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.mult ρ : ℝ) * g (ρ : ℂ))]
  refine tsum_congr fun ρ => ?_
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, xiDivisorZetaCarrierEquiv_multiplicity]
  rfl

/-- `1 / (1 + z.im²) ≤ 2 / ‖z‖²` for every `z` in the critical strip `0 ≤ z.re ≤ 1`. -/
private theorem inv_one_add_im_sq_le_two_div_norm_sq {z : ℂ}
    (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    1 / (1 + z.im ^ 2) ≤ 2 / ‖z‖ ^ 2 := by
  have hznorm : 0 < ‖z‖ ^ 2 := by
    rw [Complex.sq_norm]
    exact Complex.normSq_pos.mpr fun h => by rw [h, Complex.zero_re] at hz0; linarith
  rw [div_le_div_iff₀ (by positivity) hznorm, Complex.sq_norm, Complex.normSq_apply]
  have hre : z.re * z.re ≤ 1 := by nlinarith
  nlinarith [sq_nonneg z.im]

/-- Continuity of `γ ↦ fullZeroForm (cosineSource F₀ γ)` and `γ ↦ fullZeroForm (sineSource F₀ γ)`. -/
theorem continuous_zeta_W_re_modulated {F₀ : ℝ → ℝ} (hF₀ : ContDiff ℝ 2 F₀)
    (hF₀c : HasCompactSupport F₀) :
    Continuous (fun γ : ℝ =>
      (zetaZeroConfig.W (complexModulatedSource F₀ γ) (complexModulatedSource F₀ γ)).re) ∧
    Continuous (fun γ : ℝ => fullZeroForm (cosineSource F₀ γ)) := by
  -- Compact-support bound `|u| ≤ R₀`
  obtain ⟨R₀, hR₀⟩ := Metric.isBounded_iff_subset_closedBall (0 : ℝ) |>.mp hF₀c.isCompact.isBounded
  set A₀ : ℝ := max 1 R₀
  have hA₀ : 0 ≤ A₀ := by positivity
  have hsupp₀ : ∀ u : ℝ, A₀ < |u| → F₀ u = 0 := fun u hu => by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have hball := hR₀ hmem
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hball
    linarith [le_max_right (1 : ℝ) R₀]
  have hbd_pt : ∀ z : ℂ, |z.im| ≤ 1 / 2 →
      ‖paperFT (fun u => (F₀ u : ℂ)) z‖ ≤
        Real.exp (A₀ / 2) * envelopeWindowNorm F₀ / (1 + z.re ^ 2) := fun z hz => by
    refine (norm_paperFT_symm_le hF₀ hF₀c hA₀ hsupp₀ z).trans ?_
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith))
        (envelopeWindowNorm_nonneg F₀)) (by positivity)
  have hft_cont : Continuous (fun z : ℂ => paperFT (fun u => (F₀ u : ℂ)) z) := by
    -- Parametric continuity on compact support `[-A₀, A₀]`
    have hint_F₀ : Integrable fun u : ℝ => |F₀ u| :=
      hF₀.continuous.abs.integrable_of_hasCompactSupport hF₀c.abs
    rw [continuous_iff_continuousAt]
    intro z₀
    refine continuousAt_of_dominated
      (bound := fun u : ℝ => |F₀ u| * Real.exp (A₀ * (|z₀.im| + 1)))
      (Eventually.of_forall fun z =>
        (((Complex.continuous_ofReal.comp hF₀.continuous).mul (by fun_prop)).aestronglyMeasurable))
      ?_ (hint_F₀.mul_const _)
      (Eventually.of_forall fun u => by fun_prop)
    filter_upwards [Metric.ball_mem_nhds z₀ zero_lt_one] with z hz
    refine Eventually.of_forall fun u => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hu : |u| ≤ A₀
    · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have hz_im : |z.im| ≤ |z₀.im| + 1 := by
        have hd : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using hz
        have him := (Complex.abs_im_le_norm (z - z₀)).trans hd.le
        simp only [Complex.sub_im] at him
        linarith [abs_sub_abs_le_abs_sub z.im z₀.im]
      have hre : (Complex.I * z * (u : ℂ)).re = -z.im * u := by simp [Complex.mul_re]
      rw [hre]
      calc -z.im * u ≤ |-z.im * u| := le_abs_self _
        _ = |z.im| * |u| := by rw [abs_mul, abs_neg]
        _ ≤ (|z₀.im| + 1) * A₀ := mul_le_mul hz_im hu (abs_nonneg _) (by positivity)
        _ = A₀ * (|z₀.im| + 1) := by ring
    · simp [hsupp₀ u (not_le.mp hu)]
  -- Uniform domination on every `closedBall (0 : ℝ) M`
  have hcont_tsum : ∀ (Φ : ℝ → zetaZeroConfig.carrier → ℂ),
      (∀ ρ, Continuous fun γ : ℝ => Φ γ ρ) →
      (∀ M : ℝ, 0 ≤ M → ∃ K : ℝ, 0 ≤ K ∧ ∀ γ : ℝ, |γ| ≤ M → ∀ ρ : zetaZeroConfig.carrier,
        ‖Φ γ ρ‖ ≤ K * ((zetaZeroConfig.mult ρ : ℝ) * (1 / ‖(ρ : ℂ)‖ ^ 2))) →
      Continuous (fun γ : ℝ => (∑' ρ : zetaZeroConfig.carrier, Φ γ ρ).re) := by
    intro Φ hΦ_cont hΦ_dom
    refine Complex.continuous_re.comp (continuous_iff_continuousAt.mpr fun γ₀ => ?_)
    set M : ℝ := |γ₀| + 1
    obtain ⟨K, _hK, hdom⟩ := hΦ_dom M (by positivity)
    have hsum_base : Summable fun ρ : zetaZeroConfig.carrier =>
        K * ((zetaZeroConfig.mult ρ : ℝ) * (1 / ‖(ρ : ℂ)‖ ^ 2)) :=
      (summable_zetaCarrier_of_xiZeroCopy (g := fun z : ℂ => 1 / ‖z‖ ^ 2) (fun _ => by positivity)
        summable_inv_norm_sq_xiZeroCopy).mul_left K
    have hcont_on : ContinuousOn (fun γ : ℝ => ∑' ρ, Φ γ ρ) (Metric.closedBall 0 M) :=
      continuousOn_tsum (fun ρ => (hΦ_cont ρ).continuousOn) hsum_base fun ρ γ hγ =>
        hdom γ (by simpa [Metric.mem_closedBall, Real.dist_eq] using hγ) ρ
    exact hcont_on.continuousAt (Metric.closedBall_mem_nhds_of_mem (by simp [M]))
  have hdom_shift : ∀ M : ℝ, 0 ≤ M → ∀ γ : ℝ, |γ| ≤ M → ∀ ρ : zetaZeroConfig.carrier,
      ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ))‖ ≤
        Real.exp (A₀ / 2) * envelopeWindowNorm F₀ * (2 * (1 + M) ^ 2) *
          (2 / ‖(ρ : ℂ)‖ ^ 2) ∧
      ‖paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ≤
        Real.exp (A₀ / 2) * envelopeWindowNorm F₀ * 1 := by
    intro M hM γ hγ ρ
    have hρ := ρ.2
    have him1 : |(gammaOf (ρ : ℂ) - (γ : ℂ)).im| ≤ 1 / 2 := by
      rw [gammaOf_sub_real]; simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_sub, abs_neg]
      exact abs_le.mpr ⟨by linarith [hρ.2.1], by linarith [hρ.2.2]⟩
    have him2 : |(conj (gammaOf (ρ : ℂ)) - (γ : ℂ)).im| ≤ 1 / 2 := by
      rw [conj_gammaOf_sub_real]; simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
      exact abs_le.mpr ⟨by linarith [hρ.2.1], by linarith [hρ.2.2]⟩
    have hre1 : (gammaOf (ρ : ℂ) - (γ : ℂ)).re = (ρ : ℂ).im - γ := by
      rw [gammaOf_sub_real]; simp
    have hpeano : 1 + (ρ : ℂ).im ^ 2 ≤ 2 * (1 + M) ^ 2 * (1 + ((ρ : ℂ).im - γ) ^ 2) := by
      have ht : (ρ : ℂ).im ^ 2 ≤ 2 * ((ρ : ℂ).im - γ) ^ 2 + 2 * γ ^ 2 := by
        nlinarith [sq_nonneg (((ρ : ℂ).im - γ) - γ)]
      have hγ2 : γ ^ 2 ≤ M ^ 2 := by
        have := pow_le_pow_left₀ (abs_nonneg γ) hγ 2; rwa [sq_abs] at this
      nlinarith [sq_nonneg ((ρ : ℂ).im - γ), sq_nonneg M]
    have hinv_peano : 1 / (1 + ((ρ : ℂ).im - γ) ^ 2) ≤
        2 * (1 + M) ^ 2 * (1 / (1 + (ρ : ℂ).im ^ 2)) := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hb1 := hbd_pt _ him1
    rw [hre1] at hb1
    have hb2 := (hbd_pt _ him2).trans
      (div_le_self (mul_nonneg (Real.exp_pos _).le (envelopeWindowNorm_nonneg F₀))
        (by linarith [sq_nonneg (conj (gammaOf (ρ : ℂ)) - (γ : ℂ)).re]))
    refine ⟨?_, by simpa using hb2⟩
    calc ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ))‖
        ≤ Real.exp (A₀ / 2) * envelopeWindowNorm F₀ * (1 / (1 + ((ρ : ℂ).im - γ) ^ 2)) := by
          rw [mul_one_div]; exact hb1
      _ ≤ Real.exp (A₀ / 2) * envelopeWindowNorm F₀ *
            (2 * (1 + M) ^ 2 * (2 / ‖(ρ : ℂ)‖ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (Real.exp_pos _).le (envelopeWindowNorm_nonneg F₀))
          exact hinv_peano.trans (mul_le_mul_of_nonneg_left
            (inv_one_add_im_sq_le_two_div_norm_sq hρ.2.1 hρ.2.2) (by positivity))
      _ = Real.exp (A₀ / 2) * envelopeWindowNorm F₀ * (2 * (1 + M) ^ 2) *
            (2 / ‖(ρ : ℂ)‖ ^ 2) := by ring
  set C₀_w : ℝ := Real.exp (A₀ / 2) * envelopeWindowNorm F₀
  have hC₀_w_nn : 0 ≤ C₀_w := mul_nonneg (Real.exp_pos _).le (envelopeWindowNorm_nonneg F₀)
  refine ⟨?_, ?_⟩
  · -- Continuity of complex quadrature Weil form
    refine hcont_tsum (fun γ ρ =>
      zetaZeroConfig.Wsummand (complexModulatedSource F₀ γ) (complexModulatedSource F₀ γ) ρ)
      (fun ρ => ?_) (fun M hM => ?_)
    · simp only [ZeroConfig.Wsummand, paperFT_complexModulatedSource]
      fun_prop
    · refine ⟨4 * C₀_w ^ 2 * (1 + M) ^ 2, by positivity, fun γ hγ ρ => ?_⟩
      obtain ⟨hs1, hs2⟩ := hdom_shift M hM γ hγ ρ
      simp only [ZeroConfig.Wsummand, paperFT_complexModulatedSource, norm_mul,
        Complex.norm_natCast, Complex.norm_conj]
      have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
      have hprod := mul_le_mul hs1 hs2 (norm_nonneg _)
        (mul_nonneg (mul_nonneg hC₀_w_nn (by positivity)) (by positivity))
      calc (zetaZeroConfig.mult ρ : ℝ) *
            ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ))‖ *
              ‖paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖
          = (zetaZeroConfig.mult ρ : ℝ) *
              (‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ))‖ *
                ‖paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖) := by ring
        _ ≤ (zetaZeroConfig.mult ρ : ℝ) *
              ((C₀_w * (2 * (1 + M) ^ 2) * (2 / ‖(ρ : ℂ)‖ ^ 2)) * (C₀_w * 1)) :=
            mul_le_mul_of_nonneg_left hprod hm
        _ = 4 * C₀_w ^ 2 * (1 + M) ^ 2 * ((zetaZeroConfig.mult ρ : ℝ) * (1 / ‖(ρ : ℂ)‖ ^ 2)) := by
            ring
  · -- Continuity of `fullZeroForm (cosineSource F₀ γ)`
    have heq_cos : (fun γ : ℝ => fullZeroForm (cosineSource F₀ γ)) = fun γ : ℝ =>
        (zetaZeroConfig.W (fun u => (cosineSource F₀ γ u : ℂ))
          (fun u => (cosineSource F₀ γ u : ℂ))).re := by
      funext γ
      exact fullZeroForm_eq_zeta_W_re (contDiff_cosineSource hF₀ γ) hF₀c.mul_right
    rw [heq_cos]
    refine hcont_tsum (fun γ ρ =>
      zetaZeroConfig.Wsummand (fun u => (cosineSource F₀ γ u : ℂ))
        (fun u => (cosineSource F₀ γ u : ℂ)) ρ)
      (fun ρ => ?_) (fun M hM => ?_)
    · simp only [ZeroConfig.Wsummand, paperFT_cosineSource hF₀.continuous hF₀c]
      fun_prop
    · refine ⟨4 * C₀_w ^ 2 * (1 + M) ^ 2, by positivity, fun γ hγ ρ => ?_⟩
      obtain ⟨hp1, hp2⟩ := hdom_shift M hM γ hγ ρ
      obtain ⟨hm1, hm2⟩ := hdom_shift M hM (-γ) (by simpa using hγ) ρ
      simp only [Complex.ofReal_neg, sub_neg_eq_add] at hm1 hm2
      simp only [ZeroConfig.Wsummand, paperFT_cosineSource hF₀.continuous hF₀c, norm_mul,
        Complex.norm_natCast, Complex.norm_conj]
      have ha : ‖(paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) +
          paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ))) / 2‖ ≤
          C₀_w * (2 * (1 + M) ^ 2) * (2 / ‖(ρ : ℂ)‖ ^ 2) := by
        rw [norm_div, Complex.norm_ofNat]
        linarith [norm_add_le
          (paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)))
          (paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ)))]
      have hb : ‖(paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ)) +
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))) / 2‖ ≤ C₀_w := by
        rw [norm_div, Complex.norm_ofNat]
        linarith [norm_add_le
          (paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ)))
          (paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ)))]
      have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
      have hprod := mul_le_mul ha hb (norm_nonneg _)
        (mul_nonneg (mul_nonneg hC₀_w_nn (by positivity)) (by positivity))
      calc (zetaZeroConfig.mult ρ : ℝ) *
            ‖(paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) +
                paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ))) / 2‖ *
              ‖(paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ)) +
                paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))) / 2‖
          = (zetaZeroConfig.mult ρ : ℝ) *
              (‖(paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) +
                  paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ))) / 2‖ *
                ‖(paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ)) +
                  paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))) / 2‖) := by ring
        _ ≤ (zetaZeroConfig.mult ρ : ℝ) *
              ((C₀_w * (2 * (1 + M) ^ 2) * (2 / ‖(ρ : ℂ)‖ ^ 2)) * C₀_w) :=
            mul_le_mul_of_nonneg_left hprod hm
        _ = 4 * C₀_w ^ 2 * (1 + M) ^ 2 * ((zetaZeroConfig.mult ρ : ℝ) * (1 / ‖(ρ : ℂ)‖ ^ 2)) := by
            ring

private theorem integral_tsum_nonneg_Icc {ι : Type*} [Countable ι]
    {a b : ℝ} {f : ι → ℝ → ℝ}
    (hf_cont : ∀ i, Continuous (f i))
    (hf_nn : ∀ i γ, 0 ≤ f i γ)
    {u : ι → ℝ} (hu_sum : Summable u)
    (hf_dom : ∀ i γ, γ ∈ Icc a b → f i γ ≤ u i) :
    ContinuousOn (fun γ => ∑' i, f i γ) (Icc a b) ∧
      (∫ γ in Icc a b, ∑' i, f i γ) = ∑' i, ∫ γ in Icc a b, f i γ := by
  have hc : ContinuousOn (fun γ => ∑' i, f i γ) (Icc a b) :=
    continuousOn_tsum (fun i => (hf_cont i).continuousOn) hu_sum fun i γ hγ => by
      rw [Real.norm_of_nonneg (hf_nn i γ)]; exact hf_dom i γ hγ
  refine ⟨hc, ?_⟩
  apply MeasureTheory.integral_tsum
  · exact fun i => (hf_cont i).integrableOn_Icc.aestronglyMeasurable
  · have hi (i : ι) :
        (∫⁻ γ in Icc a b, ‖f i γ‖ₑ) = ‖∫ γ in Icc a b, ‖f i γ‖‖ₑ := by
      dsimp only [enorm]
      rw [lintegral_coe_eq_integral _ (hf_cont i).integrableOn_Icc.norm, ENNReal.coe_nnreal_eq,
        coe_nnnorm, Real.norm_of_nonneg (integral_nonneg fun γ => norm_nonneg (f i γ))]
      simp only [coe_nnnorm]
    rw [funext hi]
    have hsum_int : Summable fun i => ∫ γ in Icc a b, ‖f i γ‖ := by
      refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun _ => norm_nonneg _)
        (fun i => ?_) (hu_sum.mul_left (max 0 (b - a)))
      by_cases hab : a ≤ b
      · calc (∫ γ in Icc a b, ‖f i γ‖)
            ≤ ∫ _γ in Icc a b, u i :=
              setIntegral_mono_on (hf_cont i).norm.integrableOn_Icc
                continuous_const.integrableOn_Icc measurableSet_Icc fun γ hγ => by
                  rw [Real.norm_of_nonneg (hf_nn i γ)]; exact hf_dom i γ hγ
          _ = (b - a) * u i := by
              rw [setIntegral_const, Measure.real, Real.volume_Icc,
                ENNReal.toReal_ofReal (sub_nonneg.mpr hab), smul_eq_mul]
          _ = max 0 (b - a) * u i := by rw [max_eq_right (sub_nonneg.mpr hab)]
      · rw [Set.Icc_eq_empty hab, setIntegral_empty, max_eq_left (by linarith), zero_mul]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hsum_int.abs)

private theorem continuous_paperFT_ofReal {F₀ : ℝ → ℝ} (hF₀ : Continuous F₀)
    (hF₀c : HasCompactSupport F₀) {A : ℝ} (_hA : 0 ≤ A) (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0) :
    Continuous (fun z : ℂ => paperFT (fun u => (F₀ u : ℂ)) z) := by
  have hint_F₀ : Integrable fun u : ℝ => |F₀ u| :=
    hF₀.abs.integrable_of_hasCompactSupport hF₀c.abs
  rw [continuous_iff_continuousAt]
  intro z₀
  refine continuousAt_of_dominated
    (bound := fun u : ℝ => |F₀ u| * Real.exp (A * (|z₀.im| + 1)))
    (Eventually.of_forall fun z =>
      (((Complex.continuous_ofReal.comp hF₀).mul (by fun_prop)).aestronglyMeasurable))
    ?_ (hint_F₀.mul_const _) (Eventually.of_forall fun u => by fun_prop)
  filter_upwards [Metric.ball_mem_nhds z₀ zero_lt_one] with z hz
  refine Eventually.of_forall fun u => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases hu : |u| ≤ A
  · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr
    have hz_im : |z.im| ≤ |z₀.im| + 1 := by
      have hd : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using hz
      have him := (Complex.abs_im_le_norm (z - z₀)).trans hd.le
      simp only [Complex.sub_im] at him
      linarith [abs_sub_abs_le_abs_sub z.im z₀.im]
    have hre : (Complex.I * z * (u : ℂ)).re = -z.im * u := by simp [Complex.mul_re]
    rw [hre]
    calc -z.im * u ≤ |-z.im * u| := le_abs_self _
      _ = |z.im| * |u| := by rw [abs_mul, abs_neg]
      _ ≤ (|z₀.im| + 1) * A := mul_le_mul hz_im hu (abs_nonneg _) (by positivity)
      _ = A * (|z₀.im| + 1) := by ring
  · rw [hsupp u (not_le.mp hu)]
    simp only [abs_zero, zero_mul, le_refl]

private theorem norm_paperFT_depthDiff_div_four_le_lorentz {F₀ : ℝ → ℝ}
    (hF₀ : ContDiff ℝ 2 F₀) (hF₀c : HasCompactSupport F₀)
    {A : ℝ} (hA : 0 ≤ A) (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0)
    (z : ℂ) (ω : ℝ) (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf z - (ω : ℂ)) -
      paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf z) - (ω : ℂ))‖ ^ 2 / 4 ≤
      Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / (1 + (z.im - ω) ^ 2) ^ 2) := by
  have him1 : |(gammaOf z - (ω : ℂ)).im| ≤ 1 / 2 := by
    rw [gammaOf_sub_real]; simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_sub, abs_neg]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have him2 : |(conj (gammaOf z) - (ω : ℂ)).im| ≤ 1 / 2 := by
    rw [conj_gammaOf_sub_real]; simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hre1 : (gammaOf z - (ω : ℂ)).re = z.im - ω := by rw [gammaOf_sub_real]; simp
  have hre2 : (conj (gammaOf z) - (ω : ℂ)).re = z.im - ω := by rw [conj_gammaOf_sub_real]; simp
  have hb1 := norm_paperFT_symm_le hF₀ hF₀c hA hsupp (gammaOf z - (ω : ℂ))
  have hb2 := norm_paperFT_symm_le hF₀ hF₀c hA hsupp (conj (gammaOf z) - (ω : ℂ))
  rw [hre1] at hb1; rw [hre2] at hb2
  have hexp1 : Real.exp (A * |(gammaOf z - (ω : ℂ)).im|) ≤ Real.exp (A / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hexp2 : Real.exp (A * |(conj (gammaOf z) - (ω : ℂ)).im|) ≤ Real.exp (A / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have htri : ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf z - (ω : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf z) - (ω : ℂ))‖ ≤
      2 * Real.exp (A / 2) * envelopeWindowNorm F₀ / (1 + (z.im - ω) ^ 2) := by
    calc ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf z - (ω : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf z) - (ω : ℂ))‖
        ≤ ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf z - (ω : ℂ))‖ +
            ‖paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf z) - (ω : ℂ))‖ := norm_sub_le _ _
      _ ≤ Real.exp (A / 2) * envelopeWindowNorm F₀ / (1 + (z.im - ω) ^ 2) +
            Real.exp (A / 2) * envelopeWindowNorm F₀ / (1 + (z.im - ω) ^ 2) := by
          refine add_le_add ?_ ?_
          · exact hb1.trans (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hexp1 (envelopeWindowNorm_nonneg F₀)) (by positivity))
          · exact hb2.trans (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hexp2 (envelopeWindowNorm_nonneg F₀)) (by positivity))
      _ = 2 * Real.exp (A / 2) * envelopeWindowNorm F₀ / (1 + (z.im - ω) ^ 2) := by ring
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hexpA : Real.exp (A / 2) ^ 2 = Real.exp A := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hden_ne : 1 + (z.im - ω) ^ 2 ≠ 0 := by positivity
  calc ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf z - (ω : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf z) - (ω : ℂ))‖ ^ 2 / 4
      ≤ (2 * Real.exp (A / 2) * envelopeWindowNorm F₀ / (1 + (z.im - ω) ^ 2)) ^ 2 / 4 :=
        div_le_div_of_nonneg_right hsq (by norm_num)
    _ = Real.exp (A / 2) ^ 2 * envelopeWindowNorm F₀ ^ 2 * (1 / (1 + (z.im - ω) ^ 2) ^ 2) := by
        field_simp [hden_ne]; ring
    _ = Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / (1 + (z.im - ω) ^ 2) ^ 2) := by
        rw [hexpA]

private theorem conj_paperFT_ofReal_eq {F₀ : ℝ → ℝ} (hF₀ : Continuous F₀)
    (hF₀c : HasCompactSupport F₀) (w : ℂ) :
    conj (paperFT (fun u => (F₀ u : ℂ)) w) = paperFT (fun u => (F₀ u : ℂ)) (-conj w) := by
  unfold paperFT
  dsimp only
  have hint : Integrable fun u : ℝ => (F₀ u : ℂ) * Complex.exp (Complex.I * w * (u : ℂ)) :=
    ((Complex.continuous_ofReal.comp hF₀).mul
      (by fun_prop)).integrable_of_hasCompactSupport
      ((hF₀c.comp_left Complex.ofReal_zero).mul_right)
  rw [← Complex.conjCLE_apply]
  refine (Complex.conjCLE.integral_comp_comm hint).symm.trans
    (integral_congr_ae (Eventually.of_forall fun u => ?_))
  simp only [Complex.conjCLE_apply, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp

private theorem summable_and_swap_depthDiff_Icc {F₀ : ℝ → ℝ}
    (hF₀ : ContDiff ℝ 2 F₀) (hF₀c : HasCompactSupport F₀)
    {Γ A : ℝ} (_hΓ : 1 ≤ Γ) (hA : 0 ≤ A) (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0) :
    (∀ ω : ℝ, Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (ω : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (ω : ℂ))‖ ^ 2 / 4) ∧
    (∀ ω : ℝ, |ω| ≤ 2 * Γ → ∀ ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (ω : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (ω : ℂ))‖ ^ 2 / 4 ≤
        Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 * (1 + 2 * Γ) ^ 2) *
          ((zetaZeroConfig.mult ρ : ℝ) * (1 / ‖(ρ : ℂ)‖ ^ 2))) ∧
    ContinuousOn (fun γ : ℝ => ∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4)
      (Icc Γ (2 * Γ)) ∧
    (∫ γ in Icc Γ (2 * Γ), ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) =
      (∑' ρ : zetaZeroConfig.carrier, ∫ γ in Icc Γ (2 * Γ),
        (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) ∧
    ContinuousOn (fun γ : ℝ => ∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))‖ ^ 2 / 4)
      (Icc Γ (2 * Γ)) ∧
    (∫ γ in Icc Γ (2 * Γ), ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))‖ ^ 2 / 4) =
      (∑' ρ : zetaZeroConfig.carrier, ∫ γ in Icc Γ (2 * Γ),
        (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))‖ ^ 2 / 4) := by
  have hft_cont := continuous_paperFT_ofReal hF₀.continuous hF₀c hA hsupp
  have hsum_ω : ∀ ω : ℝ, Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (ω : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (ω : ℂ))‖ ^ 2 / 4 := by
    intro ω
    have hpeano_ω : ∀ z : ℂ, 0 < z.re → z.re < 1 →
        1 / (1 + (z.im - ω) ^ 2) ^ 2 ≤ 4 * (1 + |ω|) ^ 2 * (1 / ‖z‖ ^ 2) := fun z hz0 hz1 => by
      have ht : 1 + z.im ^ 2 ≤ 2 * (1 + |ω|) ^ 2 * (1 + (z.im - ω) ^ 2) := by
        have h1 : z.im ^ 2 ≤ 2 * (z.im - ω) ^ 2 + 2 * ω ^ 2 := by
          nlinarith [sq_nonneg ((z.im - ω) - ω)]
        have h2 : ω ^ 2 = |ω| ^ 2 := (sq_abs ω).symm
        nlinarith [sq_nonneg (z.im - ω), abs_nonneg ω]
      have hinv1 : 1 / (1 + (z.im - ω) ^ 2) ≤ 2 * (1 + |ω|) ^ 2 * (1 / (1 + z.im ^ 2)) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      have hinv2 : 1 / (1 + (z.im - ω) ^ 2) ≤ 1 :=
        div_le_one_of_le₀ (by linarith [sq_nonneg (z.im - ω)]) (by positivity)
      calc 1 / (1 + (z.im - ω) ^ 2) ^ 2
          = (1 / (1 + (z.im - ω) ^ 2)) * (1 / (1 + (z.im - ω) ^ 2)) := by simp [sq]
        _ ≤ (2 * (1 + |ω|) ^ 2 * (2 / ‖z‖ ^ 2)) * 1 := by
            refine mul_le_mul ?_ hinv2 (by positivity) (by positivity)
            exact hinv1.trans (mul_le_mul_of_nonneg_left
              (inv_one_add_im_sq_le_two_div_norm_sq hz0 hz1) (by positivity))
        _ = 4 * (1 + |ω|) ^ 2 * (1 / ‖z‖ ^ 2) := by ring
    let K_ω : ℝ := Real.exp A * envelopeWindowNorm F₀ ^ 2 * (4 * (1 + |ω|) ^ 2)
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun ρ => ?_)
      ((summable_zetaCarrier_of_xiZeroCopy (g := fun z : ℂ => 1 / ‖z‖ ^ 2)
        (fun _ => by positivity) summable_inv_norm_sq_xiZeroCopy).mul_left K_ω)
    have hρ := ρ.2
    have h1 := (norm_paperFT_depthDiff_div_four_le_lorentz hF₀ hF₀c hA hsupp (ρ : ℂ) ω hρ.2.1 hρ.2.2).trans
      (mul_le_mul_of_nonneg_left (hpeano_ω (ρ : ℂ) hρ.2.1 hρ.2.2) (by positivity))
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    calc (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (ω : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (ω : ℂ))‖ ^ 2 / 4
        = (zetaZeroConfig.mult ρ : ℝ) *
            (‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (ω : ℂ)) -
              paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (ω : ℂ))‖ ^ 2 / 4) := by ring
      _ ≤ (zetaZeroConfig.mult ρ : ℝ) *
            (Real.exp A * envelopeWindowNorm F₀ ^ 2 *
              (4 * (1 + |ω|) ^ 2 * (1 / ‖(ρ : ℂ)‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left h1 hm
      _ = K_ω * ((zetaZeroConfig.mult ρ : ℝ) * (1 / ‖(ρ : ℂ)‖ ^ 2)) := by dsimp [K_ω]; ring
  let u_dom : zetaZeroConfig.carrier → ℝ := fun ρ =>
    Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 * (1 + 2 * Γ) ^ 2) *
      ((zetaZeroConfig.mult ρ : ℝ) * (1 / ‖(ρ : ℂ)‖ ^ 2))
  have hu_dom_sum : Summable u_dom :=
    (summable_zetaCarrier_of_xiZeroCopy (g := fun z : ℂ => 1 / ‖z‖ ^ 2) (fun _ => by positivity)
      summable_inv_norm_sq_xiZeroCopy).mul_left _
  have hdom_Icc : ∀ ω : ℝ, |ω| ≤ 2 * Γ → ∀ ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (ω : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (ω : ℂ))‖ ^ 2 / 4 ≤ u_dom ρ := by
    intro ω hω ρ
    have hρ := ρ.2
    have ht : 1 + (ρ : ℂ).im ^ 2 ≤ 2 * (1 + 2 * Γ) ^ 2 * (1 + ((ρ : ℂ).im - ω) ^ 2) := by
      have h1 : (ρ : ℂ).im ^ 2 ≤ 2 * ((ρ : ℂ).im - ω) ^ 2 + 2 * ω ^ 2 := by
        nlinarith [sq_nonneg (((ρ : ℂ).im - ω) - ω)]
      have h2 : ω ^ 2 ≤ (2 * Γ) ^ 2 := by
        have := pow_le_pow_left₀ (abs_nonneg ω) hω 2; rwa [sq_abs] at this
      nlinarith [sq_nonneg ((ρ : ℂ).im - ω)]
    have hinv1 : 1 / (1 + ((ρ : ℂ).im - ω) ^ 2) ≤
        2 * (1 + 2 * Γ) ^ 2 * (1 / (1 + (ρ : ℂ).im ^ 2)) := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    have hinv2 : 1 / (1 + ((ρ : ℂ).im - ω) ^ 2) ≤ 1 :=
      div_le_one_of_le₀ (by linarith [sq_nonneg ((ρ : ℂ).im - ω)]) (by positivity)
    have hlor2 : 1 / (1 + ((ρ : ℂ).im - ω) ^ 2) ^ 2 ≤
        4 * (1 + 2 * Γ) ^ 2 * (1 / ‖(ρ : ℂ)‖ ^ 2) := by
      calc 1 / (1 + ((ρ : ℂ).im - ω) ^ 2) ^ 2
          = (1 / (1 + ((ρ : ℂ).im - ω) ^ 2)) * (1 / (1 + ((ρ : ℂ).im - ω) ^ 2)) := by simp [sq]
        _ ≤ (2 * (1 + 2 * Γ) ^ 2 * (2 / ‖(ρ : ℂ)‖ ^ 2)) * 1 := by
            refine mul_le_mul ?_ hinv2 (by positivity) (by positivity)
            exact hinv1.trans (mul_le_mul_of_nonneg_left
              (inv_one_add_im_sq_le_two_div_norm_sq hρ.2.1 hρ.2.2) (by positivity))
        _ = 4 * (1 + 2 * Γ) ^ 2 * (1 / ‖(ρ : ℂ)‖ ^ 2) := by ring
    have h1 := (norm_paperFT_depthDiff_div_four_le_lorentz hF₀ hF₀c hA hsupp (ρ : ℂ) ω hρ.2.1 hρ.2.2).trans
      (mul_le_mul_of_nonneg_left hlor2 (by positivity))
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    calc (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (ω : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (ω : ℂ))‖ ^ 2 / 4
        = (zetaZeroConfig.mult ρ : ℝ) *
            (‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (ω : ℂ)) -
              paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (ω : ℂ))‖ ^ 2 / 4) := by ring
      _ ≤ (zetaZeroConfig.mult ρ : ℝ) *
            (Real.exp A * envelopeWindowNorm F₀ ^ 2 *
              (4 * (1 + 2 * Γ) ^ 2 * (1 / ‖(ρ : ℂ)‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left h1 hm
      _ = 4 * (Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 + 2 * Γ) ^ 2 *
            ((zetaZeroConfig.mult ρ : ℝ) * (1 / ‖(ρ : ℂ)‖ ^ 2))) := by ring
      _ ≤ u_dom ρ := by
          have hu_eq : u_dom ρ = 16 * (Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 + 2 * Γ) ^ 2 *
              ((zetaZeroConfig.mult ρ : ℝ) * (1 / ‖(ρ : ℂ)‖ ^ 2))) := by dsimp [u_dom]; ring
          have hnn : 0 ≤ Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 + 2 * Γ) ^ 2 *
              ((zetaZeroConfig.mult ρ : ℝ) * (1 / ‖(ρ : ℂ)‖ ^ 2)) := by positivity
          linarith
  haveI : Countable zetaZeroConfig.carrier :=
    Countable.of_equiv XiDivisorSupport xiDivisorZetaCarrierEquiv
  have hd_sub_cont : ∀ ρ : zetaZeroConfig.carrier, Continuous fun γ : ℝ =>
      (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4 :=
    fun _ => by fun_prop
  have hd_add_cont : ∀ ρ : zetaZeroConfig.carrier, Continuous fun γ : ℝ =>
      (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))‖ ^ 2 / 4 :=
    fun _ => by fun_prop
  obtain ⟨hc_sub, hswap_sub⟩ := integral_tsum_nonneg_Icc (a := Γ) (b := 2 * Γ) hd_sub_cont
    (fun _ _ => by positivity) hu_dom_sum
    (fun ρ γ hγ => hdom_Icc γ (abs_le.mpr ⟨by linarith [hγ.1], hγ.2⟩) ρ)
  obtain ⟨hc_add, hswap_add⟩ := integral_tsum_nonneg_Icc (a := Γ) (b := 2 * Γ) hd_add_cont
    (fun _ _ => by positivity) hu_dom_sum
    (fun ρ γ hγ => by
      simpa [sub_neg_eq_add] using
        hdom_Icc (-γ) (by rw [abs_neg]; exact abs_le.mpr ⟨by linarith [hγ.1], hγ.2⟩) ρ)
  exact ⟨hsum_ω, hdom_Icc, hc_sub, hswap_sub, hc_add, hswap_add⟩

/-- Master bound on the `Icc Γ (2 * Γ)` integral of the single-shift depth-difference series
`Σ_ρ m_ρ ‖paperFT F₀_ℂ (γ_ρ ∓ γ) - paperFT F₀_ℂ (conj γ_ρ ∓ γ)‖² / 4`, shared by §2, §3, and §4. -/
theorem integral_Icc_tsum_depthDiff_div_four_le {F₀ : ℝ → ℝ}
    (hF₀ : ContDiff ℝ 2 F₀) (hF₀c : HasCompactSupport F₀)
    {Γ A : ℝ} (hΓ : 1 ≤ Γ) (hA : 0 ≤ A) (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0) :
    (∀ γ : ℝ, Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) ∧
    (∀ γ : ℝ, Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))‖ ^ 2 / 4) ∧
    ContinuousOn (fun γ : ℝ => ∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4)
      (Icc Γ (2 * Γ)) ∧
    ContinuousOn (fun γ : ℝ => ∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))‖ ^ 2 / 4)
      (Icc Γ (2 * Γ)) ∧
    ∃ G_loc : Finset XiZeroCopy,
      (∀ q ∈ G_loc, Γ / 2 ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 4 * Γ) ∧
      (∫ γ in Icc Γ (2 * Γ), ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) ≤
        (∑ q ∈ G_loc,
          (∫ γ in Icc Γ (2 * Γ),
            ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
              paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2) / 4) +
          (32 * reciprocalSquareWeightTotal / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 ∧
      (∫ γ in Icc Γ (2 * Γ), ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))‖ ^ 2 / 4) ≤
        (∑ q ∈ G_loc,
          (∫ γ in Icc Γ (2 * Γ),
            ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) + (γ : ℂ)) -
              paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) + (γ : ℂ))‖ ^ 2) / 4) +
          (32 * reciprocalSquareWeightTotal / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 := by
  classical
  obtain ⟨hsum_ω, hdom_Icc, hc_sub, hswap_sub, hc_add, hswap_add⟩ :=
    summable_and_swap_depthDiff_Icc hF₀ hF₀c hΓ hA hsupp
  have hft_cont := continuous_paperFT_ofReal hF₀.continuous hF₀c hA hsupp
  have hS_fin : ({q : XiZeroCopy | Γ / 2 ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 4 * Γ}).Finite :=
    (finite_xiOrdinateWindow (4 * Γ) 0).subset fun q hq => by
      rw [mem_xiOrdinateWindow_iff, sub_zero]; exact hq.2
  obtain ⟨G_loc, hmem_Gloc⟩ : ∃ G_loc : Finset XiZeroCopy,
      ∀ q : XiZeroCopy, q ∈ G_loc ↔ Γ / 2 ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 4 * Γ :=
    ⟨hS_fin.toFinset, fun _ => hS_fin.mem_toFinset⟩
  have hΓ0 : 0 < Γ := by linarith
  have hcont_q_sub : ∀ z : ℂ, Continuous fun γ : ℝ =>
      ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf z - (γ : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf z) - (γ : ℂ))‖ ^ 2 / 4 :=
    fun _ => by fun_prop
  have hcont_q_add : ∀ z : ℂ, Continuous fun γ : ℝ =>
      ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf z + (γ : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf z) + (γ : ℂ))‖ ^ 2 / 4 :=
    fun _ => by fun_prop
  set g_sub : ℂ → ℝ := fun z =>
    (∫ γ in Icc Γ (2 * Γ),
      ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf z - (γ : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf z) - (γ : ℂ))‖ ^ 2) / 4
  set g_add : ℂ → ℝ := fun z =>
    (∫ γ in Icc Γ (2 * Γ),
      ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf z + (γ : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf z) + (γ : ℂ))‖ ^ 2) / 4
  have hg_sub_xi_sum : Summable fun q : XiZeroCopy => g_sub (q.1 : ℂ) := by
    refine Summable.of_nonneg_of_le
      (fun _ => div_nonneg (integral_nonneg fun _ => sq_nonneg _) (by norm_num))
      (fun q => ?_)
      (summable_inv_norm_sq_xiZeroCopy.mul_left
        (Γ * (Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 * (1 + 2 * Γ) ^ 2))))
    set ρ_c : zetaZeroConfig.carrier := xiDivisorZetaCarrierEquiv q.1
    have hpt_q : ∀ γ ∈ Icc Γ (2 * Γ),
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2 / 4 ≤
          Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 * (1 + 2 * Γ) ^ 2) *
            (1 / ‖(q.1 : ℂ)‖ ^ 2) := fun γ hγ => by
      have hm1 : 1 ≤ (zetaZeroConfig.mult ρ_c : ℝ) := by
        exact_mod_cast zetaZeroConfig.one_le_mult (ρ_c : ℂ) ρ_c.2
      have hd := hdom_Icc γ (abs_le.mpr ⟨by linarith [hγ.1], hγ.2⟩) ρ_c
      have hrc : (ρ_c : ℂ) = (q.1 : ℂ) := rfl
      rw [hrc] at hd
      have hm_pos : 0 < (zetaZeroConfig.mult ρ_c : ℝ) := by linarith
      have hd' : (zetaZeroConfig.mult ρ_c : ℝ) *
          (‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) ≤
          (zetaZeroConfig.mult ρ_c : ℝ) *
            (Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 * (1 + 2 * Γ) ^ 2) *
              (1 / ‖(q.1 : ℂ)‖ ^ 2)) := by
        calc (zetaZeroConfig.mult ρ_c : ℝ) *
              (‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
                paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2 / 4)
            = (zetaZeroConfig.mult ρ_c : ℝ) *
                ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
                  paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2 / 4 := by ring
          _ ≤ Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 * (1 + 2 * Γ) ^ 2) *
                ((zetaZeroConfig.mult ρ_c : ℝ) * (1 / ‖(q.1 : ℂ)‖ ^ 2)) := hd
          _ = (zetaZeroConfig.mult ρ_c : ℝ) *
                (Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 * (1 + 2 * Γ) ^ 2) *
                  (1 / ‖(q.1 : ℂ)‖ ^ 2)) := by ring
      exact le_of_mul_le_mul_left hd' hm_pos
    have hdiv_int : g_sub (q.1 : ℂ) = ∫ γ in Icc Γ (2 * Γ),
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2 / 4 :=
      (integral_div 4 _).symm
    rw [hdiv_int]
    calc (∫ γ in Icc Γ (2 * Γ),
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2 / 4)
        ≤ ∫ _γ in Icc Γ (2 * Γ),
            Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 * (1 + 2 * Γ) ^ 2) *
              (1 / ‖(q.1 : ℂ)‖ ^ 2) :=
          setIntegral_mono_on (hcont_q_sub _).integrableOn_Icc
            continuous_const.integrableOn_Icc measurableSet_Icc hpt_q
      _ = Γ * (Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 * (1 + 2 * Γ) ^ 2)) *
            (1 / ‖(q.1 : ℂ)‖ ^ 2) := by
          rw [setIntegral_const, Measure.real, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * Γ - Γ),
            show 2 * Γ - Γ = Γ by ring, smul_eq_mul]; ring
  have hg_add_xi_sum : Summable fun q : XiZeroCopy => g_add (q.1 : ℂ) := by
    have hrefl : (fun q : XiZeroCopy => g_add (q.1 : ℂ)) =
        fun q : XiZeroCopy => g_sub ((xiZeroCopyConjEquiv q).1 : ℂ) := by
      funext q
      have hcq : ((xiZeroCopyConjEquiv q).1 : ℂ) = conj (q.1 : ℂ) := rfl
      dsimp [g_add, g_sub]
      congr 1
      refine setIntegral_congr_fun measurableSet_Icc fun γ _ => ?_
      rw [hcq]
      have hz1 : -conj (gammaOf (conj (q.1 : ℂ)) - (γ : ℂ)) = gammaOf (q.1 : ℂ) + (γ : ℂ) := by
        simp only [gammaOf, Complex.div_I]; apply Complex.ext <;> simp <;> ring
      have hz2 : -conj (conj (gammaOf (conj (q.1 : ℂ))) - (γ : ℂ)) = conj (gammaOf (q.1 : ℂ)) + (γ : ℂ) := by
        simp only [gammaOf, Complex.div_I]; apply Complex.ext <;> simp <;> ring
      have hnorm_eq : ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (conj (q.1 : ℂ)) - (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (conj (q.1 : ℂ))) - (γ : ℂ))‖ =
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) + (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) + (γ : ℂ))‖ := by
        rw [← Complex.norm_conj
          (paperFT (fun u => (F₀ u : ℂ)) (gammaOf (conj (q.1 : ℂ)) - (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (conj (q.1 : ℂ))) - (γ : ℂ))),
          map_sub, conj_paperFT_ofReal_eq hF₀.continuous hF₀c,
          conj_paperFT_ofReal_eq hF₀.continuous hF₀c, hz1, hz2]
      rw [hnorm_eq]
    rw [hrefl]
    exact xiZeroCopyConjEquiv.summable_iff.mpr hg_sub_xi_sum
  have hbound_xi : ∀ (g_fn : ℂ → ℝ),
      Summable (fun q : XiZeroCopy => g_fn (q.1 : ℂ)) →
      (∀ q : XiZeroCopy, 0 ≤ g_fn (q.1 : ℂ)) →
      (∀ q : XiZeroCopy, (|(q.1 : ℂ).im| < Γ / 2 ∨ 4 * Γ < |(q.1 : ℂ).im|) →
        g_fn (q.1 : ℂ) ≤ (32 / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 *
          (1 / ‖(q.1 : ℂ)‖ ^ 2)) →
      (∑' q : XiZeroCopy, g_fn (q.1 : ℂ)) ≤
        (∑ q ∈ G_loc, g_fn (q.1 : ℂ)) +
          (32 * reciprocalSquareWeightTotal / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 := by
    intro g_fn hg_sum _hg_nn hg_rem
    set v_loc : XiZeroCopy → ℝ := fun q => if q ∈ G_loc then g_fn (q.1 : ℂ) else 0
    set v_rem : XiZeroCopy → ℝ := fun q =>
      (32 / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / ‖(q.1 : ℂ)‖ ^ 2)
    have hv_loc : Summable v_loc := summable_of_ne_finset_zero (s := G_loc) fun q hq => if_neg hq
    have hv_rem : Summable v_rem := summable_inv_norm_sq_xiZeroCopy.mul_left _
    have hle_pt : ∀ q : XiZeroCopy, g_fn (q.1 : ℂ) ≤ v_loc q + v_rem q := fun q => by
      by_cases hq : q ∈ G_loc
      · dsimp [v_loc, v_rem]; rw [if_pos hq]; linarith [show 0 ≤ (32 / Γ) * Real.exp A *
          envelopeWindowNorm F₀ ^ 2 * (1 / ‖(q.1 : ℂ)‖ ^ 2) by positivity]
      · dsimp [v_loc]; rw [if_neg hq, zero_add]
        have hnot : |(q.1 : ℂ).im| < Γ / 2 ∨ 4 * Γ < |(q.1 : ℂ).im| := by
          rw [hmem_Gloc, not_and_or] at hq
          rcases hq with h1 | h2
          · exact Or.inl (not_le.mp h1)
          · exact Or.inr (not_le.mp h2)
        exact hg_rem q hnot
    calc (∑' q : XiZeroCopy, g_fn (q.1 : ℂ))
        ≤ (∑' q, v_loc q) + ∑' q, v_rem q :=
          (hg_sum.tsum_le_tsum hle_pt (hv_loc.add hv_rem)).trans_eq (hv_loc.tsum_add hv_rem)
      _ = (∑ q ∈ G_loc, g_fn (q.1 : ℂ)) +
            (32 * reciprocalSquareWeightTotal / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 := by
          congr 1
          · rw [tsum_eq_sum (s := G_loc) (fun q hq => if_neg hq)]
            exact Finset.sum_congr rfl fun q hq => if_pos hq
          · unfold reciprocalSquareWeightTotal
            dsimp only [v_rem]
            rw [tsum_mul_left]; ring
  have hG : Γ * (32 / Γ ^ 2) = 32 / Γ := by
    rw [mul_div_assoc', div_eq_div_iff (pow_ne_zero 2 hΓ0.ne') hΓ0.ne']; ring
  have hg_sub_rem : ∀ q : XiZeroCopy, (|(q.1 : ℂ).im| < Γ / 2 ∨ 4 * Γ < |(q.1 : ℂ).im|) →
      g_sub (q.1 : ℂ) ≤ (32 / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 *
        (1 / ‖(q.1 : ℂ)‖ ^ 2) := fun q hq => by
    have hdiv_int : g_sub (q.1 : ℂ) = ∫ γ in Icc Γ (2 * Γ),
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2 / 4 :=
      (integral_div 4 _).symm
    rw [hdiv_int]
    have hpt : ∀ γ ∈ Icc Γ (2 * Γ),
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2 / 4 ≤
          (32 / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / ‖(q.1 : ℂ)‖ ^ 2) :=
      fun γ hγ => by
        have h1 := norm_paperFT_depthDiff_div_four_le_lorentz hF₀ hF₀c hA hsupp
          (q.1 : ℂ) γ (xiZeroCopy_re_pos q) (xiZeroCopy_re_lt_one q)
        have h2 := (inv_one_add_sq_remote_le hΓ hγ.1 hγ.2 hq).2
        have h3 := inv_one_add_im_sq_le_two_div_norm_sq (xiZeroCopy_re_pos q) (xiZeroCopy_re_lt_one q)
        calc ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
              paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2 / 4
            ≤ Real.exp A * envelopeWindowNorm F₀ ^ 2 *
                ((16 / Γ ^ 2) * (2 / ‖(q.1 : ℂ)‖ ^ 2)) :=
              h1.trans (mul_le_mul_of_nonneg_left
                (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))) (by positivity))
          _ = (32 / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / ‖(q.1 : ℂ)‖ ^ 2) := by
              ring
    calc (∫ γ in Icc Γ (2 * Γ),
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2 / 4)
        ≤ ∫ _γ in Icc Γ (2 * Γ),
            (32 / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / ‖(q.1 : ℂ)‖ ^ 2) :=
          setIntegral_mono_on (hcont_q_sub _).integrableOn_Icc
            continuous_const.integrableOn_Icc measurableSet_Icc hpt
      _ = (Γ * (32 / Γ ^ 2)) *
            (Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / ‖(q.1 : ℂ)‖ ^ 2)) := by
          rw [setIntegral_const, Measure.real, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * Γ - Γ),
            show 2 * Γ - Γ = Γ by ring, smul_eq_mul]; ring
      _ = (32 / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / ‖(q.1 : ℂ)‖ ^ 2) := by
          rw [hG]; ring
  have hg_add_rem : ∀ q : XiZeroCopy, (|(q.1 : ℂ).im| < Γ / 2 ∨ 4 * Γ < |(q.1 : ℂ).im|) →
      g_add (q.1 : ℂ) ≤ (32 / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 *
        (1 / ‖(q.1 : ℂ)‖ ^ 2) := fun q hq => by
    have hdiv_int : g_add (q.1 : ℂ) = ∫ γ in Icc Γ (2 * Γ),
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) + (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) + (γ : ℂ))‖ ^ 2 / 4 :=
      (integral_div 4 _).symm
    rw [hdiv_int]
    have hpt : ∀ γ ∈ Icc Γ (2 * Γ),
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) + (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) + (γ : ℂ))‖ ^ 2 / 4 ≤
          (32 / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / ‖(q.1 : ℂ)‖ ^ 2) :=
      fun γ hγ => by
        have h1 : ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) + (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) + (γ : ℂ))‖ ^ 2 / 4 ≤
            Real.exp A * envelopeWindowNorm F₀ ^ 2 *
              (1 / (1 + ((q.1 : ℂ).im + γ) ^ 2) ^ 2) := by
          simpa [sub_neg_eq_add] using norm_paperFT_depthDiff_div_four_le_lorentz hF₀ hF₀c hA hsupp
            (q.1 : ℂ) (-γ) (xiZeroCopy_re_pos q) (xiZeroCopy_re_lt_one q)
        have h2 := (inv_one_add_sq_remote_add_le hΓ hγ.1 hγ.2 hq).2
        have h3 := inv_one_add_im_sq_le_two_div_norm_sq (xiZeroCopy_re_pos q) (xiZeroCopy_re_lt_one q)
        calc ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) + (γ : ℂ)) -
              paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) + (γ : ℂ))‖ ^ 2 / 4
            ≤ Real.exp A * envelopeWindowNorm F₀ ^ 2 *
                ((16 / Γ ^ 2) * (2 / ‖(q.1 : ℂ)‖ ^ 2)) :=
              h1.trans (mul_le_mul_of_nonneg_left
                (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))) (by positivity))
          _ = (32 / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / ‖(q.1 : ℂ)‖ ^ 2) := by
              ring
    calc (∫ γ in Icc Γ (2 * Γ),
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) + (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) + (γ : ℂ))‖ ^ 2 / 4)
        ≤ ∫ _γ in Icc Γ (2 * Γ),
            (32 / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / ‖(q.1 : ℂ)‖ ^ 2) :=
          setIntegral_mono_on (hcont_q_add _).integrableOn_Icc
            continuous_const.integrableOn_Icc measurableSet_Icc hpt
      _ = (Γ * (32 / Γ ^ 2)) *
            (Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / ‖(q.1 : ℂ)‖ ^ 2)) := by
          rw [setIntegral_const, Measure.real, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * Γ - Γ),
            show 2 * Γ - Γ = Γ by ring, smul_eq_mul]; ring
      _ = (32 / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / ‖(q.1 : ℂ)‖ ^ 2) := by
          rw [hG]; ring
  have htsum_sub_eq : (∑' ρ : zetaZeroConfig.carrier, ∫ γ in Icc Γ (2 * Γ),
        (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) =
      ∑' q : XiZeroCopy, g_sub (q.1 : ℂ) := by
    rw [tsum_xiZeroCopy_eq_zetaCarrier (g := g_sub) hg_sub_xi_sum]
    refine tsum_congr fun ρ => ?_
    dsimp [g_sub]
    rw [integral_div, integral_const_mul, mul_div_assoc]
  have htsum_add_eq : (∑' ρ : zetaZeroConfig.carrier, ∫ γ in Icc Γ (2 * Γ),
        (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))‖ ^ 2 / 4) =
      ∑' q : XiZeroCopy, g_add (q.1 : ℂ) := by
    rw [tsum_xiZeroCopy_eq_zetaCarrier (g := g_add) hg_add_xi_sum]
    refine tsum_congr fun ρ => ?_
    dsimp [g_add]
    rw [integral_div, integral_const_mul, mul_div_assoc]
  refine ⟨fun γ => hsum_ω γ, fun γ => by simpa [sub_neg_eq_add] using hsum_ω (-γ),
    hc_sub, hc_add, G_loc, fun q hq => (hmem_Gloc q).mp hq, ?_, ?_⟩
  · rw [hswap_sub, htsum_sub_eq]
    exact hbound_xi g_sub hg_sub_xi_sum
      (fun _ => div_nonneg (integral_nonneg fun _ => sq_nonneg _) (by norm_num)) hg_sub_rem
  · rw [hswap_add, htsum_add_eq]
    exact hbound_xi g_add hg_add_xi_sum
      (fun _ => div_nonneg (integral_nonneg fun _ => sq_nonneg _) (by norm_num)) hg_add_rem


/-! ## §2b. Polarization Identity and Sub-Power Coercivity up to `(2/3) log Γ` -/

/-- Exact complex polarization identity `(a * conj b).re = ‖a + b‖² / 4 - ‖a - b‖² / 4`. -/
theorem re_mul_conj_polarization (a b : ℂ) :
    (a * conj b).re = ‖a + b‖ ^ 2 / 4 - ‖a - b‖ ^ 2 / 4 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Symmetric depth-sum profile `h_sum F₀ ρ u = F₀(u)((e^{(Re ρ - 1/2)u} + e^{-(Re ρ - 1/2)u})/2)e^{i Im ρ u}`
whose `paperFT` at `-ω` equals `(paperFT F₀_ℂ (gammaOf ρ - ω) + paperFT F₀_ℂ (conj (gammaOf ρ) - ω)) / 2`. -/
def depthSumProfile (F₀ : ℝ → ℝ) (ρ : ℂ) (u : ℝ) : ℂ :=
  ((F₀ u * ((Real.exp ((ρ.re - 1 / 2) * u) + Real.exp (-((ρ.re - 1 / 2) * u))) / 2) : ℝ) : ℂ) *
    Complex.exp (Complex.I * (ρ.im : ℂ) * (u : ℂ))

theorem paperFT_depthSumProfile_eq {F₀ : ℝ → ℝ} (hF₀ : Continuous F₀)
    (hF₀c : HasCompactSupport F₀) (ρ : ℂ) (ω : ℝ) :
    paperFT (depthSumProfile F₀ ρ) (-(ω : ℂ)) =
      (paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (ω : ℂ)) +
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (ω : ℂ))) / 2 := by
  have hi1 : Integrable fun u : ℝ =>
      (F₀ u : ℂ) * Complex.exp (Complex.I * (gammaOf ρ - (ω : ℂ)) * (u : ℂ)) :=
    ((Complex.continuous_ofReal.comp hF₀).mul (by fun_prop)).integrable_of_hasCompactSupport
      ((hF₀c.comp_left Complex.ofReal_zero).mul_right)
  have hi2 : Integrable fun u : ℝ =>
      (F₀ u : ℂ) * Complex.exp (Complex.I * (conj (gammaOf ρ) - (ω : ℂ)) * (u : ℂ)) :=
    ((Complex.continuous_ofReal.comp hF₀).mul (by fun_prop)).integrable_of_hasCompactSupport
      ((hF₀c.comp_left Complex.ofReal_zero).mul_right)
  unfold paperFT depthSumProfile
  rw [← integral_add hi1 hi2, ← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_ofNat, Complex.ofReal_exp, Complex.ofReal_exp]
  have h1 : Complex.exp (((ρ.re - 1 / 2) * u : ℝ) : ℂ) *
      Complex.exp (Complex.I * (ρ.im : ℂ) * (u : ℂ)) *
      Complex.exp (Complex.I * -(ω : ℂ) * (u : ℂ)) =
      Complex.exp (Complex.I * (gammaOf ρ - (ω : ℂ)) * (u : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, gammaOf_sub_real]
    congr 1; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have h2 : Complex.exp ((-((ρ.re - 1 / 2) * u) : ℝ) : ℂ) *
      Complex.exp (Complex.I * (ρ.im : ℂ) * (u : ℂ)) *
      Complex.exp (Complex.I * -(ω : ℂ) * (u : ℂ)) =
      Complex.exp (Complex.I * (conj (gammaOf ρ) - (ω : ℂ)) * (u : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, conj_gammaOf_sub_real]
    congr 1; push_cast; ring_nf; rw [Complex.I_sq]; ring
  calc (F₀ u : ℂ) *
        ((Complex.exp (((ρ.re - 1 / 2) * u : ℝ) : ℂ) +
          Complex.exp ((-((ρ.re - 1 / 2) * u) : ℝ) : ℂ)) / 2) *
        Complex.exp (Complex.I * (ρ.im : ℂ) * (u : ℂ)) *
        Complex.exp (Complex.I * -(ω : ℂ) * (u : ℂ))
      = ((F₀ u : ℂ) *
          (Complex.exp (((ρ.re - 1 / 2) * u : ℝ) : ℂ) *
            Complex.exp (Complex.I * (ρ.im : ℂ) * (u : ℂ)) *
            Complex.exp (Complex.I * -(ω : ℂ) * (u : ℂ))) +
        (F₀ u : ℂ) *
          (Complex.exp ((-((ρ.re - 1 / 2) * u) : ℝ) : ℂ) *
            Complex.exp (Complex.I * (ρ.im : ℂ) * (u : ℂ)) *
            Complex.exp (Complex.I * -(ω : ℂ) * (u : ℂ)))) / 2 := by ring
    _ = ((F₀ u : ℂ) * Complex.exp (Complex.I * (gammaOf ρ - (ω : ℂ)) * (u : ℂ)) +
          (F₀ u : ℂ) * Complex.exp (Complex.I * (conj (gammaOf ρ) - (ω : ℂ)) * (u : ℂ))) / 2 := by
          rw [h1, h2]

/-- Finite-core polarization lower bound for `(zetaZeroConfig.W (complexModulatedSource F₀ γ) ...).re`:
retains any chosen finite subset `C_fin` of positive depth-sum squares and subtracts the full
off-line depth-difference series. -/
theorem re_zeta_W_complexModulatedSource_ge_finset {F₀ : ℝ → ℝ}
    (hF₀ : ContDiff ℝ 2 F₀) (hF₀c : HasCompactSupport F₀) (γ : ℝ)
    (C_fin : Finset zetaZeroConfig.carrier)
    (hd_sum : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) :
    (∑ ρ ∈ C_fin, (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (depthSumProfile F₀ (ρ : ℂ)) (-(γ : ℂ))‖ ^ 2) -
      (∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) ≤
      (zetaZeroConfig.W (complexModulatedSource F₀ γ) (complexModulatedSource F₀ γ)).re := by
  have hf : ContDiff ℝ 2 (complexModulatedSource F₀ γ) := contDiff_complexModulatedSource hF₀ γ
  have hfc : HasCompactSupport (complexModulatedSource F₀ γ) :=
    hasCompactSupport_complexModulatedSource hF₀c γ
  have hsumW := zeta_Wsummand_summable hf hf hfc hfc
  have hw_re_sum : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.Wsummand (complexModulatedSource F₀ γ)
        (complexModulatedSource F₀ γ) ρ).re :=
    Complex.reCLM.summable hsumW
  have hp_eq : ∀ ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.Wsummand (complexModulatedSource F₀ γ)
          (complexModulatedSource F₀ γ) ρ).re +
        (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4 =
      (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (depthSumProfile F₀ (ρ : ℂ)) (-(γ : ℂ))‖ ^ 2 := fun ρ => by
    have hw : (zetaZeroConfig.Wsummand (complexModulatedSource F₀ γ)
        (complexModulatedSource F₀ γ) ρ).re =
        (zetaZeroConfig.mult ρ : ℝ) *
          (paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) *
            conj (paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ)))).re := by
      simp [ZeroConfig.Wsummand, paperFT_complexModulatedSource, mul_assoc]
    rw [hw, re_mul_conj_polarization, paperFT_depthSumProfile_eq hF₀.continuous hF₀c (ρ : ℂ) γ,
      norm_div, Complex.norm_ofNat]
    ring
  have hp_sum : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (depthSumProfile F₀ (ρ : ℂ)) (-(γ : ℂ))‖ ^ 2 :=
    (hw_re_sum.add hd_sum).congr hp_eq
  have hle := Summable.sum_le_tsum C_fin (fun ρ _ => by positivity) hp_sum
  have htsum : (∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (depthSumProfile F₀ (ρ : ℂ)) (-(γ : ℂ))‖ ^ 2) =
      (zetaZeroConfig.W (complexModulatedSource F₀ γ) (complexModulatedSource F₀ γ)).re +
        ∑' ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℝ) *
            ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
              paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4 := by
    rw [← tsum_congr hp_eq, hw_re_sum.tsum_add hd_sum, ZeroConfig.W, Complex.re_tsum hsumW]
  linarith

/-- Finite-core polarization lower bound for a single real `cosineSource F₀ γ`:
retains any chosen finite subset `C_fin` of `(1/8)‖S_-‖² - (1/4)‖S_+‖²` core contributions and
subtracts the two-shift off-line depth-difference average `(∑' d_sub + ∑' d_add) / 2`. -/
theorem fullZeroForm_cosineSource_ge_finset {F₀ : ℝ → ℝ}
    (hF₀ : ContDiff ℝ 2 F₀) (hF₀c : HasCompactSupport F₀) (γ : ℝ)
    (C_fin : Finset zetaZeroConfig.carrier)
    (hd_sub_sum : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4)
    (hd_add_sum : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))‖ ^ 2 / 4) :
    (∑ ρ ∈ C_fin, (zetaZeroConfig.mult ρ : ℝ) *
        (‖paperFT (depthSumProfile F₀ (ρ : ℂ)) (-(γ : ℂ))‖ ^ 2 / 8 -
          ‖paperFT (depthSumProfile F₀ (ρ : ℂ)) (γ : ℂ)‖ ^ 2 / 4)) -
      ((∑' ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℝ) *
            ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
              paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) +
        ∑' ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℝ) *
            ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ)) -
              paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))‖ ^ 2 / 4) / 2 ≤
      fullZeroForm (cosineSource F₀ γ) := by
  have hcos : ContDiff ℝ 2 (cosineSource F₀ γ) := contDiff_cosineSource hF₀ γ
  have hcosc : HasCompactSupport (cosineSource F₀ γ) := hF₀c.mul_right
  have hfc2 : ContDiff ℝ 2 (fun u : ℝ => (cosineSource F₀ γ u : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hcos
  have hfcc : HasCompactSupport (fun u : ℝ => (cosineSource F₀ γ u : ℂ)) :=
    hcosc.comp_left Complex.ofReal_zero
  have hsumW := zeta_Wsummand_summable hfc2 hfc2 hfcc hfcc
  have hw_re_sum : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.Wsummand (fun u => (cosineSource F₀ γ u : ℂ))
        (fun u => (cosineSource F₀ γ u : ℂ)) ρ).re :=
    Complex.reCLM.summable hsumW
  have hd_avg_sum := (hd_sub_sum.add hd_add_sum).div_const 2
  have hp_bounds : ∀ ρ : zetaZeroConfig.carrier,
      0 ≤ (zetaZeroConfig.Wsummand (fun u => (cosineSource F₀ γ u : ℂ))
            (fun u => (cosineSource F₀ γ u : ℂ)) ρ).re +
          ((zetaZeroConfig.mult ρ : ℝ) *
              ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
                paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4 +
            (zetaZeroConfig.mult ρ : ℝ) *
              ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ)) -
                paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))‖ ^ 2 / 4) / 2 ∧
      (zetaZeroConfig.mult ρ : ℝ) *
          (‖paperFT (depthSumProfile F₀ (ρ : ℂ)) (-(γ : ℂ))‖ ^ 2 / 8 -
            ‖paperFT (depthSumProfile F₀ (ρ : ℂ)) (γ : ℂ)‖ ^ 2 / 4) ≤
        (zetaZeroConfig.Wsummand (fun u => (cosineSource F₀ γ u : ℂ))
            (fun u => (cosineSource F₀ γ u : ℂ)) ρ).re +
          ((zetaZeroConfig.mult ρ : ℝ) *
              ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
                paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4 +
            (zetaZeroConfig.mult ρ : ℝ) *
              ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ)) -
                paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))‖ ^ 2 / 4) / 2 :=
    fun ρ => by
      let um := paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ))
      let up := paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ))
      let vm := paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))
      let vp := paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))
      have hw : (zetaZeroConfig.Wsummand (fun u => (cosineSource F₀ γ u : ℂ))
          (fun u => (cosineSource F₀ γ u : ℂ)) ρ).re =
          (zetaZeroConfig.mult ρ : ℝ) *
            (‖(um + up) / 2 + (vm + vp) / 2‖ ^ 2 / 4 -
              ‖(um + up) / 2 - (vm + vp) / 2‖ ^ 2 / 4) := by
        have h1 : (zetaZeroConfig.Wsummand (fun u => (cosineSource F₀ γ u : ℂ))
            (fun u => (cosineSource F₀ γ u : ℂ)) ρ).re =
            (zetaZeroConfig.mult ρ : ℝ) *
              (((um + up) / 2) * conj ((vm + vp) / 2)).re := by
          simp [ZeroConfig.Wsummand, paperFT_cosineSource hF₀.continuous hF₀c, mul_assoc,
            um, up, vm, vp]
        rw [h1, re_mul_conj_polarization]
      have hdiff_le : ‖(um + up) / 2 - (vm + vp) / 2‖ ^ 2 / 4 ≤
          (‖um - vm‖ ^ 2 / 4 + ‖up - vp‖ ^ 2 / 4) / 2 := by
        have hrew : (um + up) / 2 - (vm + vp) / 2 = ((um - vm) + (up - vp)) / 2 := by ring
        rw [hrew, norm_div, Complex.norm_ofNat]
        have htri := norm_add_le (um - vm) (up - vp)
        have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
        nlinarith [sq_nonneg (‖um - vm‖ - ‖up - vp‖)]
      have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
      have hd_gap : 0 ≤ ((zetaZeroConfig.mult ρ : ℝ) * ‖um - vm‖ ^ 2 / 4 +
            (zetaZeroConfig.mult ρ : ℝ) * ‖up - vp‖ ^ 2 / 4) / 2 -
          (zetaZeroConfig.mult ρ : ℝ) * (‖(um + up) / 2 - (vm + vp) / 2‖ ^ 2 / 4) := by
        have hmul := mul_le_mul_of_nonneg_left hdiff_le hm
        linarith
      have hS_minus : paperFT (depthSumProfile F₀ (ρ : ℂ)) (-(γ : ℂ)) = (um + vm) / 2 :=
        paperFT_depthSumProfile_eq hF₀.continuous hF₀c (ρ : ℂ) γ
      have hS_plus : paperFT (depthSumProfile F₀ (ρ : ℂ)) (γ : ℂ) = (up + vp) / 2 := by
        simpa [sub_neg_eq_add, up, vp] using
          paperFT_depthSumProfile_eq hF₀.continuous hF₀c (ρ : ℂ) (-γ)
      have hsum_ge : ‖(um + vm) / 2‖ ^ 2 / 8 - ‖(up + vp) / 2‖ ^ 2 / 4 ≤
          ‖(um + up) / 2 + (vm + vp) / 2‖ ^ 2 / 4 := by
        have hrew : (um + up) / 2 + (vm + vp) / 2 = (um + vm) / 2 + (up + vp) / 2 := by ring
        rw [hrew]
        have htri : ‖(um + vm) / 2‖ ≤ ‖(um + vm) / 2 + (up + vp) / 2‖ + ‖(up + vp) / 2‖ := by
          simpa using norm_sub_le ((um + vm) / 2 + (up + vp) / 2) ((up + vp) / 2)
        have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
        nlinarith [sq_nonneg (‖(um + vm) / 2 + (up + vp) / 2‖ - ‖(up + vp) / 2‖)]
      rw [hw, hS_minus, hS_plus]
      refine ⟨?_, ?_⟩
      · have hpos : 0 ≤ (zetaZeroConfig.mult ρ : ℝ) *
            (‖(um + up) / 2 + (vm + vp) / 2‖ ^ 2 / 4) := by positivity
        linarith
      · have hmul := mul_le_mul_of_nonneg_left hsum_ge hm
        linarith
  have hfin_le := (Finset.sum_le_sum fun ρ _ => (hp_bounds ρ).2).trans
    (Summable.sum_le_tsum C_fin (fun ρ _ => (hp_bounds ρ).1) (hw_re_sum.add hd_avg_sum))
  have htsum : (∑' ρ : zetaZeroConfig.carrier,
      ((zetaZeroConfig.Wsummand (fun u => (cosineSource F₀ γ u : ℂ))
          (fun u => (cosineSource F₀ γ u : ℂ)) ρ).re +
        ((zetaZeroConfig.mult ρ : ℝ) *
            ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
              paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4 +
          (zetaZeroConfig.mult ρ : ℝ) *
            ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ)) -
              paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))‖ ^ 2 / 4) / 2)) =
      fullZeroForm (cosineSource F₀ γ) +
        ((∑' ρ : zetaZeroConfig.carrier,
            (zetaZeroConfig.mult ρ : ℝ) *
              ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
                paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) +
          ∑' ρ : zetaZeroConfig.carrier,
            (zetaZeroConfig.mult ρ : ℝ) *
              ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ)) -
                paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))‖ ^ 2 / 4) / 2 := by
    rw [hw_re_sum.tsum_add hd_avg_sum, fullZeroForm_eq_zeta_W_re hcos hcosc,
      ZeroConfig.W, Complex.re_tsum hsumW, tsum_div_const, hd_sub_sum.tsum_add hd_add_sum]
  linarith

/-- **Sub-Power Frequency-Averaged Coercivity of the Quadrature Weil Form up to `(2/3) log Γ`
(`exists_frequencyAverage_quadrature_fullZeroForm_ge_subpower`):**
For every aperture slope `0 ≤ α < 2/3` (exceeding both Huxley `5/12` and Guth–Maynard `13/30`)
and every `η > 0`, there exist `C ≥ 0`, `C_rem ≥ 0`, and `Γ₀ ≥ 8` such that for all `Γ ≥ Γ₀`,
all `0 ≤ A ≤ α log Γ`, and every `F₀ ∈ C²_c(ℝ)` supported in `[-A, A]`,
`(1 / Γ) ∫_Γ^{2Γ} (fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ)) dγ
  ≥ -C Γ^η ∫ F₀² - C_rem Γ^{α - 2} envelopeWindowNorm F₀ ^ 2`. -/
theorem exists_frequencyAverage_quadrature_fullZeroForm_ge_subpower
    {α η : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3) (hη : 0 < η) :
    ∃ C C_rem : ℝ, 0 ≤ C ∧ 0 ≤ C_rem ∧ ∃ Γ₀ : ℝ, 8 ≤ Γ₀ ∧
      ∀ Γ : ℝ, Γ₀ ≤ Γ → ∀ A : ℝ, 0 ≤ A → A ≤ α * Real.log Γ →
        ∀ F₀ : ℝ → ℝ, ContDiff ℝ 2 F₀ → HasCompactSupport F₀ →
          (∀ u : ℝ, A < |u| → F₀ u = 0) →
          -C * Γ ^ η * (∫ u, F₀ u ^ 2) -
              C_rem * Γ ^ (α - 2) * envelopeWindowNorm F₀ ^ 2 ≤
            (1 / Γ) * ∫ γ in Icc Γ (2 * Γ),
              (fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ)) := by
  obtain ⟨C_loc, hC_loc, Γ₀, hΓ₀, hthree⟩ :=
    exists_sum_exp_foldedRe_threeShells_le_subpower hα0 hα hη
  refine ⟨(Real.pi / 2) * C_loc, 32 * reciprocalSquareWeightTotal,
    by positivity, by positivity [reciprocalSquareWeightTotal_nonneg], Γ₀, hΓ₀,
    fun Γ hΓ A hA0 hA F₀ hF₀ hF₀c hsupp => ?_⟩
  have hΓ8 : 8 ≤ Γ := hΓ₀.trans hΓ
  have hΓ1 : 1 ≤ Γ := by linarith
  have hΓ0 : 0 < Γ := by linarith
  obtain ⟨hd_sub_sum, _hd_add_sum, hc_sub, _hc_add, G_loc, hG_loc, hsub_int, _hadd_int⟩ :=
    integral_Icc_tsum_depthDiff_div_four_le hF₀ hF₀c hΓ1 hA0 hsupp
  have hpt : ∀ γ ∈ Icc Γ (2 * Γ),
      -(∑' ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℝ) *
            ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
              paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) ≤
        fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ) := fun γ _ => by
    rw [fullZeroForm_cosine_add_sine_eq_zeta_W_re hF₀ hF₀c γ]
    have h := re_zeta_W_complexModulatedSource_ge_finset hF₀ hF₀c γ ∅ (hd_sub_sum γ)
    rwa [Finset.sum_empty, zero_sub] at h
  have hquad_cont : Continuous fun γ : ℝ =>
      fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ) := by
    have heq : (fun γ : ℝ => fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ)) =
        fun γ : ℝ =>
          (zetaZeroConfig.W (complexModulatedSource F₀ γ) (complexModulatedSource F₀ γ)).re :=
      funext (fullZeroForm_cosine_add_sine_eq_zeta_W_re hF₀ hF₀c)
    rw [heq]
    exact (continuous_zeta_W_re_modulated hF₀ hF₀c).1
  have hneg_sub_int : IntegrableOn
      (fun γ : ℝ => -(∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4))
      (Icc Γ (2 * Γ)) :=
    hc_sub.neg.integrableOn_Icc
  have hint_ge := setIntegral_mono_on hneg_sub_int
    hquad_cont.integrableOn_Icc measurableSet_Icc hpt
  rw [integral_neg] at hint_ge
  -- Bound the local Plancherel sum over `G_loc`
  have hGloc_le : (∑ q ∈ G_loc,
      (∫ γ in Icc Γ (2 * Γ),
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2) / 4) ≤
      (Real.pi / 2) * (∫ u, F₀ u ^ 2) *
        ∑ q ∈ G_loc, Real.exp (2 * A * (foldedRe q - 1 / 2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ => ?_
    have hpl := (integral_norm_paperFT_depthDiff_sq_le hF₀.continuous hF₀c hA0 hsupp
      (q.1 : ℂ) Γ (2 * Γ)).2.1
    rw [← foldedRe_sub_half_eq_abs q] at hpl
    linarith
  have hshell := hthree Γ hΓ A hA0 hA G_loc hG_loc
  have hmass_nn : 0 ≤ ∫ u, F₀ u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hloc_tot : (1 / Γ) * ((Real.pi / 2) * (∫ u, F₀ u ^ 2) *
      ∑ q ∈ G_loc, Real.exp (2 * A * (foldedRe q - 1 / 2))) ≤
      (Real.pi / 2) * C_loc * Γ ^ η * (∫ u, F₀ u ^ 2) := by
    calc (1 / Γ) * ((Real.pi / 2) * (∫ u, F₀ u ^ 2) *
          ∑ q ∈ G_loc, Real.exp (2 * A * (foldedRe q - 1 / 2)))
        = (Real.pi / 2) * (∫ u, F₀ u ^ 2) *
            ((1 / Γ) * ∑ q ∈ G_loc, Real.exp (2 * A * (foldedRe q - 1 / 2))) := by ring
      _ ≤ (Real.pi / 2) * (∫ u, F₀ u ^ 2) * (C_loc * Γ ^ η) :=
          mul_le_mul_of_nonneg_left hshell (by positivity)
      _ = (Real.pi / 2) * C_loc * Γ ^ η * (∫ u, F₀ u ^ 2) := by ring
  have hexpA : Real.exp A ≤ Γ ^ α := by
    calc Real.exp A ≤ Real.exp (α * Real.log Γ) := Real.exp_le_exp.mpr hA
      _ = Γ ^ α := by rw [Real.rpow_def_of_pos hΓ0, mul_comm]
  have hrem_tot : (1 / Γ) * ((32 * reciprocalSquareWeightTotal / Γ) *
      Real.exp A * envelopeWindowNorm F₀ ^ 2) ≤
      32 * reciprocalSquareWeightTotal * Γ ^ (α - 2) * envelopeWindowNorm F₀ ^ 2 := by
    have hrpow : (1 / Γ) * (1 / Γ) * Γ ^ α = Γ ^ (α - 2) := by
      have hsq : (1 / Γ) * (1 / Γ) = Γ ^ (-2 : ℝ) := by
        have h1 : (Γ ^ 2)⁻¹ = Γ ^ (-2 : ℝ) := by
          rw [← Real.rpow_natCast Γ 2, ← Real.rpow_neg hΓ0.le]; norm_num
        calc (1 / Γ) * (1 / Γ) = (Γ ^ 2)⁻¹ := by ring
          _ = Γ ^ (-2 : ℝ) := h1
      rw [hsq, ← Real.rpow_add hΓ0]; congr 1; ring
    calc (1 / Γ) * ((32 * reciprocalSquareWeightTotal / Γ) *
          Real.exp A * envelopeWindowNorm F₀ ^ 2)
        ≤ (1 / Γ) * ((32 * reciprocalSquareWeightTotal / Γ) *
            Γ ^ α * envelopeWindowNorm F₀ ^ 2) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hexpA
                (by positivity [reciprocalSquareWeightTotal_nonneg]))
              (sq_nonneg _)) (by positivity)
      _ = 32 * reciprocalSquareWeightTotal * ((1 / Γ) * (1 / Γ) * Γ ^ α) *
            envelopeWindowNorm F₀ ^ 2 := by ring
      _ = 32 * reciprocalSquareWeightTotal * Γ ^ (α - 2) * envelopeWindowNorm F₀ ^ 2 := by
          rw [hrpow]
  have hupper : (1 / Γ) * (∫ γ in Icc Γ (2 * Γ),
      ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) ≤
      (Real.pi / 2) * C_loc * Γ ^ η * (∫ u, F₀ u ^ 2) +
        32 * reciprocalSquareWeightTotal * Γ ^ (α - 2) * envelopeWindowNorm F₀ ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left
      (hsub_int.trans (add_le_add hGloc_le le_rfl)) (by positivity : 0 ≤ 1 / Γ)
    rw [mul_add] at h1
    exact h1.trans (add_le_add hloc_tot hrem_tot)
  have hlower := mul_le_mul_of_nonneg_left hint_ge (by positivity : 0 ≤ 1 / Γ)
  linarith

/-- **Sub-Power Frequency-Averaged Coercivity of Single `cosineSource F₀ γ` up to `(2/3) log Γ`
(`exists_frequencyAverage_fullZeroForm_cosineSource_ge_subpower`):**
Same sub-power coercivity law for the single real modulated test `cosineSource F₀ γ`. -/
theorem exists_frequencyAverage_fullZeroForm_cosineSource_ge_subpower
    {α η : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3) (hη : 0 < η) :
    ∃ C C_rem : ℝ, 0 ≤ C ∧ 0 ≤ C_rem ∧ ∃ Γ₀ : ℝ, 8 ≤ Γ₀ ∧
      ∀ Γ : ℝ, Γ₀ ≤ Γ → ∀ A : ℝ, 0 ≤ A → A ≤ α * Real.log Γ →
        ∀ F₀ : ℝ → ℝ, ContDiff ℝ 2 F₀ → HasCompactSupport F₀ →
          (∀ u : ℝ, A < |u| → F₀ u = 0) →
          -C * Γ ^ η * (∫ u, F₀ u ^ 2) -
              C_rem * Γ ^ (α - 2) * envelopeWindowNorm F₀ ^ 2 ≤
            (1 / Γ) * ∫ γ in Icc Γ (2 * Γ), fullZeroForm (cosineSource F₀ γ) := by
  obtain ⟨C_loc, hC_loc, Γ₀, hΓ₀, hthree⟩ :=
    exists_sum_exp_foldedRe_threeShells_le_subpower hα0 hα hη
  refine ⟨(Real.pi / 2) * C_loc, 32 * reciprocalSquareWeightTotal,
    by positivity, by positivity [reciprocalSquareWeightTotal_nonneg], Γ₀, hΓ₀,
    fun Γ hΓ A hA0 hA F₀ hF₀ hF₀c hsupp => ?_⟩
  have hΓ8 : 8 ≤ Γ := hΓ₀.trans hΓ
  have hΓ1 : 1 ≤ Γ := by linarith
  have hΓ0 : 0 < Γ := by linarith
  obtain ⟨hd_sub_sum, hd_add_sum, hc_sub, hc_add, G_loc, hG_loc, hsub_int, hadd_int⟩ :=
    integral_Icc_tsum_depthDiff_div_four_le hF₀ hF₀c hΓ1 hA0 hsupp
  let D : ℝ → ℝ := fun γ =>
    ((∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) +
      ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))‖ ^ 2 / 4) / 2
  have hpt : ∀ γ ∈ Icc Γ (2 * Γ), -D γ ≤ fullZeroForm (cosineSource F₀ γ) := fun γ _ => by
    have h := fullZeroForm_cosineSource_ge_finset hF₀ hF₀c γ ∅ (hd_sub_sum γ) (hd_add_sum γ)
    rwa [Finset.sum_empty, zero_sub] at h
  have hf_cos_cont := (continuous_zeta_W_re_modulated hF₀ hF₀c).2
  have hD_neg_int : IntegrableOn (fun γ : ℝ => -D γ) (Icc Γ (2 * Γ)) :=
    (((hc_sub.add hc_add).div_const 2).neg).integrableOn_Icc
  have hint_ge := setIntegral_mono_on hD_neg_int hf_cos_cont.integrableOn_Icc measurableSet_Icc hpt
  rw [integral_neg] at hint_ge
  dsimp only [D] at hint_ge
  rw [integral_div, integral_add hc_sub.integrableOn_Icc hc_add.integrableOn_Icc] at hint_ge
  have hGloc_sub : (∑ q ∈ G_loc,
      (∫ γ in Icc Γ (2 * Γ),
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2) / 4) ≤
      (Real.pi / 2) * (∫ u, F₀ u ^ 2) *
        ∑ q ∈ G_loc, Real.exp (2 * A * (foldedRe q - 1 / 2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ => ?_
    have hpl := (integral_norm_paperFT_depthDiff_sq_le hF₀.continuous hF₀c hA0 hsupp
      (q.1 : ℂ) Γ (2 * Γ)).2.1
    rw [← foldedRe_sub_half_eq_abs q] at hpl
    linarith
  have hGloc_add : (∑ q ∈ G_loc,
      (∫ γ in Icc Γ (2 * Γ),
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) + (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) + (γ : ℂ))‖ ^ 2) / 4) ≤
      (Real.pi / 2) * (∫ u, F₀ u ^ 2) *
        ∑ q ∈ G_loc, Real.exp (2 * A * (foldedRe q - 1 / 2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ => ?_
    have hpl := (integral_norm_paperFT_depthDiff_add_sq_le hF₀.continuous hF₀c hA0 hsupp
      (q.1 : ℂ) Γ (2 * Γ)).1
    rw [← foldedRe_sub_half_eq_abs q] at hpl
    linarith
  have hshell := hthree Γ hΓ A hA0 hA G_loc hG_loc
  have hmass_nn : 0 ≤ ∫ u, F₀ u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hloc_tot : (1 / Γ) * ((Real.pi / 2) * (∫ u, F₀ u ^ 2) *
      ∑ q ∈ G_loc, Real.exp (2 * A * (foldedRe q - 1 / 2))) ≤
      (Real.pi / 2) * C_loc * Γ ^ η * (∫ u, F₀ u ^ 2) := by
    calc (1 / Γ) * ((Real.pi / 2) * (∫ u, F₀ u ^ 2) *
          ∑ q ∈ G_loc, Real.exp (2 * A * (foldedRe q - 1 / 2)))
        = (Real.pi / 2) * (∫ u, F₀ u ^ 2) *
            ((1 / Γ) * ∑ q ∈ G_loc, Real.exp (2 * A * (foldedRe q - 1 / 2))) := by ring
      _ ≤ (Real.pi / 2) * (∫ u, F₀ u ^ 2) * (C_loc * Γ ^ η) :=
          mul_le_mul_of_nonneg_left hshell (by positivity)
      _ = (Real.pi / 2) * C_loc * Γ ^ η * (∫ u, F₀ u ^ 2) := by ring
  have hexpA : Real.exp A ≤ Γ ^ α := by
    calc Real.exp A ≤ Real.exp (α * Real.log Γ) := Real.exp_le_exp.mpr hA
      _ = Γ ^ α := by rw [Real.rpow_def_of_pos hΓ0, mul_comm]
  have hrem_tot : (1 / Γ) * ((32 * reciprocalSquareWeightTotal / Γ) *
      Real.exp A * envelopeWindowNorm F₀ ^ 2) ≤
      32 * reciprocalSquareWeightTotal * Γ ^ (α - 2) * envelopeWindowNorm F₀ ^ 2 := by
    have hrpow : (1 / Γ) * (1 / Γ) * Γ ^ α = Γ ^ (α - 2) := by
      have hsq : (1 / Γ) * (1 / Γ) = Γ ^ (-2 : ℝ) := by
        have h1 : (Γ ^ 2)⁻¹ = Γ ^ (-2 : ℝ) := by
          rw [← Real.rpow_natCast Γ 2, ← Real.rpow_neg hΓ0.le]; norm_num
        calc (1 / Γ) * (1 / Γ) = (Γ ^ 2)⁻¹ := by ring
          _ = Γ ^ (-2 : ℝ) := h1
      rw [hsq, ← Real.rpow_add hΓ0]; congr 1; ring
    calc (1 / Γ) * ((32 * reciprocalSquareWeightTotal / Γ) *
          Real.exp A * envelopeWindowNorm F₀ ^ 2)
        ≤ (1 / Γ) * ((32 * reciprocalSquareWeightTotal / Γ) *
            Γ ^ α * envelopeWindowNorm F₀ ^ 2) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hexpA
                (by positivity [reciprocalSquareWeightTotal_nonneg]))
              (sq_nonneg _)) (by positivity)
      _ = 32 * reciprocalSquareWeightTotal * ((1 / Γ) * (1 / Γ) * Γ ^ α) *
            envelopeWindowNorm F₀ ^ 2 := by ring
      _ = 32 * reciprocalSquareWeightTotal * Γ ^ (α - 2) * envelopeWindowNorm F₀ ^ 2 := by
          rw [hrpow]
  have havg_le : ((∫ γ in Icc Γ (2 * Γ),
        ∑' ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℝ) *
            ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
              paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) +
      ∫ γ in Icc Γ (2 * Γ),
        ∑' ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℝ) *
            ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ)) -
              paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))‖ ^ 2 / 4) / 2 ≤
      (Real.pi / 2) * (∫ u, F₀ u ^ 2) *
          (∑ q ∈ G_loc, Real.exp (2 * A * (foldedRe q - 1 / 2))) +
        (32 * reciprocalSquareWeightTotal / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 := by
    linarith [hsub_int, hadd_int, hGloc_sub, hGloc_add]
  have hupper := mul_le_mul_of_nonneg_left havg_le (by positivity : 0 ≤ 1 / Γ)
  rw [mul_add] at hupper
  have htot := hupper.trans (add_le_add hloc_tot hrem_tot)
  have hlower := mul_le_mul_of_nonneg_left hint_ge (by positivity : 0 ≤ 1 / Γ)
  linarith

/-! ## §3. Collapse of the Effective Exponential Floor Rate from `zetaZeroWidth` to `0` and Bad-Frequency Decay -/

/-- **Collapse of the Effective Exponential Floor Rate to `0`
(`exists_frequencyAverage_fullZeroForm_ge_neg_exp_every_pos_rate`):**
While unfiltered `fullZeroForm` on `C²_c([-A, A])` has exponential worst-case growth governed by
`zetaZeroWidth` (`AllParityCriticalDeficitAndEndpointSobolevLaws`), modulating along any exponential
frequency schedule `Γ = e^{λ A}` with `λ > 3/2` collapses the effective exponential floor rate
unconditionally to **`0`**: for **every** `β > 0`, the negative part grows at most as `O(e^{2βA})`. -/
theorem exists_frequencyAverage_fullZeroForm_ge_neg_exp_every_pos_rate
    {lam β : ℝ} (hlam : 3 / 2 < lam) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ A₀ : ℝ, 0 ≤ A₀ ∧
      ∀ A : ℝ, A₀ ≤ A →
        ∀ F₀ : ℝ → ℝ, ContDiff ℝ 2 F₀ → HasCompactSupport F₀ →
          (∀ u : ℝ, A < |u| → F₀ u = 0) →
          -C * Real.exp (2 * β * A) * ((∫ u, F₀ u ^ 2) + envelopeWindowNorm F₀ ^ 2) ≤
            (1 / Real.exp (lam * A)) *
              ∫ γ in Icc (Real.exp (lam * A)) (2 * Real.exp (lam * A)),
                fullZeroForm (cosineSource F₀ γ) := by
  have hlam_pos : 0 < lam := by linarith
  have hα0 : 0 ≤ 1 / lam := by positivity
  have hα_lt : 1 / lam < 2 / 3 := by
    rw [div_lt_div_iff₀ hlam_pos (by norm_num)]
    linarith
  have hη : 0 < 2 * β / lam := div_pos (by positivity) hlam_pos
  obtain ⟨C₁, C_rem, hC₁, hC_rem, Γ₀, hΓ₀, hsub⟩ :=
    exists_frequencyAverage_fullZeroForm_cosineSource_ge_subpower hα0 hα_lt hη
  refine ⟨C₁ + C_rem, by positivity, max 0 (Real.log Γ₀ / lam), le_max_left _ _,
    fun A hA F₀ hF₀ hF₀c hsupp => ?_⟩
  have hA0 : 0 ≤ A := (le_max_left _ _).trans hA
  have hA_log : Real.log Γ₀ / lam ≤ A := (le_max_right _ _).trans hA
  have hΓ_ge : Γ₀ ≤ Real.exp (lam * A) := by
    have hmul := (div_le_iff₀ hlam_pos).mp hA_log
    calc Γ₀ = Real.exp (Real.log Γ₀) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (lam * A) := Real.exp_le_exp.mpr (by linarith)
  have hA_ap : A ≤ (1 / lam) * Real.log (Real.exp (lam * A)) := by
    rw [Real.log_exp]; field_simp [hlam_pos.ne']; exact le_rfl
  have hmain := hsub (Real.exp (lam * A)) hΓ_ge A hA0 hA_ap F₀ hF₀ hF₀c hsupp
  have hrpow_η : (Real.exp (lam * A)) ^ (2 * β / lam) = Real.exp (2 * β * A) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1; field_simp [hlam_pos.ne']
  have hrpow_rem : (Real.exp (lam * A)) ^ (1 / lam - 2) ≤ Real.exp (2 * β * A) := by
    have h1 : 1 ≤ Real.exp (lam * A) := Real.one_le_exp (by positivity)
    have h2 : (Real.exp (lam * A)) ^ (1 / lam - 2) ≤ (Real.exp (lam * A)) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    rw [Real.rpow_zero] at h2
    exact h2.trans (Real.one_le_exp (by positivity))
  rw [hrpow_η] at hmain
  have hm1 : 0 ≤ ∫ u, F₀ u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hm2 : 0 ≤ envelopeWindowNorm F₀ ^ 2 := sq_nonneg _
  have hrem_le : C_rem * (Real.exp (lam * A)) ^ (1 / lam - 2) * envelopeWindowNorm F₀ ^ 2 ≤
      C_rem * Real.exp (2 * β * A) * envelopeWindowNorm F₀ ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrpow_rem hC_rem) hm2
  have hp1 : 0 ≤ C₁ * Real.exp (2 * β * A) * envelopeWindowNorm F₀ ^ 2 := by positivity
  have hp2 : 0 ≤ C_rem * Real.exp (2 * β * A) * ∫ u, F₀ u ^ 2 := by positivity
  have hexpand : -(C₁ + C_rem) * Real.exp (2 * β * A) *
      ((∫ u, F₀ u ^ 2) + envelopeWindowNorm F₀ ^ 2) =
      -C₁ * Real.exp (2 * β * A) * (∫ u, F₀ u ^ 2) -
        C_rem * Real.exp (2 * β * A) * envelopeWindowNorm F₀ ^ 2 -
        C₁ * Real.exp (2 * β * A) * envelopeWindowNorm F₀ ^ 2 -
        C_rem * Real.exp (2 * β * A) * (∫ u, F₀ u ^ 2) := by ring
  linarith

/-- **Sub-Linear Measure of Bad Frequencies (`exists_volume_bad_frequencies_fullZeroForm_cosineSource_le`):**
For every `0 ≤ α < 2/3`, `η > 0`, and positive threshold `M > 0`, the Lebesgue measure of
frequencies `γ ∈ [Γ, 2Γ]` where `fullZeroForm (cosineSource F₀ γ) < -M` is at most
`(C Γ^{1 + η} ∫ F₀² + C_rem Γ^{α - 1} envelopeWindowNorm F₀ ^ 2) / M` (hence `O(Γ^{1 - δ})` when
`M = Γ^{2δ}` and `η = δ`, which is `o(Γ)`). -/
theorem exists_volume_bad_frequencies_fullZeroForm_cosineSource_le
    {α η : ℝ} (hα0 : 0 ≤ α) (hα : α < 2 / 3) (hη : 0 < η) :
    ∃ C C_rem : ℝ, 0 ≤ C ∧ 0 ≤ C_rem ∧ ∃ Γ₀ : ℝ, 8 ≤ Γ₀ ∧
      ∀ Γ : ℝ, Γ₀ ≤ Γ → ∀ A : ℝ, 0 ≤ A → A ≤ α * Real.log Γ →
        ∀ F₀ : ℝ → ℝ, ContDiff ℝ 2 F₀ → HasCompactSupport F₀ →
          (∀ u : ℝ, A < |u| → F₀ u = 0) →
          ∀ M : ℝ, 0 < M →
            (MeasureTheory.volume
              {γ ∈ Icc Γ (2 * Γ) | fullZeroForm (cosineSource F₀ γ) < -M}).toReal ≤
              (C * Γ ^ (1 + η) * (∫ u, F₀ u ^ 2) +
                C_rem * Γ ^ (α - 1) * envelopeWindowNorm F₀ ^ 2) / M := by
  obtain ⟨C_loc, hC_loc, Γ₀, hΓ₀, hthree⟩ :=
    exists_sum_exp_foldedRe_threeShells_le_subpower hα0 hα hη
  refine ⟨(Real.pi / 2) * C_loc, 32 * reciprocalSquareWeightTotal,
    by positivity, by positivity [reciprocalSquareWeightTotal_nonneg], Γ₀, hΓ₀,
    fun Γ hΓ A hA0 hA F₀ hF₀ hF₀c hsupp M hM => ?_⟩
  have hΓ8 : 8 ≤ Γ := hΓ₀.trans hΓ
  have hΓ1 : 1 ≤ Γ := by linarith
  have hΓ0 : 0 < Γ := by linarith
  obtain ⟨hd_sub_sum, hd_add_sum, hc_sub, hc_add, G_loc, hG_loc, hsub_int, hadd_int⟩ :=
    integral_Icc_tsum_depthDiff_div_four_le hF₀ hF₀c hΓ1 hA0 hsupp
  let D : ℝ → ℝ := fun γ =>
    ((∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) +
      ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))‖ ^ 2 / 4) / 2
  have hD_nn : ∀ γ : ℝ, 0 ≤ D γ := fun γ =>
    div_nonneg (add_nonneg (tsum_nonneg fun _ => by positivity)
      (tsum_nonneg fun _ => by positivity)) (by norm_num)
  have hD_int : IntegrableOn D (Icc Γ (2 * Γ)) :=
    ((hc_sub.add hc_add).div_const 2).integrableOn_Icc
  let S : Set ℝ := {γ ∈ Icc Γ (2 * Γ) | fullZeroForm (cosineSource F₀ γ) < -M}
  have hf_cos_cont := (continuous_zeta_W_re_modulated hF₀ hF₀c).2
  have hS_meas : MeasurableSet S :=
    measurableSet_Icc.inter (isOpen_Iio.preimage hf_cos_cont).measurableSet
  have hS_sub : S ⊆ Icc Γ (2 * Γ) := fun _ h => h.1
  have hM_le_D : ∀ γ ∈ S, M ≤ D γ := fun γ hγ => by
    have hge := fullZeroForm_cosineSource_ge_finset hF₀ hF₀c γ ∅ (hd_sub_sum γ) (hd_add_sum γ)
    rw [Finset.sum_empty, zero_sub] at hge
    have hlt : fullZeroForm (cosineSource F₀ γ) < -M := hγ.2
    change -D γ ≤ fullZeroForm (cosineSource F₀ γ) at hge
    linarith
  have hmarkov : (MeasureTheory.volume S).toReal * M ≤ ∫ γ in Icc Γ (2 * Γ), D γ := by
    calc (MeasureTheory.volume S).toReal * M
        = ∫ _γ in S, M := by rw [setIntegral_const, Measure.real, smul_eq_mul]
      _ ≤ ∫ γ in S, D γ :=
          setIntegral_mono_on (continuous_const.integrableOn_Icc.mono_set hS_sub)
            (hD_int.mono_set hS_sub) hS_meas hM_le_D
      _ ≤ ∫ γ in Icc Γ (2 * Γ), D γ :=
          setIntegral_mono_set hD_int (Eventually.of_forall hD_nn) (LE.le.eventuallyLE hS_sub)
  -- Bound `∫ γ in Icc Γ (2 * Γ), D γ`
  have hD_int_eq : (∫ γ in Icc Γ (2 * Γ), D γ) =
      ((∫ γ in Icc Γ (2 * Γ),
          ∑' ρ : zetaZeroConfig.carrier,
            (zetaZeroConfig.mult ρ : ℝ) *
              ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
                paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) +
        ∫ γ in Icc Γ (2 * Γ),
          ∑' ρ : zetaZeroConfig.carrier,
            (zetaZeroConfig.mult ρ : ℝ) *
              ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ)) -
                paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))‖ ^ 2 / 4) / 2 := by
    dsimp only [D]
    rw [integral_div, integral_add hc_sub.integrableOn_Icc hc_add.integrableOn_Icc]
  have hGloc_sub : (∑ q ∈ G_loc,
      (∫ γ in Icc Γ (2 * Γ),
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2) / 4) ≤
      (Real.pi / 2) * (∫ u, F₀ u ^ 2) *
        ∑ q ∈ G_loc, Real.exp (2 * A * (foldedRe q - 1 / 2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ => ?_
    have hpl := (integral_norm_paperFT_depthDiff_sq_le hF₀.continuous hF₀c hA0 hsupp
      (q.1 : ℂ) Γ (2 * Γ)).2.1
    rw [← foldedRe_sub_half_eq_abs q] at hpl
    linarith
  have hGloc_add : (∑ q ∈ G_loc,
      (∫ γ in Icc Γ (2 * Γ),
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) + (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) + (γ : ℂ))‖ ^ 2) / 4) ≤
      (Real.pi / 2) * (∫ u, F₀ u ^ 2) *
        ∑ q ∈ G_loc, Real.exp (2 * A * (foldedRe q - 1 / 2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ => ?_
    have hpl := (integral_norm_paperFT_depthDiff_add_sq_le hF₀.continuous hF₀c hA0 hsupp
      (q.1 : ℂ) Γ (2 * Γ)).1
    rw [← foldedRe_sub_half_eq_abs q] at hpl
    linarith
  have hshell := hthree Γ hΓ A hA0 hA G_loc hG_loc
  have hsum_le : ∑ q ∈ G_loc, Real.exp (2 * A * (foldedRe q - 1 / 2)) ≤ C_loc * Γ ^ (1 + η) := by
    have hmul := mul_le_mul_of_nonneg_left hshell hΓ0.le
    have h1 : Γ * ((1 / Γ) * ∑ q ∈ G_loc, Real.exp (2 * A * (foldedRe q - 1 / 2))) =
        ∑ q ∈ G_loc, Real.exp (2 * A * (foldedRe q - 1 / 2)) := by field_simp [hΓ0.ne']
    have h2 : Γ * (C_loc * Γ ^ η) = C_loc * Γ ^ (1 + η) := by
      calc Γ * (C_loc * Γ ^ η) = C_loc * (Γ ^ (1 : ℝ) * Γ ^ η) := by rw [Real.rpow_one]; ring
        _ = C_loc * Γ ^ (1 + η) := by rw [← Real.rpow_add hΓ0]
    linarith
  have hexpA : Real.exp A ≤ Γ ^ α := by
    calc Real.exp A ≤ Real.exp (α * Real.log Γ) := Real.exp_le_exp.mpr hA
      _ = Γ ^ α := by rw [Real.rpow_def_of_pos hΓ0, mul_comm]
  have hrem_le : (32 * reciprocalSquareWeightTotal / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 ≤
      32 * reciprocalSquareWeightTotal * Γ ^ (α - 1) * envelopeWindowNorm F₀ ^ 2 := by
    have hrpow : (1 / Γ) * Γ ^ α = Γ ^ (α - 1) := by
      rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_add hΓ0]; congr 1; ring
    calc (32 * reciprocalSquareWeightTotal / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2
        ≤ (32 * reciprocalSquareWeightTotal / Γ) * Γ ^ α * envelopeWindowNorm F₀ ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexpA
              (by positivity [reciprocalSquareWeightTotal_nonneg]))
            (sq_nonneg _)
      _ = 32 * reciprocalSquareWeightTotal * ((1 / Γ) * Γ ^ α) * envelopeWindowNorm F₀ ^ 2 := by
          ring
      _ = 32 * reciprocalSquareWeightTotal * Γ ^ (α - 1) * envelopeWindowNorm F₀ ^ 2 := by
          rw [hrpow]
  have hmass_nn : 0 ≤ ∫ u, F₀ u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hloc_le : (Real.pi / 2) * (∫ u, F₀ u ^ 2) *
      (∑ q ∈ G_loc, Real.exp (2 * A * (foldedRe q - 1 / 2))) ≤
      (Real.pi / 2) * C_loc * Γ ^ (1 + η) * (∫ u, F₀ u ^ 2) := by
    calc (Real.pi / 2) * (∫ u, F₀ u ^ 2) *
          (∑ q ∈ G_loc, Real.exp (2 * A * (foldedRe q - 1 / 2)))
        ≤ (Real.pi / 2) * (∫ u, F₀ u ^ 2) * (C_loc * Γ ^ (1 + η)) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = (Real.pi / 2) * C_loc * Γ ^ (1 + η) * (∫ u, F₀ u ^ 2) := by ring
  rw [le_div_iff₀ hM]
  linarith [hmarkov, hD_int_eq, hsub_int, hadd_int, hGloc_sub, hGloc_add, hloc_le, hrem_le]

/-! ## §4. Unconditional Logarithmic-Aperture Strict Positivity via RVM Core and Selberg Near-Line Density -/

/-- Pointwise hyperbolic-cosine lower bound `1 ≤ ((e^x + e^{-x}) / 2)²` for every `x : ℝ`. -/
theorem one_le_cosh_sq (x : ℝ) : 1 ≤ ((Real.exp x + Real.exp (-x)) / 2) ^ 2 := by
  have hexp : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hsq : 0 ≤ ((Real.exp x - Real.exp (-x)) / 2) ^ 2 := sq_nonneg _
  nlinarith

private theorem depthSumProfile_plancherel_and_cont {F₀ : ℝ → ℝ}
    (hF₀ : Continuous F₀) (hF₀c : HasCompactSupport F₀) (ρ : ℂ) :
    Continuous (fun γ : ℝ => ‖paperFT (depthSumProfile F₀ ρ) (-(γ : ℂ))‖ ^ 2) ∧
    Continuous (fun γ : ℝ => ‖paperFT (depthSumProfile F₀ ρ) (γ : ℂ)‖ ^ 2) ∧
    Integrable (fun γ : ℝ => ‖paperFT (depthSumProfile F₀ ρ) (-(γ : ℂ))‖ ^ 2) ∧
    2 * Real.pi * (∫ u, F₀ u ^ 2) ≤
      ∫ γ : ℝ, ‖paperFT (depthSumProfile F₀ ρ) (-(γ : ℂ))‖ ^ 2 := by
  let h := depthSumProfile F₀ ρ
  have hh_cont : Continuous h := by unfold h depthSumProfile; fun_prop
  have hh_comp : HasCompactSupport h := by
    unfold h depthSumProfile
    exact ((hF₀c.mul_right).comp_left Complex.ofReal_zero).mul_right
  have hh1 : Integrable h := hh_cont.integrable_of_hasCompactSupport hh_comp
  have hint_h2 : Integrable fun u : ℝ => ‖h u‖ ^ 2 :=
    (hh_cont.norm.pow 2).integrable_of_hasCompactSupport
      ((hh_comp.norm).comp_left (zero_pow two_ne_zero))
  have hh2 : MemLp h 2 :=
    (memLp_two_iff_integrable_sq_norm hh_cont.aestronglyMeasurable).mpr hint_h2
  have hft_cont : Continuous fun x : ℝ => paperFT h (x : ℂ) := by
    have hint_h : Integrable fun u : ℝ => ‖h u‖ := hh1.norm
    rw [continuous_iff_continuousAt]
    intro x₀
    refine continuousAt_of_dominated (bound := fun u : ℝ => ‖h u‖)
      (Eventually.of_forall fun x => (hh_cont.mul (by fun_prop)).aestronglyMeasurable)
      (Eventually.of_forall fun x => Eventually.of_forall fun u => ?_)
      hint_h (Eventually.of_forall fun u => by fun_prop)
    have hexp1 : ‖Complex.exp (Complex.I * (x : ℂ) * (u : ℂ))‖ = 1 := by
      have : Complex.I * (x : ℂ) * (u : ℂ) = ((x * u : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, hexp1, mul_one]
  have heq_m : (fun γ : ℝ => ‖paperFT h (-(γ : ℂ))‖ ^ 2) =
      fun γ : ℝ => ‖paperFT h ((-γ : ℝ) : ℂ)‖ ^ 2 := by funext γ; simp
  have hc_minus : Continuous fun γ : ℝ => ‖paperFT h (-(γ : ℂ))‖ ^ 2 := by
    rw [heq_m]; exact ((hft_cont.comp continuous_neg).norm).pow 2
  have hc_plus : Continuous fun γ : ℝ => ‖paperFT h (γ : ℂ)‖ ^ 2 := (hft_cont.norm).pow 2
  have hint_pos : Integrable fun x : ℝ => ‖paperFT h (x : ℂ)‖ ^ 2 := by
    have hfun : (fun x : ℝ => ‖paperFT h (x : ℂ)‖ ^ 2) =
        fun x => (fun ξ : ℝ => ‖FourierTransform.fourier h ξ‖ ^ 2) (x / (-(2 * Real.pi))) := by
      funext x; rw [paperFT_ofReal_eq_fourier, neg_div, ← div_neg]
    rw [hfun]
    exact (GaloisForLFunctions.RHTower.integrable_norm_sq_fourier hh1 hh2).comp_div
      (by linarith [Real.pi_pos])
  have hint_minus : Integrable fun γ : ℝ => ‖paperFT h (-(γ : ℂ))‖ ^ 2 := by
    rw [heq_m]; exact hint_pos.comp_neg
  have hwhole : (∫ γ : ℝ, ‖paperFT h (-(γ : ℂ))‖ ^ 2) = 2 * Real.pi * ∫ u : ℝ, ‖h u‖ ^ 2 := by
    rw [heq_m, integral_neg_eq_self (fun x : ℝ => ‖paperFT h (x : ℂ)‖ ^ 2)]
    exact RHTower.KernelStrip.integral_norm_sq_paperFT_of_memLp hh1 hh2
  have hint_F₀2 : Integrable fun u : ℝ => F₀ u ^ 2 :=
    (hF₀.pow 2).integrable_of_hasCompactSupport (hF₀c.comp_left (zero_pow two_ne_zero))
  have hL2_ge : (∫ u : ℝ, F₀ u ^ 2) ≤ ∫ u : ℝ, ‖h u‖ ^ 2 := by
    refine integral_mono hint_F₀2 hint_h2 fun u => ?_
    dsimp [h, depthSumProfile]
    have hexp_norm : ‖Complex.exp (Complex.I * (ρ.im : ℂ) * (u : ℂ))‖ = 1 := by
      have : Complex.I * (ρ.im : ℂ) * (u : ℂ) = ((ρ.im * u : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, hexp_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
    exact le_mul_of_one_le_right (sq_nonneg _) (one_le_cosh_sq ((ρ.re - 1 / 2) * u))
  refine ⟨hc_minus, hc_plus, hint_minus, ?_⟩
  rw [hwhole]
  exact mul_le_mul_of_nonneg_left hL2_ge (by positivity)

private theorem norm_paperFT_depthSumProfile_sq_le_lorentz {F₀ : ℝ → ℝ}
    (hF₀ : ContDiff ℝ 2 F₀) (hF₀c : HasCompactSupport F₀)
    {A : ℝ} (hA : 0 ≤ A) (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0)
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (ω : ℝ) :
    ‖paperFT (depthSumProfile F₀ ρ) (-(ω : ℂ))‖ ^ 2 ≤
      Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / (1 + (ρ.im - ω) ^ 2) ^ 2) := by
  rw [paperFT_depthSumProfile_eq hF₀.continuous hF₀c ρ ω]
  have him1 : |(gammaOf ρ - (ω : ℂ)).im| ≤ 1 / 2 := by
    rw [gammaOf_sub_real]; simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_sub, abs_neg]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have him2 : |(conj (gammaOf ρ) - (ω : ℂ)).im| ≤ 1 / 2 := by
    rw [conj_gammaOf_sub_real]; simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hre1 : (gammaOf ρ - (ω : ℂ)).re = ρ.im - ω := by rw [gammaOf_sub_real]; simp
  have hre2 : (conj (gammaOf ρ) - (ω : ℂ)).re = ρ.im - ω := by rw [conj_gammaOf_sub_real]; simp
  have hb1 := norm_paperFT_symm_le hF₀ hF₀c hA hsupp (gammaOf ρ - (ω : ℂ))
  have hb2 := norm_paperFT_symm_le hF₀ hF₀c hA hsupp (conj (gammaOf ρ) - (ω : ℂ))
  rw [hre1] at hb1; rw [hre2] at hb2
  have hexp1 : Real.exp (A * |(gammaOf ρ - (ω : ℂ)).im|) ≤ Real.exp (A / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hexp2 : Real.exp (A * |(conj (gammaOf ρ) - (ω : ℂ)).im|) ≤ Real.exp (A / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have htri : ‖(paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (ω : ℂ)) +
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (ω : ℂ))) / 2‖ ≤
      Real.exp (A / 2) * envelopeWindowNorm F₀ / (1 + (ρ.im - ω) ^ 2) := by
    rw [norm_div, Complex.norm_ofNat]
    have h1 := hb1.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hexp1 (envelopeWindowNorm_nonneg F₀)) (by positivity))
    have h2 := hb2.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hexp2 (envelopeWindowNorm_nonneg F₀)) (by positivity))
    have hadd := (norm_add_le
      (paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (ω : ℂ)))
      (paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (ω : ℂ)))).trans (add_le_add h1 h2)
    linarith
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hexpA : Real.exp (A / 2) ^ 2 = Real.exp A := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  calc ‖(paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (ω : ℂ)) +
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (ω : ℂ))) / 2‖ ^ 2
      ≤ (Real.exp (A / 2) * envelopeWindowNorm F₀ / (1 + (ρ.im - ω) ^ 2)) ^ 2 := hsq
    _ = Real.exp (A / 2) ^ 2 * envelopeWindowNorm F₀ ^ 2 * (1 / (1 + (ρ.im - ω) ^ 2) ^ 2) := by
        rw [div_pow, mul_pow, mul_one_div]
    _ = Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / (1 + (ρ.im - ω) ^ 2) ^ 2) := by rw [hexpA]

/-- Per-zero core lower bound on `∫_{Icc Γ (2Γ)} ‖paperFT (depthSumProfile F₀ ρ) (-γ)‖²` and upper
bound on `∫_{Icc Γ (2Γ)} ‖paperFT (depthSumProfile F₀ ρ) γ‖²` for every zero `ρ` in the open strip
with interior ordinate `5Γ/4 ≤ Im ρ ≤ 3Γ/2` (`Γ ≥ 1`), uniformly in `Re ρ ∈ (0, 1)`. -/
theorem integral_Icc_norm_paperFT_depthSum_sq_bounds {F₀ : ℝ → ℝ}
    (hF₀ : ContDiff ℝ 2 F₀) (hF₀c : HasCompactSupport F₀)
    {Γ A : ℝ} (hΓ : 1 ≤ Γ) (hA : 0 ≤ A) (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0)
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hρ_im1 : 5 * Γ / 4 ≤ ρ.im) (hρ_im2 : ρ.im ≤ 3 * Γ / 2) :
    Continuous (fun γ : ℝ => ‖paperFT (depthSumProfile F₀ ρ) (-(γ : ℂ))‖ ^ 2) ∧
    Continuous (fun γ : ℝ => ‖paperFT (depthSumProfile F₀ ρ) (γ : ℂ)‖ ^ 2) ∧
    2 * Real.pi * (∫ u, F₀ u ^ 2) -
        (16 * Real.pi / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2 ≤
      (∫ γ in Icc Γ (2 * Γ), ‖paperFT (depthSumProfile F₀ ρ) (-(γ : ℂ))‖ ^ 2) ∧
    (∫ γ in Icc Γ (2 * Γ), ‖paperFT (depthSumProfile F₀ ρ) (γ : ℂ)‖ ^ 2) ≤
      (Real.pi / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2 := by
  obtain ⟨hc_minus, hc_plus, hint_minus, hpl_ge⟩ :=
    depthSumProfile_plancherel_and_cont hF₀.continuous hF₀c ρ
  have hsum_lor := norm_paperFT_depthSumProfile_sq_le_lorentz hF₀ hF₀c hA hsupp hρ0 hρ1
  -- Exterior integral on `(Icc Γ (2 * Γ))ᶜ`
  have hint_lor_sub : Integrable fun γ : ℝ => 1 / (1 + (ρ.im - γ) ^ 2) := by
    have heq : (fun γ : ℝ => 1 / (1 + (ρ.im - γ) ^ 2)) = fun γ : ℝ => (1 + (γ - ρ.im) ^ 2)⁻¹ := by
      funext γ; simp only [one_div]; congr 2; ring
    rw [heq]
    exact integrable_inv_one_add_sq.comp_sub_right ρ.im
  have hint_lor_sub_val : (∫ γ : ℝ, 1 / (1 + (ρ.im - γ) ^ 2)) = Real.pi := by
    have heq : (fun γ : ℝ => 1 / (1 + (ρ.im - γ) ^ 2)) = fun γ : ℝ => (1 + (γ - ρ.im) ^ 2)⁻¹ := by
      funext γ; simp only [one_div]; congr 2; ring
    rw [heq, integral_sub_right_eq_self (fun u : ℝ => (1 + u ^ 2)⁻¹) ρ.im]
    exact integral_univ_inv_one_add_sq
  have hext_le : (∫ γ in (Icc Γ (2 * Γ))ᶜ, ‖paperFT (depthSumProfile F₀ ρ) (-(γ : ℂ))‖ ^ 2) ≤
      (16 * Real.pi / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2 := by
    have hpt_ext : ∀ γ ∈ (Icc Γ (2 * Γ))ᶜ,
        ‖paperFT (depthSumProfile F₀ ρ) (-(γ : ℂ))‖ ^ 2 ≤
          Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 / Γ ^ 2) *
            (1 / (1 + (ρ.im - γ) ^ 2)) := fun γ hγ => by
      have hsq_gap : Γ ^ 2 / 16 ≤ (ρ.im - γ) ^ 2 := by
        rw [Set.mem_compl_iff, Set.mem_Icc, not_and_or] at hγ
        rcases hγ with h1 | h2
        · have hd : Γ / 4 ≤ ρ.im - γ := by linarith [not_le.mp h1]
          have := pow_le_pow_left₀ (by positivity) hd 2
          linarith
        · have hd : Γ / 4 ≤ γ - ρ.im := by linarith [not_le.mp h2]
          have := pow_le_pow_left₀ (by positivity) hd 2
          linarith [show (ρ.im - γ) ^ 2 = (γ - ρ.im) ^ 2 by ring]
      have hinv16 : 1 / (1 + (ρ.im - γ) ^ 2) ≤ 16 / Γ ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      calc ‖paperFT (depthSumProfile F₀ ρ) (-(γ : ℂ))‖ ^ 2
          ≤ Real.exp A * envelopeWindowNorm F₀ ^ 2 *
              ((1 / (1 + (ρ.im - γ) ^ 2)) * (1 / (1 + (ρ.im - γ) ^ 2))) := by
            simpa [sq] using hsum_lor γ
        _ ≤ Real.exp A * envelopeWindowNorm F₀ ^ 2 *
              ((16 / Γ ^ 2) * (1 / (1 + (ρ.im - γ) ^ 2))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hinv16 (by positivity)) (by positivity)
        _ = Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 / Γ ^ 2) *
              (1 / (1 + (ρ.im - γ) ^ 2)) := by ring
    have hint_maj := hint_lor_sub.const_mul
      (Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 / Γ ^ 2))
    calc (∫ γ in (Icc Γ (2 * Γ))ᶜ, ‖paperFT (depthSumProfile F₀ ρ) (-(γ : ℂ))‖ ^ 2)
        ≤ ∫ γ in (Icc Γ (2 * Γ))ᶜ,
            Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 / Γ ^ 2) *
              (1 / (1 + (ρ.im - γ) ^ 2)) :=
          setIntegral_mono_on hint_minus.integrableOn hint_maj.integrableOn
            measurableSet_Icc.compl hpt_ext
      _ ≤ ∫ γ : ℝ, Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 / Γ ^ 2) *
            (1 / (1 + (ρ.im - γ) ^ 2)) :=
          setIntegral_le_integral hint_maj (Eventually.of_forall fun _ => by positivity)
      _ = Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 / Γ ^ 2) * Real.pi := by
          rw [integral_const_mul, hint_lor_sub_val]
      _ = (16 * Real.pi / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2 := by ring
  have hsplit := integral_add_compl (s := Icc Γ (2 * Γ)) measurableSet_Icc hint_minus
  have hplus_le : (∫ γ in Icc Γ (2 * Γ), ‖paperFT (depthSumProfile F₀ ρ) (γ : ℂ)‖ ^ 2) ≤
      (Real.pi / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2 := by
    have hpt_plus : ∀ γ ∈ Icc Γ (2 * Γ),
        ‖paperFT (depthSumProfile F₀ ρ) (γ : ℂ)‖ ^ 2 ≤
          Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / Γ ^ 2) *
            (1 / (1 + (ρ.im + γ) ^ 2)) := fun γ hγ => by
      have h1 : ‖paperFT (depthSumProfile F₀ ρ) (γ : ℂ)‖ ^ 2 ≤
          Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / (1 + (ρ.im + γ) ^ 2) ^ 2) := by
        simpa [sub_neg_eq_add] using hsum_lor (-γ)
      have hsq_gap : Γ ^ 2 ≤ (ρ.im + γ) ^ 2 := by
        have hd : Γ ≤ ρ.im + γ := by linarith [hγ.1]
        exact pow_le_pow_left₀ (by positivity) hd 2
      have hinv1 : 1 / (1 + (ρ.im + γ) ^ 2) ≤ 1 / Γ ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      calc ‖paperFT (depthSumProfile F₀ ρ) (γ : ℂ)‖ ^ 2
          ≤ Real.exp A * envelopeWindowNorm F₀ ^ 2 *
              ((1 / (1 + (ρ.im + γ) ^ 2)) * (1 / (1 + (ρ.im + γ) ^ 2))) := by
            simpa [sq] using h1
        _ ≤ Real.exp A * envelopeWindowNorm F₀ ^ 2 *
              ((1 / Γ ^ 2) * (1 / (1 + (ρ.im + γ) ^ 2))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hinv1 (by positivity)) (by positivity)
        _ = Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / Γ ^ 2) *
              (1 / (1 + (ρ.im + γ) ^ 2)) := by ring
    have hint_lor_add : IntegrableOn (fun γ : ℝ => 1 / (1 + (ρ.im + γ) ^ 2)) (Icc Γ (2 * Γ)) :=
      (continuous_const.div (by fun_prop) (fun _ => by positivity)).integrableOn_Icc
    calc (∫ γ in Icc Γ (2 * Γ), ‖paperFT (depthSumProfile F₀ ρ) (γ : ℂ)‖ ^ 2)
        ≤ ∫ γ in Icc Γ (2 * Γ),
            Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / Γ ^ 2) *
              (1 / (1 + (ρ.im + γ) ^ 2)) :=
          setIntegral_mono_on hc_plus.integrableOn_Icc
            (hint_lor_add.const_mul _) measurableSet_Icc hpt_plus
      _ = Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / Γ ^ 2) *
            ∫ γ in Icc Γ (2 * Γ), 1 / (1 + (ρ.im + γ) ^ 2) :=
          integral_const_mul _ _
      _ ≤ Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / Γ ^ 2) * Real.pi :=
          mul_le_mul_of_nonneg_left
            (integral_Icc_inv_one_add_sq_add_le_pi Γ (2 * Γ) ρ.im) (by positivity)
      _ = (Real.pi / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2 := by ring
  refine ⟨hc_minus, hc_plus, ?_, hplus_le⟩
  linarith [hsplit, hext_le, hpl_ge]

/-- Riemann–von Mangoldt multiplicity lower and upper bounds on the interior core window
`xiSupportsWindow (5 * Γ / 4) (3 * Γ / 2)` (`5Γ/4 < Im ρ ≤ 3Γ/2`). -/
theorem exists_sum_mult_xiSupportsWindow_core_bounds :
    ∃ Γ_rvm : ℝ, 16 ≤ Γ_rvm ∧
      ∀ Γ : ℝ, Γ_rvm ≤ Γ →
        (1 / (16 * Real.pi)) * Γ * Real.log Γ ≤
          (∑ ρ ∈ xiSupportsWindow (5 * Γ / 4) (3 * Γ / 2), (xiSupportMultiplicity ρ : ℝ)) ∧
        (∑ ρ ∈ xiSupportsWindow (5 * Γ / 4) (3 * Γ / 2), (xiSupportMultiplicity ρ : ℝ)) ≤
          (2 / Real.pi) * Γ * Real.log Γ := by
  have hπ : 0 < Real.pi := Real.pi_pos
  obtain ⟨T_rvm, hT_rvm, hN⟩ := exists_xiZeroCount_close (1 / (64 * Real.pi)) (by positivity)
  refine ⟨max 16 T_rvm, le_max_left _ _, fun Γ hΓ => ?_⟩
  have hΓ16 : 16 ≤ Γ := (le_max_left _ _).trans hΓ
  have hΓ_T : T_rvm ≤ Γ := (le_max_right _ _).trans hΓ
  have hΓ0 : 0 < Γ := by linarith
  have hlogΓ_pos : 0 < Real.log Γ := Real.log_pos (by linarith)
  have h1 : T_rvm ≤ 5 * Γ / 4 := by linarith
  have h2 : T_rvm ≤ 3 * Γ / 2 := by linarith
  have hN1 := hN (5 * Γ / 4) h1
  have hN2 := hN (3 * Γ / 2) h2
  have hN1_upper : (xiZeroCount (5 * Γ / 4) : ℝ) ≤
      (33 / (64 * Real.pi)) * ((5 * Γ / 4) * Real.log (5 * Γ / 4)) := by
    have := (abs_le.mp hN1).2
    have heq : (1 / (2 * Real.pi)) * ((5 * Γ / 4) * Real.log (5 * Γ / 4)) +
        (1 / (64 * Real.pi)) * ((5 * Γ / 4) * Real.log (5 * Γ / 4)) =
        (33 / (64 * Real.pi)) * ((5 * Γ / 4) * Real.log (5 * Γ / 4)) := by ring
    linarith
  have hN2_lower : (31 / (64 * Real.pi)) * ((3 * Γ / 2) * Real.log (3 * Γ / 2)) ≤
      (xiZeroCount (3 * Γ / 2) : ℝ) := by
    have := (abs_le.mp hN2).1
    have heq : (1 / (2 * Real.pi)) * ((3 * Γ / 2) * Real.log (3 * Γ / 2)) -
        (1 / (64 * Real.pi)) * ((3 * Γ / 2) * Real.log (3 * Γ / 2)) =
        (31 / (64 * Real.pi)) * ((3 * Γ / 2) * Real.log (3 * Γ / 2)) := by ring
    linarith
  have hN2_upper : (xiZeroCount (3 * Γ / 2) : ℝ) ≤
      (33 / (64 * Real.pi)) * ((3 * Γ / 2) * Real.log (3 * Γ / 2)) := by
    have := (abs_le.mp hN2).2
    have heq : (1 / (2 * Real.pi)) * ((3 * Γ / 2) * Real.log (3 * Γ / 2)) +
        (1 / (64 * Real.pi)) * ((3 * Γ / 2) * Real.log (3 * Γ / 2)) =
        (33 / (64 * Real.pi)) * ((3 * Γ / 2) * Real.log (3 * Γ / 2)) := by ring
    linarith
  have hwin := sum_mult_xiSupportsWindow (by positivity : 0 ≤ 5 * Γ / 4)
    (by linarith : 5 * Γ / 4 ≤ 3 * Γ / 2)
  rw [hwin]
  have hlog_mono1 : Real.log Γ ≤ Real.log (5 * Γ / 4) :=
    Real.log_le_log hΓ0 (by linarith)
  have hlog_mono2 : Real.log (5 * Γ / 4) ≤ Real.log (3 * Γ / 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hN2_lower' : (93 / (128 * Real.pi)) * Γ * Real.log (5 * Γ / 4) ≤
      (xiZeroCount (3 * Γ / 2) : ℝ) := by
    calc (93 / (128 * Real.pi)) * Γ * Real.log (5 * Γ / 4)
        = (31 / (64 * Real.pi)) * (3 * Γ / 2) * Real.log (5 * Γ / 4) := by ring
      _ ≤ (31 / (64 * Real.pi)) * (3 * Γ / 2) * Real.log (3 * Γ / 2) :=
          mul_le_mul_of_nonneg_left hlog_mono2 (by positivity)
      _ = (31 / (64 * Real.pi)) * ((3 * Γ / 2) * Real.log (3 * Γ / 2)) := by ring
      _ ≤ (xiZeroCount (3 * Γ / 2) : ℝ) := hN2_lower
  have hN1_nn : 0 ≤ (xiZeroCount (5 * Γ / 4) : ℝ) := by
    have heq := xiZeroCount_eq_pos_sum (by positivity : 0 ≤ 5 * Γ / 4)
    have hnn : (0 : ℤ) ≤ xiZeroCount (5 * Γ / 4) := by
      rw [heq]; exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    exact_mod_cast hnn
  have hlog_sq : Real.log (3 * Γ / 2) ≤ 2 * Real.log Γ := by
    have hle : 3 * Γ / 2 ≤ Γ ^ 2 := by nlinarith
    calc Real.log (3 * Γ / 2) ≤ Real.log (Γ ^ 2) := Real.log_le_log (by positivity) hle
      _ = 2 * Real.log Γ := by rw [Real.log_pow]; norm_num
  refine ⟨?_, ?_⟩
  · have hdiff : (21 / (256 * Real.pi)) * Γ * Real.log (5 * Γ / 4) ≤
        (xiZeroCount (3 * Γ / 2) : ℝ) - (xiZeroCount (5 * Γ / 4) : ℝ) := by
      have hsub_eq : (93 / (128 * Real.pi)) * Γ * Real.log (5 * Γ / 4) -
          (33 / (64 * Real.pi)) * ((5 * Γ / 4) * Real.log (5 * Γ / 4)) =
          (21 / (256 * Real.pi)) * Γ * Real.log (5 * Γ / 4) := by
        field_simp [hπ.ne']; ring
      linarith [hN2_lower', hN1_upper, hsub_eq]
    calc (1 / (16 * Real.pi)) * Γ * Real.log Γ
        ≤ (21 / (256 * Real.pi)) * Γ * Real.log Γ := by
          have hdiff_c : (21 / (256 * Real.pi)) * Γ * Real.log Γ -
              (1 / (16 * Real.pi)) * Γ * Real.log Γ =
              (5 / (256 * Real.pi)) * Γ * Real.log Γ := by
            field_simp [hπ.ne']; ring
          have hpos_c : 0 ≤ (5 / (256 * Real.pi)) * Γ * Real.log Γ := by positivity
          linarith
      _ ≤ (21 / (256 * Real.pi)) * Γ * Real.log (5 * Γ / 4) :=
          mul_le_mul_of_nonneg_left hlog_mono1 (by positivity)
      _ ≤ (xiZeroCount (3 * Γ / 2) : ℝ) - (xiZeroCount (5 * Γ / 4) : ℝ) := hdiff
  · calc (xiZeroCount (3 * Γ / 2) : ℝ) - (xiZeroCount (5 * Γ / 4) : ℝ)
        ≤ (xiZeroCount (3 * Γ / 2) : ℝ) := by linarith
      _ ≤ (33 / (64 * Real.pi)) * (3 * Γ / 2) * Real.log (3 * Γ / 2) := by
          linarith [hN2_upper]
      _ ≤ (33 / (64 * Real.pi)) * (3 * Γ / 2) * (2 * Real.log Γ) :=
          mul_le_mul_of_nonneg_left hlog_sq (by positivity)
      _ = (99 / (64 * Real.pi)) * Γ * Real.log Γ := by ring
      _ ≤ (2 / Real.pi) * Γ * Real.log Γ := by
          have hdiff_c2 : (2 / Real.pi) * Γ * Real.log Γ -
              (99 / (64 * Real.pi)) * Γ * Real.log Γ =
              (29 / (64 * Real.pi)) * Γ * Real.log Γ := by
            field_simp [hπ.ne']; ring
          have hpos_c2 : 0 ≤ (29 / (64 * Real.pi)) * Γ * Real.log Γ := by positivity
          linarith

/-- 4-quadrant `foldedRe`-invariant symmetry + multiplicity-preserving bridge to `windowZeros T₁ T₂`:
for any nonnegative weight `g : ℝ → ℝ`, `0 < T₁ ≤ T₂`, `0 < v₀`, and any finite set `G_w` of zero
copies in `T₁ ≤ |Im ρ_q| ≤ T₂` with `1/2 + v₀ < foldedRe q`,
`∑ q ∈ G_w, g (foldedRe q) ≤ 4 * ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1/2 + v₀ < w.re), RHTower.zeroMult w * g w.re`. -/
theorem sum_foldedRe_le_four_mul_windowZeros {g : ℝ → ℝ} (hg : ∀ y, 0 ≤ g y)
    {T₁ T₂ v₀ : ℝ} (hT₁ : 0 < T₁) (hT12 : T₁ ≤ T₂) (hv₀ : 0 < v₀)
    (G_w : Finset XiZeroCopy)
    (hG_w : ∀ q ∈ G_w, 1 / 2 + v₀ < foldedRe q ∧ T₁ ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ T₂) :
    (∑ q ∈ G_w, g (foldedRe q)) ≤
      4 * ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + v₀ < w.re),
        RHTower.zeroMult w * g w.re := by
  classical
  let W_ur : Finset XiDivisorSupport :=
    (xiSupportsPos T₂).filter (fun ρ => 1 / 2 + v₀ < (ρ : ℂ).re ∧ T₁ ≤ (ρ : ℂ).im)
  let U_ur : Finset XiZeroCopy := xiCopiesOf W_ur
  have hmem_U : ∀ q : XiZeroCopy,
      q ∈ U_ur ↔ 1 / 2 + v₀ < (q.1 : ℂ).re ∧ T₁ ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ T₂ := fun q => by
    unfold U_ur xiCopiesOf W_ur
    rw [Finset.mem_sigma]
    simp only [Finset.mem_univ, and_true, Finset.mem_filter, mem_xiSupportsPos]
    constructor
    · rintro ⟨⟨habs, him0⟩, hre, him1⟩
      rw [abs_of_pos him0] at habs
      exact ⟨hre, him1, habs⟩
    · rintro ⟨hre, him1, him2⟩
      have him0 : 0 < (q.1 : ℂ).im := lt_of_lt_of_le hT₁ him1
      exact ⟨⟨by rw [abs_of_pos him0]; exact him2, him0⟩, hre, him1⟩
  -- For any `foldedRe`-preserving equivalence `e`, the filtered sum over `G_w` is `≤ ∑ x ∈ U_ur`
  have hequiv_le : ∀ (e : XiZeroCopy ≃ XiZeroCopy),
      (∀ q, foldedRe (e q) = foldedRe q) →
      (∑ q ∈ G_w, if e q ∈ U_ur then g (foldedRe q) else 0) ≤
        ∑ x ∈ U_ur, g (foldedRe x) := fun e hinv => by
    rw [← Finset.sum_filter]
    have hmap_sub : (G_w.filter (fun q => e q ∈ U_ur)).map e.toEmbedding ⊆ U_ur := by
      intro x hx
      rcases Finset.mem_map.mp hx with ⟨q, hq, rfl⟩
      exact (Finset.mem_filter.mp hq).2
    calc (∑ q ∈ G_w.filter (fun q => e q ∈ U_ur), g (foldedRe q))
        = ∑ q ∈ G_w.filter (fun q => e q ∈ U_ur), g (foldedRe (e.toEmbedding q)) :=
          Finset.sum_congr rfl fun q _ => congrArg g (hinv q).symm
      _ = ∑ x ∈ (G_w.filter (fun q => e q ∈ U_ur)).map e.toEmbedding, g (foldedRe x) :=
          (Finset.sum_map (G_w.filter (fun q => e q ∈ U_ur)) e.toEmbedding
            (fun x => g (foldedRe x))).symm
      _ ≤ ∑ x ∈ U_ur, g (foldedRe x) :=
          Finset.sum_le_sum_of_subset_of_nonneg hmap_sub fun x _ _ => hg _
  have hf_id : ∀ q, foldedRe (Equiv.refl XiZeroCopy q) = foldedRe q := fun _ => rfl
  have hf_conj : ∀ q, foldedRe (xiZeroCopyConjEquiv q) = foldedRe q := fun q => by
    have hc : ((xiZeroCopyConjEquiv q).1 : ℂ) = conj (q.1 : ℂ) := rfl
    simp [foldedRe, hc]
  have hf_refl : ∀ q, foldedRe (xiZeroCopyReflectEquiv q) = foldedRe q := fun q => by
    have hr : ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) := rfl
    simp only [foldedRe, hr, Complex.sub_re, Complex.one_re, sub_sub_cancel]
    exact max_comm _ _
  have hf_cr : ∀ q, foldedRe ((xiZeroCopyConjEquiv.trans xiZeroCopyReflectEquiv) q) = foldedRe q :=
    fun q => (hf_refl (xiZeroCopyConjEquiv q)).trans (hf_conj q)
  have hcover_pt : ∀ q ∈ G_w, g (foldedRe q) ≤
      (if Equiv.refl XiZeroCopy q ∈ U_ur then g (foldedRe q) else 0) +
      (if xiZeroCopyConjEquiv q ∈ U_ur then g (foldedRe q) else 0) +
      (if (xiZeroCopyConjEquiv.trans xiZeroCopyReflectEquiv) q ∈ U_ur then g (foldedRe q) else 0) +
      (if xiZeroCopyReflectEquiv q ∈ U_ur then g (foldedRe q) else 0) := fun q hq => by
    obtain ⟨hσ, h1, h2⟩ := hG_w q hq
    have hc : ((xiZeroCopyConjEquiv q).1 : ℂ) = conj (q.1 : ℂ) := rfl
    have hr : ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) := rfl
    have hcr : (((xiZeroCopyConjEquiv.trans xiZeroCopyReflectEquiv) q).1 : ℂ) =
        1 - conj (q.1 : ℂ) := rfl
    have hnn0 := hg (foldedRe q)
    have h0a : 0 ≤ if Equiv.refl XiZeroCopy q ∈ U_ur then g (foldedRe q) else 0 := by
      split_ifs <;> linarith
    have h0b : 0 ≤ if xiZeroCopyConjEquiv q ∈ U_ur then g (foldedRe q) else 0 := by
      split_ifs <;> linarith
    have h0c : 0 ≤ if (xiZeroCopyConjEquiv.trans xiZeroCopyReflectEquiv) q ∈ U_ur then
        g (foldedRe q) else 0 := by split_ifs <;> linarith
    have h0d : 0 ≤ if xiZeroCopyReflectEquiv q ∈ U_ur then g (foldedRe q) else 0 := by
      split_ifs <;> linarith
    rw [foldedRe, lt_max_iff] at hσ
    rcases hσ with hσ | hσ <;> rcases le_total 0 ((q.1 : ℂ).im) with hγ | hγ
    · rw [abs_of_nonneg hγ] at h1 h2
      have hm : Equiv.refl XiZeroCopy q ∈ U_ur := (hmem_U _).mpr ⟨hσ, h1, h2⟩
      rw [if_pos hm]; linarith
    · rw [abs_of_nonpos hγ] at h1 h2
      have hm : xiZeroCopyConjEquiv q ∈ U_ur := by
        rw [hmem_U, hc, Complex.conj_re, Complex.conj_im]
        exact ⟨hσ, h1, h2⟩
      rw [if_pos hm]; linarith
    · rw [abs_of_nonneg hγ] at h1 h2
      have hm : (xiZeroCopyConjEquiv.trans xiZeroCopyReflectEquiv) q ∈ U_ur := by
        rw [hmem_U, hcr, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
          Complex.one_re, Complex.one_im]
        exact ⟨hσ, by linarith, by linarith⟩
      rw [if_pos hm]; linarith
    · rw [abs_of_nonpos hγ] at h1 h2
      have hm : xiZeroCopyReflectEquiv q ∈ U_ur := by
        rw [hmem_U, hr, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
        exact ⟨hσ, by linarith, by linarith⟩
      rw [if_pos hm]; linarith
  have h4_le : (∑ q ∈ G_w, g (foldedRe q)) ≤ 4 * ∑ x ∈ U_ur, g (foldedRe x) := by
    have hs := Finset.sum_le_sum hcover_pt
    simp only [Finset.sum_add_distrib] at hs
    linarith [hequiv_le _ hf_id, hequiv_le _ hf_conj, hequiv_le _ hf_cr, hequiv_le _ hf_refl]
  -- Evaluate `∑ x ∈ U_ur, g (foldedRe x)` via `xiCopiesOf W_ur`
  have hU_eq : (∑ x ∈ U_ur, g (foldedRe x)) =
      ∑ ρ ∈ W_ur, (xiSupportMultiplicity ρ : ℝ) * g (ρ : ℂ).re := by
    unfold U_ur xiCopiesOf
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    have hre_gt : 1 / 2 + v₀ < (ρ : ℂ).re := ((Finset.mem_filter.mp hρ).2).1
    have hfold_ρ : ∀ i : Fin (xiSupportMultiplicity ρ),
        foldedRe ⟨ρ, i⟩ = (ρ : ℂ).re := fun _ =>
      max_eq_left (by linarith)
    simp only [hfold_ρ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rfl
  -- Inject `W_ur` into `(windowZeros T₁ T₂).filter (fun w => 1 / 2 + v₀ < w.re)` via `ρ ↦ (ρ : ℂ)`
  let embC : XiDivisorSupport ↪ ℂ := ⟨fun ρ => (ρ : ℂ), fun _ _ h => Subtype.ext h⟩
  have hmap_win : W_ur.map embC ⊆
      (windowZeros T₁ T₂).filter (fun w => 1 / 2 + v₀ < w.re) := by
    intro z hz
    rcases Finset.mem_map.mp hz with ⟨ρ, hρ, rfl⟩
    have hρ_filt := Finset.mem_filter.mp hρ
    have hρ_pos := (mem_xiSupportsPos.mp hρ_filt.1)
    rw [abs_of_pos hρ_pos.2] at hρ_pos
    have hstrip := (xiDivisorZetaCarrierEquiv ρ).2
    have hmem_strip : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := (xiDivisorZetaCarrierEquiv ρ).2.2
    rw [Finset.mem_filter, mem_windowZeros_iff hT₁ hT12]
    dsimp [embC]
    refine ⟨⟨?_, hstrip.1⟩, hρ_filt.2.1⟩
    rw [Complex.mem_reProdIm, uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 15 / 2), uIcc_of_le hT12]
    exact ⟨⟨by linarith [hρ_filt.2.1], by linarith [hmem_strip.2]⟩, ⟨hρ_filt.2.2, hρ_pos.1⟩⟩
  have hW_le : (∑ ρ ∈ W_ur, (xiSupportMultiplicity ρ : ℝ) * g (ρ : ℂ).re) ≤
      ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + v₀ < w.re),
        RHTower.zeroMult w * g w.re := by
    have hmult_eq : ∀ ρ ∈ W_ur,
        (xiSupportMultiplicity ρ : ℝ) * g (ρ : ℂ).re =
          RHTower.zeroMult (embC ρ) * g (embC ρ).re := fun ρ hρ => by
      have him1 : T₁ ≤ (ρ : ℂ).im := ((Finset.mem_filter.mp hρ).2).2
      have hne1 : (ρ : ℂ) ≠ 1 := fun h => by
        have := congrArg Complex.im h; simp at this; linarith
      have hmem_strip : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := (xiDivisorZetaCarrierEquiv ρ).2.2
      congr 1
      dsimp [embC]
      rw [RHTower.zeroMult_eq_zeta_order hne1,
        ← xi_analyticOrderAt_eq_riemannZeta_of_mem_strip hmem_strip,
        ← xiSupportMultiplicity_eq_analyticOrderAt_toNat]
    calc (∑ ρ ∈ W_ur, (xiSupportMultiplicity ρ : ℝ) * g (ρ : ℂ).re)
        = ∑ ρ ∈ W_ur, RHTower.zeroMult (embC ρ) * g (embC ρ).re :=
          Finset.sum_congr rfl hmult_eq
      _ = ∑ w ∈ W_ur.map embC, RHTower.zeroMult w * g w.re :=
          (Finset.sum_map W_ur embC (fun w => RHTower.zeroMult w * g w.re)).symm
      _ ≤ ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + v₀ < w.re),
            RHTower.zeroMult w * g w.re :=
          Finset.sum_le_sum_of_subset_of_nonneg hmap_win fun w _ _ =>
            mul_nonneg (by unfold RHTower.zeroMult; positivity) (hg _)
  linarith [h4_le, hU_eq, hW_le]

/-- Pure zero-side Plancherel weight per zero copy `q` at aperture `A`: minimum of the global
exponential bound `(π/2) e^{2A(foldedRe q - 1/2)}` and the near-line quadratic bound
`2π A² (foldedRe q - 1/2)² e^{2A(foldedRe q - 1/2)}`. -/
def localZeroWeight (A : ℝ) (q : XiZeroCopy) : ℝ :=
  min ((Real.pi / 2) * Real.exp (2 * A * (foldedRe q - 1 / 2)))
    (2 * Real.pi * A ^ 2 * (foldedRe q - 1 / 2) ^ 2 * Real.exp (2 * A * (foldedRe q - 1 / 2)))

theorem localZeroWeight_nonneg (A : ℝ) (q : XiZeroCopy) : 0 ≤ localZeroWeight A q :=
  le_min (by positivity) (by positivity)

private theorem sum_shallow_localZeroWeight_le {ε_target C₂ κ₀ Cg Γ A v₀ : ℝ}
    (_hε : 0 < ε_target) (hC₂_pos : 0 < C₂) (hκ₀_pos : 0 < κ₀) (hCg : 0 ≤ Cg)
    (hglob : ∀ {T : ℝ}, 4 ≤ T → ∀ {σ : ℝ}, 1 / 2 ≤ σ →
      ((zeroHeightBox σ T).ncard : ℝ) ≤ Cg * (1 + Real.log T) * T)
    (hκ₀_2 : κ₀ ≤ 1 / (2 * C₂))
    (hκ₀_sq : κ₀ ^ 2 ≤ ε_target / (4000 * Real.pi * (Cg + 1) * C₂ ^ 2))
    (hΓ64 : 64 ≤ Γ) (hlogΓ_pos : 0 < Real.log Γ) (hlogΓ_ge1 : 1 ≤ Real.log Γ)
    (hA0 : 0 ≤ A) (hA : A ≤ κ₀ * Real.log Γ) (hv₀_def : v₀ = C₂ / Real.log Γ)
    (G : Finset XiZeroCopy)
    (hG : ∀ q ∈ G, Γ / 2 ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 4 * Γ) :
    (1 / Γ) * (∑ q ∈ G.filter (fun q => foldedRe q ≤ 1 / 2 + v₀), localZeroWeight A q) ≤
      (ε_target / 2) * Real.log Γ := by
  classical
  have hΓ0 : 0 < Γ := by linarith
  let G_sh := G.filter (fun q => foldedRe q ≤ 1 / 2 + v₀)
  have hsh_pt : ∀ q ∈ G_sh, localZeroWeight A q ≤ 6 * Real.pi * C₂ ^ 2 * κ₀ ^ 2 := fun q hq => by
    have hq_le : foldedRe q - 1 / 2 ≤ v₀ := by linarith [(Finset.mem_filter.mp hq).2]
    have hq_nn : 0 ≤ foldedRe q - 1 / 2 := sub_nonneg.mpr (half_le_foldedRe q)
    have hprod_le : A * (foldedRe q - 1 / 2) ≤ κ₀ * C₂ := by
      calc A * (foldedRe q - 1 / 2) ≤ (κ₀ * Real.log Γ) * v₀ :=
            mul_le_mul hA hq_le hq_nn (by positivity)
        _ = κ₀ * C₂ := by rw [hv₀_def]; field_simp [hlogΓ_pos.ne']
    have hκC₂_le : κ₀ * C₂ ≤ 1 / 2 := by
      have hm := mul_le_mul_of_nonneg_right hκ₀_2 hC₂_pos.le
      have heq : 1 / (2 * C₂) * C₂ = 1 / 2 := by field_simp [hC₂_pos.ne']
      linarith
    have hexp_le3 : Real.exp (2 * A * (foldedRe q - 1 / 2)) ≤ 3 := by
      have h1 : Real.exp (2 * A * (foldedRe q - 1 / 2)) ≤ Real.exp 1 :=
        Real.exp_le_exp.mpr (by linarith)
      exact h1.trans (Real.exp_one_lt_d9.le.trans (by norm_num))
    have hsq_le : A ^ 2 * (foldedRe q - 1 / 2) ^ 2 ≤ C₂ ^ 2 * κ₀ ^ 2 := by
      have h1 := pow_le_pow_left₀ (by positivity) hprod_le 2
      linarith
    refine (min_le_right _ _).trans ?_
    calc 2 * Real.pi * A ^ 2 * (foldedRe q - 1 / 2) ^ 2 * Real.exp (2 * A * (foldedRe q - 1 / 2))
        = 2 * Real.pi * (A ^ 2 * (foldedRe q - 1 / 2) ^ 2) *
            Real.exp (2 * A * (foldedRe q - 1 / 2)) := by ring
      _ ≤ 2 * Real.pi * (C₂ ^ 2 * κ₀ ^ 2) * 3 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsq_le (by positivity))
            hexp_le3 (Real.exp_pos _).le (by positivity)
      _ = 6 * Real.pi * C₂ ^ 2 * κ₀ ^ 2 := by ring
  have hsh_card : (G_sh.card : ℝ) ≤ 36 * (Cg + 1) * Γ * Real.log Γ := by
    let B₁ := G_sh.filter (fun q => |(q.1 : ℂ).im| ≤ Γ)
    let B₂ := G_sh.filter (fun q => Γ < |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 2 * Γ)
    let B₃ := G_sh.filter (fun q => 2 * Γ < |(q.1 : ℂ).im|)
    have hcard_cov : (G_sh.card : ℝ) ≤ (B₁.card : ℝ) + (B₂.card : ℝ) + (B₃.card : ℝ) := by
      have hpt_c : ∀ q ∈ G_sh, (1 : ℝ) ≤
          (if |(q.1 : ℂ).im| ≤ Γ then 1 else 0) +
          (if Γ < |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 2 * Γ then 1 else 0) +
          (if 2 * Γ < |(q.1 : ℂ).im| then 1 else 0) := fun q _ => by
        by_cases h1 : |(q.1 : ℂ).im| ≤ Γ
        · rw [if_pos h1, if_neg (fun h => not_lt_of_ge h1 h.1),
            if_neg (by linarith : ¬(2 * Γ < |(q.1 : ℂ).im|))]; norm_num
        · push Not at h1
          by_cases h2 : |(q.1 : ℂ).im| ≤ 2 * Γ
          · rw [if_neg (not_le.mpr h1), if_pos ⟨h1, h2⟩, if_neg (not_lt.mpr h2)]; norm_num
          · push Not at h2
            rw [if_neg (not_le.mpr h1), if_neg (fun h => not_le.mpr h2 h.2), if_pos h2]; norm_num
      have hs := Finset.sum_le_sum hpt_c
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_add_distrib,
        ← Finset.sum_filter] at hs
      exact hs
    have hbox_card : ∀ (T : ℝ), 4 ≤ T → ∀ (H : Finset XiZeroCopy),
        (∀ q ∈ H, T ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 2 * T) →
        (H.card : ℝ) ≤ 4 * Cg * (1 + Real.log T) * T := fun T hT4 H hH => by
      have hsub : (H : Set XiZeroCopy) ⊆ foldedHeightBox (1 / 2) T := fun q hq =>
        ⟨half_le_foldedRe q, hH q hq⟩
      have h1 := Set.ncard_le_ncard hsub (foldedHeightBox_finite _ _)
      rw [Set.ncard_coe_finset] at h1
      have h2 : (H.card : ℝ) ≤ 4 * ((zeroHeightBox (1 / 2) T).ncard : ℝ) := by
        exact_mod_cast h1.trans (ncard_foldedHeightBox_le (1 / 2) T)
      have h3 := hglob hT4 (le_rfl : (1 / 2 : ℝ) ≤ 1 / 2)
      nlinarith
    have hb1 := hbox_card (Γ / 2) (by linarith) B₁ fun q hq => by
      have hq' := Finset.mem_filter.mp hq
      exact ⟨(hG q (Finset.mem_filter.mp hq'.1).1).1, by linarith [hq'.2]⟩
    have hb2 := hbox_card Γ (by linarith) B₂ fun q hq => by
      have hq' := Finset.mem_filter.mp hq
      exact ⟨hq'.2.1.le, hq'.2.2⟩
    have hb3 := hbox_card (2 * Γ) (by linarith) B₃ fun q hq => by
      have hq' := Finset.mem_filter.mp hq
      exact ⟨hq'.2.le, by linarith [(hG q (Finset.mem_filter.mp hq'.1).1).2]⟩
    have hl1 : 1 + Real.log (Γ / 2) ≤ 2 * Real.log Γ := by
      have : Real.log (Γ / 2) ≤ Real.log Γ := Real.log_le_log (by positivity) (by linarith)
      linarith
    have hl2 : 1 + Real.log Γ ≤ 2 * Real.log Γ := by linarith
    have hl3 : 1 + Real.log (2 * Γ) ≤ 3 * Real.log Γ := by
      have : Real.log (2 * Γ) ≤ Real.log (Γ ^ 2) := Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_pow] at this; norm_num at this
      linarith
    have hb1' : (B₁.card : ℝ) ≤ 4 * Cg * (2 * Real.log Γ) * (Γ / 2) :=
      hb1.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hl1 (by positivity)) (by positivity))
    have hb2' : (B₂.card : ℝ) ≤ 4 * Cg * (2 * Real.log Γ) * Γ :=
      hb2.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hl2 (by positivity)) hΓ0.le)
    have hb3' : (B₃.card : ℝ) ≤ 4 * Cg * (3 * Real.log Γ) * (2 * Γ) :=
      hb3.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hl3 (by positivity)) (by positivity))
    have hsum3 : 4 * Cg * (2 * Real.log Γ) * (Γ / 2) +
        4 * Cg * (2 * Real.log Γ) * Γ +
        4 * Cg * (3 * Real.log Γ) * (2 * Γ) = 36 * Cg * Γ * Real.log Γ := by ring
    have hle36 : 36 * Cg * Γ * Real.log Γ ≤ 36 * (Cg + 1) * Γ * Real.log Γ := by
      have : 0 ≤ 36 * Γ * Real.log Γ := by positivity
      linarith
    linarith [hcard_cov, hb1', hb2', hb3', hsum3, hle36]
  have hs1 : (∑ q ∈ G_sh, localZeroWeight A q) ≤
      (G_sh.card : ℝ) * (6 * Real.pi * C₂ ^ 2 * κ₀ ^ 2) := by
    refine (Finset.sum_le_sum hsh_pt).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  calc (1 / Γ) * (∑ q ∈ G_sh, localZeroWeight A q)
      ≤ (1 / Γ) * ((36 * (Cg + 1) * Γ * Real.log Γ) * (6 * Real.pi * C₂ ^ 2 * κ₀ ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (hs1.trans (mul_le_mul_of_nonneg_right hsh_card (by positivity))) (by positivity)
    _ = 216 * Real.pi * (Cg + 1) * C₂ ^ 2 * κ₀ ^ 2 * Real.log Γ := by
        field_simp [hΓ0.ne']; norm_num
    _ ≤ 216 * Real.pi * (Cg + 1) * C₂ ^ 2 *
          (ε_target / (4000 * Real.pi * (Cg + 1) * C₂ ^ 2)) * Real.log Γ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hκ₀_sq (by positivity)) hlogΓ_pos.le
    _ = (216 / 4000) * ε_target * Real.log Γ := by
        have hπ_ne : Real.pi ≠ 0 := Real.pi_ne_zero
        have hCg_ne : Cg + 1 ≠ 0 := by positivity
        have hC₂_ne : C₂ ≠ 0 := hC₂_pos.ne'
        field_simp [hπ_ne, hCg_ne, hC₂_ne]
    _ ≤ (ε_target / 2) * Real.log Γ :=
        mul_le_mul_of_nonneg_right (by linarith) hlogΓ_pos.le

/-- **Logarithmic-Aperture Local Shell Absorption via Selberg Near-Line Density
(`exists_local_shell_depthDiff_weighted_le`):**
For every target `ε_target > 0`, there exist `κ₀ > 0` and `Γ₁ ≥ 64` such that for all `Γ ≥ Γ₁`,
all `0 ≤ A ≤ κ₀ log Γ`, and every finite set `G` of zero copies in `Γ/2 ≤ |Im ρ_q| ≤ 4Γ`,
`(1 / Γ) * ∑ q ∈ G, localZeroWeight A q ≤ ε_target * log Γ`. -/
theorem exists_local_shell_depthDiff_weighted_le {ε_target : ℝ} (hε : 0 < ε_target) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∃ Γ₁ : ℝ, 64 ≤ Γ₁ ∧
      ∀ Γ : ℝ, Γ₁ ≤ Γ → ∀ A : ℝ, 0 ≤ A → A ≤ κ₀ * Real.log Γ →
        ∀ G : Finset XiZeroCopy,
          (∀ q ∈ G, Γ / 2 ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 4 * Γ) →
          (1 / Γ) * (∑ q ∈ G, localZeroWeight A q) ≤ ε_target * Real.log Γ := by
  obtain ⟨A_sel, K_sel, hA_sel, hK_sel, hev_sel⟩ := RHTower.exists_windowZeros_weighted_le
  obtain ⟨U_sel, hU_sel⟩ := Filter.eventually_atTop.mp hev_sel
  obtain ⟨Cg, hCg, hglob⟩ := exists_zeroHeightBox_half_le_mul_log
  obtain ⟨K_log3, hK_log3_1, hK_log3⟩ :=
    exists_one_add_log_pow_le_rpow 3 (by norm_num : (0 : ℝ) < 1 / 4)
  set C₂ : ℝ := max 4800 (400 * A_sel / ε_target)
  have hC₂_4800 : 4800 ≤ C₂ := le_max_left _ _
  have hC₂_pos : 0 < C₂ := by linarith
  have hC₂_sel : 400 * A_sel / ε_target ≤ C₂ := le_max_right _ _
  clear_value C₂
  set κ₀ : ℝ :=
    min (1 / 38400)
      (min (1 / (2 * C₂))
        (Real.sqrt (ε_target / (4000 * Real.pi * (Cg + 1) * C₂ ^ 2))))
  have hκ₀_pos : 0 < κ₀ :=
    lt_min (by norm_num) (lt_min (by positivity) (Real.sqrt_pos.mpr (by positivity)))
  have hκ₀_1 : κ₀ ≤ 1 / 38400 := min_le_left _ _
  have hκ₀_2 : κ₀ ≤ 1 / (2 * C₂) := (min_le_right _ _).trans (min_le_left _ _)
  have hκ₀_sq : κ₀ ^ 2 ≤ ε_target / (4000 * Real.pi * (Cg + 1) * C₂ ^ 2) := by
    have hle : κ₀ ≤ Real.sqrt (ε_target / (4000 * Real.pi * (Cg + 1) * C₂ ^ 2)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    exact (pow_le_pow_left₀ hκ₀_pos.le hle 2).trans_eq (Real.sq_sqrt (by positivity))
  clear_value κ₀
  -- Choose `Γ₁` large enough for Selberg threshold, `v₀ ≤ 1/4`, and `Γ^{-1/4}` term
  set M_rem : ℝ := 160 * (K_sel + 1) * K_log3 / (C₂ * ε_target)
  have hM_rem_def : M_rem = 160 * (K_sel + 1) * K_log3 / (C₂ * ε_target) := rfl
  have hM_rem_pos : 0 < M_rem := by rw [hM_rem_def]; positivity
  clear_value M_rem
  set Γ₁ : ℝ := max 64 (max U_sel (max (Real.exp (4 * C₂)) (M_rem ^ (4 : ℕ))))
  have hΓ₁_64 : 64 ≤ Γ₁ := le_max_left _ _
  have hΓ₁_Usel : U_sel ≤ Γ₁ := (le_max_left _ _).trans (le_max_right _ _)
  have hΓ₁_expC₂ : Real.exp (4 * C₂) ≤ Γ₁ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hΓ₁_Mrem : M_rem ^ (4 : ℕ) ≤ Γ₁ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  clear_value Γ₁
  refine ⟨κ₀, hκ₀_pos, Γ₁, hΓ₁_64, fun Γ hΓ A hA0 hA G hG => ?_⟩
  classical
  have hΓ64 : 64 ≤ Γ := hΓ₁_64.trans hΓ
  have hΓ_Usel : U_sel ≤ Γ := hΓ₁_Usel.trans hΓ
  have hΓ_expC₂ : Real.exp (4 * C₂) ≤ Γ := hΓ₁_expC₂.trans hΓ
  have hΓ_Mrem : M_rem ^ (4 : ℕ) ≤ Γ := hΓ₁_Mrem.trans hΓ
  have hΓ0 : 0 < Γ := by linarith
  have hΓ1 : 1 ≤ Γ := by linarith
  have hlogΓ_ge : 4 * C₂ ≤ Real.log Γ := by
    have := Real.log_le_log (Real.exp_pos _) hΓ_expC₂
    rwa [Real.log_exp] at this
  have hlogΓ_pos : 0 < Real.log Γ := by linarith
  have hlogΓ_ge1 : 1 ≤ Real.log Γ := by linarith
  set v₀ : ℝ := C₂ / Real.log Γ
  have hv₀_def : v₀ = C₂ / Real.log Γ := rfl
  have hv₀_pos : 0 < v₀ := div_pos hC₂_pos hlogΓ_pos
  have hv₀_le_quarter : v₀ ≤ 1 / 4 := by
    rw [hv₀_def, div_le_div_iff₀ hlogΓ_pos (by norm_num)]; linarith
  clear_value v₀
  -- Split `G` into `G_shallow` (`foldedRe q ≤ 1/2 + v₀`) and `G_deep` (`1/2 + v₀ < foldedRe q`)
  let G_sh := G.filter (fun q => foldedRe q ≤ 1 / 2 + v₀)
  let G_dp := G.filter (fun q => 1 / 2 + v₀ < foldedRe q)
  have hsplit_G : ∑ q ∈ G, localZeroWeight A q =
      (∑ q ∈ G_sh, localZeroWeight A q) + ∑ q ∈ G_dp, localZeroWeight A q := by
    dsimp [G_sh, G_dp]
    rw [← Finset.sum_filter_add_sum_filter_not G (fun q => foldedRe q ≤ 1 / 2 + v₀)]
    congr 2; ext q; simp [not_le]
  have hsh_tot : (1 / Γ) * (∑ q ∈ G_sh, localZeroWeight A q) ≤ (ε_target / 2) * Real.log Γ :=
    sum_shallow_localZeroWeight_le hε hC₂_pos hκ₀_pos hCg hglob hκ₀_2 hκ₀_sq hΓ64 hlogΓ_pos
      hlogΓ_ge1 hA0 hA hv₀_def G hG
  -- 2. Deep zeros `G_dp` via 5 overlapping Selberg windows `U_k = (16/9) * (3/2)^k * Γ`
  let U_fn : ℕ → ℝ := fun k => (16 / 9 : ℝ) * (3 / 2 : ℝ) ^ k * Γ
  have hU_ge : ∀ k : ℕ, Γ ≤ U_fn k ∧ U_sel ≤ U_fn k ∧ 64 ≤ U_fn k := fun k => by
    have hp : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    have h1 : Γ ≤ U_fn k := by dsimp [U_fn]; nlinarith
    exact ⟨h1, hΓ_Usel.trans h1, hΓ64.trans h1⟩
  choose T₁ hT₁ T₂ hT₂ hsel_win using fun k : ℕ => hU_sel (U_fn k) (hU_ge k).2.1
  have hwin_bounds : ∀ k : ℕ, 0 < T₁ k ∧ T₁ k ≤ T₂ k ∧
      T₁ k ≤ (9 / 32) * U_fn k ∧ (15 / 32) * U_fn k ≤ T₂ k := fun k => by
    have hU64 := (hU_ge k).2.2
    have h1 := (hT₁ k).1; have h2 := (hT₁ k).2
    have h3 := (hT₂ k).1; have h4 := (hT₂ k).2
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  -- Cover `[Γ/2, 4Γ]` by `k ∈ Finset.range 5`
  have hcover_5 : ∀ t : ℝ, Γ / 2 ≤ t → t ≤ 4 * Γ →
      ∃ k ∈ Finset.range 5, T₁ k ≤ t ∧ t ≤ T₂ k := fun t ht1 ht2 => by
    by_cases hc0 : t ≤ (5 / 6) * Γ
    · refine ⟨0, by simp, ?_, ?_⟩
      · have := (hwin_bounds 0).2.2.1; dsimp [U_fn] at this; linarith
      · have := (hwin_bounds 0).2.2.2; dsimp [U_fn] at this; linarith
    · by_cases hc1 : t ≤ (5 / 4) * Γ
      · refine ⟨1, by simp, ?_, ?_⟩
        · have := (hwin_bounds 1).2.2.1; dsimp [U_fn] at this; linarith
        · have := (hwin_bounds 1).2.2.2; dsimp [U_fn] at this; linarith
      · by_cases hc2 : t ≤ (15 / 8) * Γ
        · refine ⟨2, by simp, ?_, ?_⟩
          · have := (hwin_bounds 2).2.2.1; dsimp [U_fn] at this; linarith
          · have := (hwin_bounds 2).2.2.2; dsimp [U_fn] at this; linarith
        · by_cases hc3 : t ≤ (45 / 16) * Γ
          · refine ⟨3, by simp, ?_, ?_⟩
            · have := (hwin_bounds 3).2.2.1; dsimp [U_fn] at this; linarith
            · have := (hwin_bounds 3).2.2.2; dsimp [U_fn] at this; linarith
          · refine ⟨4, by simp, ?_, ?_⟩
            · have := (hwin_bounds 4).2.2.1; dsimp [U_fn] at this; linarith
            · have := (hwin_bounds 4).2.2.2; dsimp [U_fn] at this; linarith
  have hdp_cov : (∑ q ∈ G_dp, localZeroWeight A q) ≤
      ∑ k ∈ Finset.range 5,
        (Real.pi / 2) *
          ∑ q ∈ G_dp.filter (fun q => T₁ k ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ T₂ k),
            Real.exp (2 * A * (foldedRe q - 1 / 2)) := by
    have hpt_dp : ∀ q ∈ G_dp, localZeroWeight A q ≤
        ∑ k ∈ Finset.range 5,
          if T₁ k ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ T₂ k then
            (Real.pi / 2) * Real.exp (2 * A * (foldedRe q - 1 / 2)) else 0 := fun q hq => by
      have hqG := hG q (Finset.mem_filter.mp hq).1
      obtain ⟨k₀, hk₀, htk⟩ := hcover_5 |(q.1 : ℂ).im| hqG.1 hqG.2
      refine (min_le_left _ _).trans ?_
      calc (Real.pi / 2) * Real.exp (2 * A * (foldedRe q - 1 / 2))
          = if T₁ k₀ ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ T₂ k₀ then
              (Real.pi / 2) * Real.exp (2 * A * (foldedRe q - 1 / 2)) else 0 :=
            (if_pos htk).symm
        _ ≤ ∑ k ∈ Finset.range 5,
              if T₁ k ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ T₂ k then
                (Real.pi / 2) * Real.exp (2 * A * (foldedRe q - 1 / 2)) else 0 :=
          Finset.single_le_sum (fun k _ => by split_ifs <;> positivity) hk₀
    refine (Finset.sum_le_sum hpt_dp).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [← Finset.sum_filter, Finset.mul_sum]
  -- Bound each of the 5 windows via `sum_foldedRe_le_four_mul_windowZeros` + `hsel_win`
  have hwin_k_le : ∀ k ∈ Finset.range 5,
      (1 / Γ) * ((Real.pi / 2) *
        ∑ q ∈ G_dp.filter (fun q => T₁ k ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ T₂ k),
          Real.exp (2 * A * (foldedRe q - 1 / 2))) ≤
        (ε_target / 10) * Real.log Γ := fun k hk => by
    have hk4 : k ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hU_upper : U_fn k ≤ 9 * Γ := by
      have hp : (3 / 2 : ℝ) ^ k ≤ (3 / 2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) hk4
      dsimp [U_fn]; nlinarith
    have hU_pos : 0 < U_fn k := lt_of_lt_of_le hΓ0 (hU_ge k).1
    have hlogU_ge : Real.log Γ ≤ Real.log (U_fn k) := Real.log_le_log hΓ0 (hU_ge k).1
    have hlogU_pos : 0 < Real.log (U_fn k) := lt_of_lt_of_le hlogΓ_pos hlogU_ge
    have hlogU_le : Real.log (U_fn k) ≤ 2 * Real.log Γ := by
      have hsq : U_fn k ≤ Γ ^ 2 := by nlinarith
      calc Real.log (U_fn k) ≤ Real.log (Γ ^ 2) := Real.log_le_log hU_pos hsq
        _ = 2 * Real.log Γ := by rw [Real.log_pow]; norm_num
    have hv₀_low : 2 / Real.log (U_fn k) ≤ v₀ := by
      rw [hv₀_def]
      calc 2 / Real.log (U_fn k) ≤ 2 / Real.log Γ :=
            div_le_div_of_nonneg_left (by norm_num) hlogΓ_pos hlogU_ge
        _ ≤ C₂ / Real.log Γ := div_le_div_of_nonneg_right (by linarith) hlogΓ_pos.le
    -- Compare `2 * A` with `(1 / 19200) * log (U_fn k)`
    have hexp_le_lam : ∀ q : XiZeroCopy,
        Real.exp (2 * A * (foldedRe q - 1 / 2)) ≤
          Real.exp ((1 / 19200) * (foldedRe q - 1 / 2) * Real.log (U_fn k)) := fun q => by
      apply Real.exp_le_exp.mpr
      have h2A : 2 * A ≤ (1 / 19200) * Real.log (U_fn k) := by
        calc 2 * A ≤ 2 * (κ₀ * Real.log Γ) := by linarith
          _ ≤ 2 * ((1 / 38400) * Real.log Γ) := by nlinarith
          _ = (1 / 19200) * Real.log Γ := by ring
          _ ≤ (1 / 19200) * Real.log (U_fn k) :=
              mul_le_mul_of_nonneg_left hlogU_ge (by norm_num)
      have hnn : 0 ≤ foldedRe q - 1 / 2 := sub_nonneg.mpr (half_le_foldedRe q)
      calc 2 * A * (foldedRe q - 1 / 2)
          ≤ ((1 / 19200) * Real.log (U_fn k)) * (foldedRe q - 1 / 2) :=
            mul_le_mul_of_nonneg_right h2A hnn
        _ = (1 / 19200) * (foldedRe q - 1 / 2) * Real.log (U_fn k) := by ring
    let Hk := G_dp.filter (fun q => T₁ k ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ T₂ k)
    have h4fold := sum_foldedRe_le_four_mul_windowZeros
      (g := fun y => Real.exp ((1 / 19200) * (y - 1 / 2) * Real.log (U_fn k)))
      (fun _ => (Real.exp_pos _).le)
      (hwin_bounds k).1 (hwin_bounds k).2.1 hv₀_pos Hk fun q hq => by
        have hq1 := Finset.mem_filter.mp hq
        exact ⟨(Finset.mem_filter.mp hq1.1).2, hq1.2.1, hq1.2.2⟩
    have hsel := hsel_win k (1 / 19200) v₀ (by norm_num) (by norm_num) hv₀_low hv₀_le_quarter
    -- Bound Term 1 of Selberg
    have hvL_ge : 4800 ≤ v₀ * Real.log (U_fn k) := by
      have h1 : C₂ ≤ v₀ * Real.log (U_fn k) := by
        rw [hv₀_def]
        calc C₂ = C₂ / Real.log Γ * Real.log Γ := by field_simp [hlogΓ_pos.ne']
          _ ≤ C₂ / Real.log Γ * Real.log (U_fn k) :=
              mul_le_mul_of_nonneg_left hlogU_ge (by positivity)
      linarith
    have hterm1 : U_fn k * A_sel / (4 * Real.pi * v₀) *
          (1 + 4800 / (v₀ * Real.log (U_fn k))) *
          Real.exp (-(v₀ * Real.log (U_fn k) / 4800)) ≤
        (9 * A_sel / (2 * Real.pi * C₂)) * Γ * Real.log Γ := by
      have hf1 : 1 + 4800 / (v₀ * Real.log (U_fn k)) ≤ 2 := by
        have : 4800 / (v₀ * Real.log (U_fn k)) ≤ 1 :=
          div_le_one_of_le₀ hvL_ge (by positivity)
        linarith
      have hf2 : Real.exp (-(v₀ * Real.log (U_fn k) / 4800)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith)
      have hprod12 : (1 + 4800 / (v₀ * Real.log (U_fn k))) *
          Real.exp (-(v₀ * Real.log (U_fn k) / 4800)) ≤ 2 :=
        (mul_le_mul hf1 hf2 (Real.exp_pos _).le (by norm_num)).trans_eq (by ring)
      have hmain1 : U_fn k * A_sel / (4 * Real.pi * v₀) ≤
          (9 * A_sel / (4 * Real.pi * C₂)) * Γ * Real.log Γ := by
        calc U_fn k * A_sel / (4 * Real.pi * v₀)
            ≤ (9 * Γ) * A_sel / (4 * Real.pi * v₀) :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right hU_upper hA_sel.le) (by positivity)
          _ = (9 * A_sel / (4 * Real.pi * C₂)) * Γ * Real.log Γ := by
              rw [hv₀_def]
              field_simp [Real.pi_ne_zero, hC₂_pos.ne', hlogΓ_pos.ne']
      calc U_fn k * A_sel / (4 * Real.pi * v₀) *
            (1 + 4800 / (v₀ * Real.log (U_fn k))) *
            Real.exp (-(v₀ * Real.log (U_fn k) / 4800))
          = (U_fn k * A_sel / (4 * Real.pi * v₀)) *
              ((1 + 4800 / (v₀ * Real.log (U_fn k))) *
                Real.exp (-(v₀ * Real.log (U_fn k) / 4800))) := by ring
        _ ≤ ((9 * A_sel / (4 * Real.pi * C₂)) * Γ * Real.log Γ) * 2 :=
            mul_le_mul hmain1 hprod12 (by positivity) (by positivity)
        _ = (9 * A_sel / (2 * Real.pi * C₂)) * Γ * Real.log Γ := by ring
    -- Bound Term 2 of Selberg
    have hterm2 : Real.log (U_fn k) *
          (K_sel * Real.log (U_fn k) / (Real.pi * v₀) *
            Real.exp ((1 / 19200) * Real.log (U_fn k))) ≤
        (4 * (K_sel + 1) * K_log3 / (Real.pi * C₂)) * Γ ^ (3 / 4 : ℝ) := by
      have hexpU : Real.exp ((1 / 19200) * Real.log (U_fn k)) ≤ Γ ^ (1 / 2 : ℝ) := by
        have hle : (1 / 19200) * Real.log (U_fn k) ≤ (1 / 2) * Real.log Γ := by linarith
        calc Real.exp ((1 / 19200) * Real.log (U_fn k))
            ≤ Real.exp ((1 / 2) * Real.log Γ) := Real.exp_le_exp.mpr hle
          _ = Γ ^ (1 / 2 : ℝ) := by rw [Real.rpow_def_of_pos hΓ0, mul_comm]
      have hlog3 : Real.log Γ ^ 3 ≤ K_log3 * Γ ^ (1 / 4 : ℝ) := by
        have h1 : Real.log Γ ^ 3 ≤ (1 + Real.log Γ) ^ 3 :=
          pow_le_pow_left₀ hlogΓ_pos.le (by linarith) 3
        exact h1.trans (hK_log3 Γ hΓ1)
      have hK_le : K_sel ≤ K_sel + 1 := by linarith
      calc Real.log (U_fn k) *
            (K_sel * Real.log (U_fn k) / (Real.pi * v₀) *
              Real.exp ((1 / 19200) * Real.log (U_fn k)))
          ≤ (2 * Real.log Γ) *
              ((K_sel + 1) * (2 * Real.log Γ) / (Real.pi * v₀) * Γ ^ (1 / 2 : ℝ)) := by
            refine mul_le_mul hlogU_le ?_ (by positivity) (by positivity)
            refine mul_le_mul ?_ hexpU (Real.exp_pos _).le (by positivity)
            exact div_le_div_of_nonneg_right
              (mul_le_mul hK_le hlogU_le hlogU_pos.le (by positivity)) (by positivity)
        _ = (4 * (K_sel + 1) / (Real.pi * C₂)) * Real.log Γ ^ 3 * Γ ^ (1 / 2 : ℝ) := by
            rw [hv₀_def, show Real.pi * (C₂ / Real.log Γ) = (Real.pi * C₂) / Real.log Γ by ring,
              div_div_eq_mul_div]
            ring
        _ ≤ (4 * (K_sel + 1) / (Real.pi * C₂)) * (K_log3 * Γ ^ (1 / 4 : ℝ)) * Γ ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hlog3 (by positivity))
              (Real.rpow_nonneg hΓ0.le _)
        _ = (4 * (K_sel + 1) * K_log3 / (Real.pi * C₂)) *
              (Γ ^ (1 / 4 : ℝ) * Γ ^ (1 / 2 : ℝ)) := by ring
        _ = (4 * (K_sel + 1) * K_log3 / (Real.pi * C₂)) * Γ ^ (3 / 4 : ℝ) := by
            rw [← Real.rpow_add hΓ0]; norm_num
    -- Combine `(1 / Γ) * (π / 2) * 4 * (hterm1 + hterm2) ≤ (ε_target / 10) * log Γ`
    have hsum_Hk : ∑ q ∈ Hk, Real.exp (2 * A * (foldedRe q - 1 / 2)) ≤
        4 * ((9 * A_sel / (2 * Real.pi * C₂)) * Γ * Real.log Γ +
          (4 * (K_sel + 1) * K_log3 / (Real.pi * C₂)) * Γ ^ (3 / 4 : ℝ)) := by
      have hs1 := Finset.sum_le_sum fun q (_ : q ∈ Hk) => hexp_le_lam q
      have hs2 := hs1.trans (h4fold.trans (mul_le_mul_of_nonneg_left hsel (by norm_num)))
      linarith [hterm1, hterm2]
    have h1_eps : 9 * A_sel / C₂ ≤ ε_target / 20 := by
      have hmul := (div_le_iff₀ hε).mp hC₂_sel
      rw [div_le_div_iff₀ hC₂_pos (by norm_num)]
      nlinarith
    have h2_eps : (8 * (K_sel + 1) * K_log3 / C₂) * Γ ^ (-(1 / 4 : ℝ)) ≤ ε_target / 20 := by
      have hM_le_rpow : M_rem ≤ Γ ^ (1 / 4 : ℝ) := by
        calc M_rem = (M_rem ^ (4 : ℕ)) ^ (1 / 4 : ℝ) := by
              rw [← Real.rpow_natCast M_rem 4, ← Real.rpow_mul hM_rem_pos.le]; norm_num
          _ ≤ Γ ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) hΓ_Mrem (by norm_num)
      have hinv_rpow : Γ ^ (-(1 / 4 : ℝ)) ≤ 1 / M_rem := by
        rw [Real.rpow_neg hΓ0.le, ← one_div]
        exact one_div_le_one_div_of_le hM_rem_pos hM_le_rpow
      calc (8 * (K_sel + 1) * K_log3 / C₂) * Γ ^ (-(1 / 4 : ℝ))
          ≤ (8 * (K_sel + 1) * K_log3 / C₂) * (1 / M_rem) :=
            mul_le_mul_of_nonneg_left hinv_rpow (by positivity)
        _ = ε_target / 20 := by
            have hK1_ne : K_sel + 1 ≠ 0 := by positivity
            have hKl_ne : K_log3 ≠ 0 := by linarith
            rw [hM_rem_def, one_div_div, div_mul_div_comm,
              div_eq_div_iff
                (mul_ne_zero hC₂_pos.ne' (mul_ne_zero (mul_ne_zero (by norm_num) hK1_ne) hKl_ne))
                (by norm_num)]
            ring
    have hrpow_div : (1 / Γ) * Γ ^ (3 / 4 : ℝ) = Γ ^ (-(1 / 4 : ℝ)) := by
      rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_add hΓ0]; norm_num
    calc (1 / Γ) * ((Real.pi / 2) * ∑ q ∈ Hk, Real.exp (2 * A * (foldedRe q - 1 / 2)))
        ≤ (1 / Γ) * ((Real.pi / 2) *
            (4 * ((9 * A_sel / (2 * Real.pi * C₂)) * Γ * Real.log Γ +
              (4 * (K_sel + 1) * K_log3 / (Real.pi * C₂)) * Γ ^ (3 / 4 : ℝ)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsum_Hk (by positivity)) (by positivity)
      _ = (9 * A_sel / C₂) * Real.log Γ +
            (8 * (K_sel + 1) * K_log3 / C₂) * ((1 / Γ) * Γ ^ (3 / 4 : ℝ)) := by
          field_simp [Real.pi_ne_zero, hC₂_pos.ne', hΓ0.ne']
      _ = (9 * A_sel / C₂) * Real.log Γ +
            (8 * (K_sel + 1) * K_log3 / C₂) * Γ ^ (-(1 / 4 : ℝ)) := by rw [hrpow_div]
      _ ≤ (ε_target / 20) * Real.log Γ + (ε_target / 20) * 1 :=
          add_le_add (mul_le_mul_of_nonneg_right h1_eps hlogΓ_pos.le)
            (by linarith [h2_eps])
      _ ≤ (ε_target / 20) * Real.log Γ + (ε_target / 20) * Real.log Γ :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hlogΓ_ge1 (by positivity))
      _ = (ε_target / 10) * Real.log Γ := by ring
  have hdp_tot : (1 / Γ) * (∑ q ∈ G_dp, localZeroWeight A q) ≤ (ε_target / 2) * Real.log Γ := by
    have hmul := mul_le_mul_of_nonneg_left hdp_cov (by positivity : 0 ≤ 1 / Γ)
    rw [Finset.mul_sum] at hmul
    calc (1 / Γ) * (∑ q ∈ G_dp, localZeroWeight A q)
        ≤ ∑ k ∈ Finset.range 5, (ε_target / 10) * Real.log Γ :=
          hmul.trans (Finset.sum_le_sum hwin_k_le)
      _ = (ε_target / 2) * Real.log Γ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  rw [hsplit_G, mul_add]
  linarith [hsh_tot, hdp_tot]

/-- **Unconditional Logarithmic-Aperture Strict Positivity for Single `cosineSource F₀ γ`
(`exists_logarithmic_aperture_frequencyAverage_fullZeroForm_cosineSource_pos`):**
There exist explicit positive constants `κ₀ > 0`, `c₀ > 0`, `C₀ ≥ 0`, and `Γ₀ ≥ 64` such that for
all `Γ ≥ Γ₀`, all apertures `0 ≤ A ≤ κ₀ log Γ` (polynomial prime support `X = e^{2A} ≤ Γ^{2κ₀}`,
exponentially beyond single-height positivity `A ≲ log log Γ`), and every `F₀ ∈ C²_c(ℝ)` supported
in `[-A, A]`,
`(1 / Γ) ∫_Γ^{2Γ} fullZeroForm (cosineSource F₀ γ) dγ ≥ c₀ (log Γ) ∫ F₀² - C₀ Γ^{-4/3} envelopeWindowNorm F₀ ^ 2`. -/
theorem exists_logarithmic_aperture_frequencyAverage_fullZeroForm_cosineSource_pos :
    ∃ κ₀ c₀ C₀ : ℝ, 0 < κ₀ ∧ 0 < c₀ ∧ 0 ≤ C₀ ∧ ∃ Γ₀ : ℝ, 64 ≤ Γ₀ ∧
      ∀ Γ : ℝ, Γ₀ ≤ Γ → ∀ A : ℝ, 0 ≤ A → A ≤ κ₀ * Real.log Γ →
        ∀ F₀ : ℝ → ℝ, ContDiff ℝ 2 F₀ → HasCompactSupport F₀ →
          (∀ u : ℝ, A < |u| → F₀ u = 0) →
          c₀ * Real.log Γ * (∫ u, F₀ u ^ 2) -
              C₀ * Γ ^ (-(4 / 3 : ℝ)) * envelopeWindowNorm F₀ ^ 2 ≤
            (1 / Γ) * ∫ γ in Icc Γ (2 * Γ), fullZeroForm (cosineSource F₀ γ) := by
  obtain ⟨Γ_rvm, hΓ_rvm, hrvm⟩ := exists_sum_mult_xiSupportsWindow_core_bounds
  obtain ⟨κ₁, hκ₁, Γ₁, hΓ₁, hloc_sel⟩ :=
    exists_local_shell_depthDiff_weighted_le (ε_target := 1 / 128) (by norm_num)
  obtain ⟨K_log1, hK_log1_1, hK_log1⟩ :=
    exists_one_add_log_pow_le_rpow 1 (by norm_num : (0 : ℝ) < 1 / 6)
  set κ₀ : ℝ := min κ₁ (1 / 2)
  have hκ₀_pos : 0 < κ₀ := lt_min hκ₁ (by norm_num)
  have hκ₀_1 : κ₀ ≤ κ₁ := min_le_left _ _
  have hκ₀_half : κ₀ ≤ 1 / 2 := min_le_right _ _
  set C₀ : ℝ := (9 / 2) * K_log1 + 32 * reciprocalSquareWeightTotal
  refine ⟨κ₀, 1 / 128, C₀, hκ₀_pos, by norm_num,
    by dsimp [C₀]; positivity [reciprocalSquareWeightTotal_nonneg],
    max Γ₁ Γ_rvm, hΓ₁.trans (le_max_left _ _),
    fun Γ hΓ A hA0 hA F₀ hF₀ hF₀c hsupp => ?_⟩
  classical
  have hΓ64 : 64 ≤ Γ := (hΓ₁.trans (le_max_left _ _)).trans hΓ
  have hΓ1 : 1 ≤ Γ := by linarith
  have hΓ0 : 0 < Γ := by linarith
  have hlogΓ_nn : 0 ≤ Real.log Γ := Real.log_nonneg hΓ1
  have hA_κ₁ : A ≤ κ₁ * Real.log Γ :=
    hA.trans (mul_le_mul_of_nonneg_right hκ₀_1 hlogΓ_nn)
  have hA_half : A ≤ (1 / 2) * Real.log Γ :=
    hA.trans (mul_le_mul_of_nonneg_right hκ₀_half hlogΓ_nn)
  obtain ⟨hd_sub_sum, hd_add_sum, hc_sub, hc_add, G_loc, hG_loc, hsub_int, hadd_int⟩ :=
    integral_Icc_tsum_depthDiff_div_four_le hF₀ hF₀c hΓ1 hA0 hsupp
  -- Embed `W_core := xiSupportsWindow (5*Γ/4) (3*Γ/2)` into `zetaZeroConfig.carrier`
  let W_core : Finset XiDivisorSupport := xiSupportsWindow (5 * Γ / 4) (3 * Γ / 2)
  let C_core : Finset zetaZeroConfig.carrier := W_core.map xiDivisorZetaCarrierEquiv.toEmbedding
  have hmem_core : ∀ ρ ∈ C_core,
      0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 ∧ 5 * Γ / 4 ≤ (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 3 * Γ / 2 := by
    intro ρ hρ
    rcases Finset.mem_map.mp hρ with ⟨ξ₀, hξ₀, rfl⟩
    have hwin := (mem_xiSupportsWindow (by positivity : 0 ≤ 5 * Γ / 4)).mp hξ₀
    have hstrip := (xiDivisorZetaCarrierEquiv ξ₀).2
    exact ⟨hstrip.2.1, hstrip.2.2, hwin.1.le, hwin.2⟩
  -- Pointwise lower bound on `Icc Γ (2 * Γ)` and finite-sum integration
  let coreTerm : zetaZeroConfig.carrier → ℝ → ℝ := fun ρ γ =>
    (zetaZeroConfig.mult ρ : ℝ) *
      (‖paperFT (depthSumProfile F₀ (ρ : ℂ)) (-(γ : ℂ))‖ ^ 2 / 8 -
        ‖paperFT (depthSumProfile F₀ (ρ : ℂ)) (γ : ℂ)‖ ^ 2 / 4)
  let diffAvg : ℝ → ℝ := fun γ =>
    ((∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) +
      ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))‖ ^ 2 / 4) / 2
  have hcore_cont : ∀ ρ ∈ C_core, Continuous (coreTerm ρ) := fun ρ hρ => by
    obtain ⟨hr0, hr1, hi1, hi2⟩ := hmem_core ρ hρ
    obtain ⟨hcm, hcp, _, _⟩ :=
      integral_Icc_norm_paperFT_depthSum_sq_bounds hF₀ hF₀c hΓ1 hA0 hsupp hr0 hr1 hi1 hi2
    dsimp [coreTerm]
    exact continuous_const.mul ((hcm.div_const 8).sub (hcp.div_const 4))
  have hcore_sum_int : IntegrableOn (fun γ : ℝ => ∑ ρ ∈ C_core, coreTerm ρ γ) (Icc Γ (2 * Γ)) :=
    (continuous_finsetSum C_core hcore_cont).integrableOn_Icc
  have hdiff_int : IntegrableOn diffAvg (Icc Γ (2 * Γ)) :=
    ((hc_sub.add hc_add).div_const 2).integrableOn_Icc
  have hlhs_int : IntegrableOn (fun γ : ℝ => (∑ ρ ∈ C_core, coreTerm ρ γ) - diffAvg γ)
      (Icc Γ (2 * Γ)) :=
    hcore_sum_int.sub hdiff_int
  have hf_cos_cont := (continuous_zeta_W_re_modulated hF₀ hF₀c).2
  have hint_ge := setIntegral_mono_on hlhs_int hf_cos_cont.integrableOn_Icc measurableSet_Icc
    fun γ _ => fullZeroForm_cosineSource_ge_finset hF₀ hF₀c γ C_core (hd_sub_sum γ) (hd_add_sum γ)
  rw [integral_sub hcore_sum_int hdiff_int,
    integral_finsetSum C_core (fun ρ hρ => (hcore_cont ρ hρ).integrableOn_Icc)] at hint_ge
  -- Lower bound each `ρ ∈ C_core` integral
  have hcore_each : ∀ ρ ∈ C_core,
      (zetaZeroConfig.mult ρ : ℝ) *
          ((Real.pi / 4) * (∫ u, F₀ u ^ 2) -
            (9 * Real.pi / (4 * Γ ^ 2)) * Real.exp A * envelopeWindowNorm F₀ ^ 2) ≤
        ∫ γ in Icc Γ (2 * Γ), coreTerm ρ γ := fun ρ hρ => by
    obtain ⟨hr0, hr1, hi1, hi2⟩ := hmem_core ρ hρ
    obtain ⟨hcm, hcp, hbm, hbp⟩ :=
      integral_Icc_norm_paperFT_depthSum_sq_bounds hF₀ hF₀c hΓ1 hA0 hsupp hr0 hr1 hi1 hi2
    dsimp [coreTerm]
    rw [integral_const_mul, integral_sub (hcm.div_const 8).integrableOn_Icc
        (hcp.div_const 4).integrableOn_Icc, integral_div, integral_div]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hcomb : ((2 * Real.pi * ∫ u, F₀ u ^ 2) -
          (16 * Real.pi / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2) / 8 -
        ((Real.pi / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2) / 4 =
        (Real.pi / 4) * (∫ u, F₀ u ^ 2) -
          (9 * Real.pi / (4 * Γ ^ 2)) * Real.exp A * envelopeWindowNorm F₀ ^ 2 := by
      field_simp [hΓ0.ne']; ring
    exact hcomb.symm.trans_le (sub_le_sub
      (div_le_div_of_nonneg_right hbm (by norm_num))
      (div_le_div_of_nonneg_right hbp (by norm_num)))
  have hmult_sum_eq : (∑ ρ ∈ C_core, (zetaZeroConfig.mult ρ : ℝ)) =
      ∑ ξ₀ ∈ W_core, (xiSupportMultiplicity ξ₀ : ℝ) := by
    dsimp [C_core]
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun ξ₀ _ => ?_
    exact_mod_cast (xiDivisorZetaCarrierEquiv_multiplicity ξ₀).symm
  obtain ⟨hrvm_low, hrvm_high⟩ := hrvm Γ ((le_max_right _ _).trans hΓ)
  have hmass_nn : 0 ≤ ∫ u, F₀ u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hcore_sum_ge : (1 / 64) * Γ * Real.log Γ * (∫ u, F₀ u ^ 2) -
        (9 / 2) * (Real.log Γ / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 ≤
      ∑ ρ ∈ C_core, ∫ γ in Icc Γ (2 * Γ), coreTerm ρ γ := by
    have hs := Finset.sum_le_sum hcore_each
    rw [← Finset.sum_mul, hmult_sum_eq] at hs
    have hpos_part : (1 / 64) * Γ * Real.log Γ * (∫ u, F₀ u ^ 2) ≤
        (∑ ξ₀ ∈ W_core, (xiSupportMultiplicity ξ₀ : ℝ)) *
          ((Real.pi / 4) * (∫ u, F₀ u ^ 2)) := by
      calc (1 / 64) * Γ * Real.log Γ * (∫ u, F₀ u ^ 2)
          = ((1 / (16 * Real.pi)) * Γ * Real.log Γ) * ((Real.pi / 4) * (∫ u, F₀ u ^ 2)) := by
            field_simp [Real.pi_ne_zero]; ring
        _ ≤ (∑ ξ₀ ∈ W_core, (xiSupportMultiplicity ξ₀ : ℝ)) *
              ((Real.pi / 4) * (∫ u, F₀ u ^ 2)) :=
            mul_le_mul_of_nonneg_right hrvm_low (by positivity)
    have hneg_part : (∑ ξ₀ ∈ W_core, (xiSupportMultiplicity ξ₀ : ℝ)) *
          ((9 * Real.pi / (4 * Γ ^ 2)) * Real.exp A * envelopeWindowNorm F₀ ^ 2) ≤
        (9 / 2) * (Real.log Γ / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 := by
      calc (∑ ξ₀ ∈ W_core, (xiSupportMultiplicity ξ₀ : ℝ)) *
            ((9 * Real.pi / (4 * Γ ^ 2)) * Real.exp A * envelopeWindowNorm F₀ ^ 2)
          ≤ ((2 / Real.pi) * Γ * Real.log Γ) *
              ((9 * Real.pi / (4 * Γ ^ 2)) * Real.exp A * envelopeWindowNorm F₀ ^ 2) :=
            mul_le_mul_of_nonneg_right hrvm_high (by positivity)
        _ = (9 / 2) * (Real.log Γ / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 := by
            field_simp [Real.pi_ne_zero, hΓ0.ne']; ring
    linarith
  -- Upper bound `(1 / Γ) * ∫ diffAvg` via `localZeroWeight` + `hloc_sel`
  have hGloc_sub : (∑ q ∈ G_loc,
      (∫ γ in Icc Γ (2 * Γ),
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2) / 4) ≤
      (∑ q ∈ G_loc, localZeroWeight A q) * ∫ u, F₀ u ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun q _ => ?_
    obtain ⟨_, hb1, hb2⟩ := integral_norm_paperFT_depthDiff_sq_le hF₀.continuous hF₀c hA0 hsupp
      (q.1 : ℂ) Γ (2 * Γ)
    have hsq_abs : ((q.1 : ℂ).re - 1 / 2) ^ 2 = (foldedRe q - 1 / 2) ^ 2 := by
      rw [foldedRe_sub_half_eq_abs, sq_abs]
    rw [← foldedRe_sub_half_eq_abs q] at hb1 hb2
    rw [hsq_abs] at hb2
    unfold localZeroWeight
    rcases min_cases
      ((Real.pi / 2) * Real.exp (2 * A * (foldedRe q - 1 / 2)))
      (2 * Real.pi * A ^ 2 * (foldedRe q - 1 / 2) ^ 2 * Real.exp (2 * A * (foldedRe q - 1 / 2)))
      with ⟨heq, _⟩ | ⟨heq, _⟩ <;> (rw [heq]; linarith)
  have hGloc_add : (∑ q ∈ G_loc,
      (∫ γ in Icc Γ (2 * Γ),
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) + (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) + (γ : ℂ))‖ ^ 2) / 4) ≤
      (∑ q ∈ G_loc, localZeroWeight A q) * ∫ u, F₀ u ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun q _ => ?_
    obtain ⟨hb1, hb2⟩ := integral_norm_paperFT_depthDiff_add_sq_le hF₀.continuous hF₀c hA0 hsupp
      (q.1 : ℂ) Γ (2 * Γ)
    have hsq_abs : ((q.1 : ℂ).re - 1 / 2) ^ 2 = (foldedRe q - 1 / 2) ^ 2 := by
      rw [foldedRe_sub_half_eq_abs, sq_abs]
    rw [← foldedRe_sub_half_eq_abs q] at hb1 hb2
    rw [hsq_abs] at hb2
    unfold localZeroWeight
    rcases min_cases
      ((Real.pi / 2) * Real.exp (2 * A * (foldedRe q - 1 / 2)))
      (2 * Real.pi * A ^ 2 * (foldedRe q - 1 / 2) ^ 2 * Real.exp (2 * A * (foldedRe q - 1 / 2)))
      with ⟨heq, _⟩ | ⟨heq, _⟩ <;> (rw [heq]; linarith)
  have hdiff_int_le : (∫ γ in Icc Γ (2 * Γ), diffAvg γ) ≤
      (∑ q ∈ G_loc, localZeroWeight A q) * (∫ u, F₀ u ^ 2) +
        (32 * reciprocalSquareWeightTotal / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 := by
    have heq : (∫ γ in Icc Γ (2 * Γ), diffAvg γ) =
        ((∫ γ in Icc Γ (2 * Γ),
            ∑' ρ : zetaZeroConfig.carrier,
              (zetaZeroConfig.mult ρ : ℝ) *
                ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
                  paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) +
          ∫ γ in Icc Γ (2 * Γ),
            ∑' ρ : zetaZeroConfig.carrier,
              (zetaZeroConfig.mult ρ : ℝ) *
                ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ)) -
                  paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))‖ ^ 2 / 4) / 2 := by
      dsimp only [diffAvg]
      rw [integral_div, integral_add hc_sub.integrableOn_Icc hc_add.integrableOn_Icc]
    linarith [heq, hsub_int, hadd_int, hGloc_sub, hGloc_add]
  have hsel_bound := hloc_sel Γ ((le_max_left _ _).trans hΓ) A hA0 hA_κ₁ G_loc hG_loc
  have hexpA_half : Real.exp A ≤ Γ ^ (1 / 2 : ℝ) := by
    calc Real.exp A ≤ Real.exp ((1 / 2) * Real.log Γ) := Real.exp_le_exp.mpr hA_half
      _ = Γ ^ (1 / 2 : ℝ) := by rw [Real.rpow_def_of_pos hΓ0, mul_comm]
  -- Bound the two `envelopeWindowNorm F₀ ^ 2` error terms by `C₀ * Γ^{-4/3} * W²`
  have herr_core : (1 / Γ) * ((9 / 2) * (Real.log Γ / Γ) * Real.exp A *
      envelopeWindowNorm F₀ ^ 2) ≤
      (9 / 2) * K_log1 * Γ ^ (-(4 / 3 : ℝ)) * envelopeWindowNorm F₀ ^ 2 := by
    have hlog1 : Real.log Γ ≤ K_log1 * Γ ^ (1 / 6 : ℝ) := by
      have h1 : Real.log Γ ≤ (1 + Real.log Γ) ^ 1 := by simp
      exact h1.trans (hK_log1 Γ hΓ1)
    have hrpow : (1 / Γ) * (1 / Γ) * Γ ^ (1 / 6 : ℝ) * Γ ^ (1 / 2 : ℝ) = Γ ^ (-(4 / 3 : ℝ)) := by
      have hsq : (1 / Γ) * (1 / Γ) = Γ ^ (-2 : ℝ) := by
        have h1 : (Γ ^ 2)⁻¹ = Γ ^ (-2 : ℝ) := by
          rw [← Real.rpow_natCast Γ 2, ← Real.rpow_neg hΓ0.le]; norm_num
        calc (1 / Γ) * (1 / Γ) = (Γ ^ 2)⁻¹ := by ring
          _ = Γ ^ (-2 : ℝ) := h1
      rw [hsq, ← Real.rpow_add hΓ0, ← Real.rpow_add hΓ0]; norm_num
    calc (1 / Γ) * ((9 / 2) * (Real.log Γ / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2)
        ≤ (1 / Γ) * ((9 / 2) * ((K_log1 * Γ ^ (1 / 6 : ℝ)) / Γ) *
            Γ ^ (1 / 2 : ℝ) * envelopeWindowNorm F₀ ^ 2) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              (mul_le_mul
                (mul_le_mul_of_nonneg_left
                  (div_le_div_of_nonneg_right hlog1 hΓ0.le) (by norm_num))
                hexpA_half (Real.exp_pos _).le (by positivity))
              (sq_nonneg _)) (by positivity)
      _ = (9 / 2) * K_log1 * ((1 / Γ) * (1 / Γ) * Γ ^ (1 / 6 : ℝ) * Γ ^ (1 / 2 : ℝ)) *
            envelopeWindowNorm F₀ ^ 2 := by ring
      _ = (9 / 2) * K_log1 * Γ ^ (-(4 / 3 : ℝ)) * envelopeWindowNorm F₀ ^ 2 := by rw [hrpow]
  have herr_rem : (1 / Γ) * ((32 * reciprocalSquareWeightTotal / Γ) *
      Real.exp A * envelopeWindowNorm F₀ ^ 2) ≤
      32 * reciprocalSquareWeightTotal * Γ ^ (-(4 / 3 : ℝ)) * envelopeWindowNorm F₀ ^ 2 := by
    have hrpow : (1 / Γ) * (1 / Γ) * Γ ^ (1 / 2 : ℝ) ≤ Γ ^ (-(4 / 3 : ℝ)) := by
      have hsq : (1 / Γ) * (1 / Γ) * Γ ^ (1 / 2 : ℝ) = Γ ^ (-(3 / 2 : ℝ)) := by
        have h1 : (Γ ^ 2)⁻¹ = Γ ^ (-2 : ℝ) := by
          rw [← Real.rpow_natCast Γ 2, ← Real.rpow_neg hΓ0.le]; norm_num
        calc (1 / Γ) * (1 / Γ) * Γ ^ (1 / 2 : ℝ) = (Γ ^ 2)⁻¹ * Γ ^ (1 / 2 : ℝ) := by ring
          _ = Γ ^ (-2 : ℝ) * Γ ^ (1 / 2 : ℝ) := by rw [h1]
          _ = Γ ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add hΓ0]; norm_num
      rw [hsq]
      exact Real.rpow_le_rpow_of_exponent_le hΓ1 (by norm_num)
    calc (1 / Γ) * ((32 * reciprocalSquareWeightTotal / Γ) *
          Real.exp A * envelopeWindowNorm F₀ ^ 2)
        ≤ (1 / Γ) * ((32 * reciprocalSquareWeightTotal / Γ) *
            Γ ^ (1 / 2 : ℝ) * envelopeWindowNorm F₀ ^ 2) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hexpA_half
                (by positivity [reciprocalSquareWeightTotal_nonneg]))
              (sq_nonneg _)) (by positivity)
      _ = 32 * reciprocalSquareWeightTotal * ((1 / Γ) * (1 / Γ) * Γ ^ (1 / 2 : ℝ)) *
            envelopeWindowNorm F₀ ^ 2 := by ring
      _ ≤ 32 * reciprocalSquareWeightTotal * Γ ^ (-(4 / 3 : ℝ)) * envelopeWindowNorm F₀ ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hrpow
              (by positivity [reciprocalSquareWeightTotal_nonneg]))
            (sq_nonneg _)
  have hmain_pos : (1 / Γ) * ((1 / 64) * Γ * Real.log Γ * (∫ u, F₀ u ^ 2)) =
      (1 / 64) * Real.log Γ * (∫ u, F₀ u ^ 2) := by field_simp [hΓ0.ne']
  have hsel_mass : (1 / Γ) * ((∑ q ∈ G_loc, localZeroWeight A q) * (∫ u, F₀ u ^ 2)) ≤
      (1 / 128) * Real.log Γ * (∫ u, F₀ u ^ 2) := by
    calc (1 / Γ) * ((∑ q ∈ G_loc, localZeroWeight A q) * (∫ u, F₀ u ^ 2))
        = ((1 / Γ) * ∑ q ∈ G_loc, localZeroWeight A q) * (∫ u, F₀ u ^ 2) := by ring
      _ ≤ ((1 / 128) * Real.log Γ) * (∫ u, F₀ u ^ 2) :=
          mul_le_mul_of_nonneg_right hsel_bound hmass_nn
      _ = (1 / 128) * Real.log Γ * (∫ u, F₀ u ^ 2) := by ring
  have h1 := mul_le_mul_of_nonneg_left hint_ge (by positivity : 0 ≤ 1 / Γ)
  have h2 := mul_le_mul_of_nonneg_left hcore_sum_ge (by positivity : 0 ≤ 1 / Γ)
  have h3 := mul_le_mul_of_nonneg_left hdiff_int_le (by positivity : 0 ≤ 1 / Γ)
  dsimp [C₀]
  linarith [h1, h2, h3, hmain_pos, hsel_mass, herr_core, herr_rem]

/-- **Unconditional Logarithmic-Aperture Strict Positivity for Quadrature
(`exists_logarithmic_aperture_frequencyAverage_quadrature_pos`):**
Applying `re_zeta_W_complexModulatedSource_ge_finset` on the interior RVM core window coupled with
`exists_local_shell_depthDiff_weighted_le` yields strict logarithmic-aperture positivity for the
quadrature sum `fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ)`. -/
theorem exists_logarithmic_aperture_frequencyAverage_quadrature_pos :
    ∃ κ₀ c₀ C₀ : ℝ, 0 < κ₀ ∧ 0 < c₀ ∧ 0 ≤ C₀ ∧ ∃ Γ₀ : ℝ, 64 ≤ Γ₀ ∧
      ∀ Γ : ℝ, Γ₀ ≤ Γ → ∀ A : ℝ, 0 ≤ A → A ≤ κ₀ * Real.log Γ →
        ∀ F₀ : ℝ → ℝ, ContDiff ℝ 2 F₀ → HasCompactSupport F₀ →
          (∀ u : ℝ, A < |u| → F₀ u = 0) →
          c₀ * Real.log Γ * (∫ u, F₀ u ^ 2) -
              C₀ * Γ ^ (-(4 / 3 : ℝ)) * envelopeWindowNorm F₀ ^ 2 ≤
            (1 / Γ) * ∫ γ in Icc Γ (2 * Γ),
              (fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ)) := by
  obtain ⟨Γ_rvm, hΓ_rvm, hrvm⟩ := exists_sum_mult_xiSupportsWindow_core_bounds
  obtain ⟨κ₁, hκ₁, Γ₁, hΓ₁, hloc_sel⟩ :=
    exists_local_shell_depthDiff_weighted_le (ε_target := 1 / 16) (by norm_num)
  obtain ⟨K_log1, hK_log1_1, hK_log1⟩ :=
    exists_one_add_log_pow_le_rpow 1 (by norm_num : (0 : ℝ) < 1 / 6)
  set κ₀ : ℝ := min κ₁ (1 / 2)
  have hκ₀_pos : 0 < κ₀ := lt_min hκ₁ (by norm_num)
  set C₀ : ℝ := 32 * K_log1 + 32 * reciprocalSquareWeightTotal
  refine ⟨κ₀, 1 / 16, C₀, hκ₀_pos, by norm_num,
    by dsimp [C₀]; positivity [reciprocalSquareWeightTotal_nonneg],
    max Γ₁ Γ_rvm, hΓ₁.trans (le_max_left _ _),
    fun Γ hΓ A hA0 hA F₀ hF₀ hF₀c hsupp => ?_⟩
  classical
  have hΓ64 : 64 ≤ Γ := (hΓ₁.trans (le_max_left _ _)).trans hΓ
  have hΓ1 : 1 ≤ Γ := by linarith
  have hΓ0 : 0 < Γ := by linarith
  have hlogΓ_nn : 0 ≤ Real.log Γ := Real.log_nonneg hΓ1
  have hA_κ₁ : A ≤ κ₁ * Real.log Γ :=
    hA.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hlogΓ_nn)
  have hA_half : A ≤ (1 / 2) * Real.log Γ :=
    hA.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hlogΓ_nn)
  obtain ⟨hd_sub_sum, _hd_add_sum, hc_sub, _hc_add, G_loc, hG_loc, hsub_int, _hadd_int⟩ :=
    integral_Icc_tsum_depthDiff_div_four_le hF₀ hF₀c hΓ1 hA0 hsupp
  let W_core : Finset XiDivisorSupport := xiSupportsWindow (5 * Γ / 4) (3 * Γ / 2)
  let C_core : Finset zetaZeroConfig.carrier := W_core.map xiDivisorZetaCarrierEquiv.toEmbedding
  have hmem_core : ∀ ρ ∈ C_core,
      0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 ∧ 5 * Γ / 4 ≤ (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 3 * Γ / 2 := by
    intro ρ hρ
    rcases Finset.mem_map.mp hρ with ⟨ξ₀, hξ₀, rfl⟩
    have hwin := (mem_xiSupportsWindow (by positivity : 0 ≤ 5 * Γ / 4)).mp hξ₀
    have hstrip := (xiDivisorZetaCarrierEquiv ξ₀).2
    exact ⟨hstrip.2.1, hstrip.2.2, hwin.1.le, hwin.2⟩
  let coreQ : zetaZeroConfig.carrier → ℝ → ℝ := fun ρ γ =>
    (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT (depthSumProfile F₀ (ρ : ℂ)) (-(γ : ℂ))‖ ^ 2
  have hcore_cont : ∀ ρ ∈ C_core, Continuous (coreQ ρ) := fun ρ hρ => by
    obtain ⟨hr0, hr1, hi1, hi2⟩ := hmem_core ρ hρ
    obtain ⟨hcm, _, _, _⟩ :=
      integral_Icc_norm_paperFT_depthSum_sq_bounds hF₀ hF₀c hΓ1 hA0 hsupp hr0 hr1 hi1 hi2
    exact continuous_const.mul hcm
  have hquad_cont : Continuous fun γ : ℝ =>
      fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ) := by
    have heq : (fun γ : ℝ => fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ)) =
        fun γ : ℝ =>
          (zetaZeroConfig.W (complexModulatedSource F₀ γ) (complexModulatedSource F₀ γ)).re :=
      funext (fullZeroForm_cosine_add_sine_eq_zeta_W_re hF₀ hF₀c)
    rw [heq]
    exact (continuous_zeta_W_re_modulated hF₀ hF₀c).1
  have hcore_sum_int : IntegrableOn (fun γ : ℝ => ∑ ρ ∈ C_core, coreQ ρ γ) (Icc Γ (2 * Γ)) :=
    (continuous_finsetSum C_core hcore_cont).integrableOn_Icc
  have hsub_int_on : IntegrableOn
      (fun γ : ℝ => ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4)
      (Icc Γ (2 * Γ)) :=
    hc_sub.integrableOn_Icc
  have hlhs_int : IntegrableOn
      (fun γ : ℝ => (∑ ρ ∈ C_core, coreQ ρ γ) -
        ∑' ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℝ) *
            ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
              paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4)
      (Icc Γ (2 * Γ)) :=
    hcore_sum_int.sub hsub_int_on
  have hint_ge := setIntegral_mono_on hlhs_int hquad_cont.integrableOn_Icc measurableSet_Icc
    fun γ _ => by
      rw [fullZeroForm_cosine_add_sine_eq_zeta_W_re hF₀ hF₀c γ]
      exact re_zeta_W_complexModulatedSource_ge_finset hF₀ hF₀c γ C_core (hd_sub_sum γ)
  rw [integral_sub hcore_sum_int hsub_int_on,
    integral_finsetSum C_core (fun ρ hρ => (hcore_cont ρ hρ).integrableOn_Icc)] at hint_ge
  have hcore_each : ∀ ρ ∈ C_core,
      (zetaZeroConfig.mult ρ : ℝ) *
          (2 * Real.pi * (∫ u, F₀ u ^ 2) -
            (16 * Real.pi / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2) ≤
        ∫ γ in Icc Γ (2 * Γ), coreQ ρ γ := fun ρ hρ => by
    obtain ⟨hr0, hr1, hi1, hi2⟩ := hmem_core ρ hρ
    obtain ⟨_, _, hbm, _⟩ :=
      integral_Icc_norm_paperFT_depthSum_sq_bounds hF₀ hF₀c hΓ1 hA0 hsupp hr0 hr1 hi1 hi2
    dsimp [coreQ]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hbm (Nat.cast_nonneg _)
  have hmult_sum_eq : (∑ ρ ∈ C_core, (zetaZeroConfig.mult ρ : ℝ)) =
      ∑ ξ₀ ∈ W_core, (xiSupportMultiplicity ξ₀ : ℝ) := by
    dsimp [C_core]; rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun ξ₀ _ => ?_
    exact_mod_cast (xiDivisorZetaCarrierEquiv_multiplicity ξ₀).symm
  obtain ⟨hrvm_low, hrvm_high⟩ := hrvm Γ ((le_max_right _ _).trans hΓ)
  have hmass_nn : 0 ≤ ∫ u, F₀ u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hcore_sum_ge : (1 / 8) * Γ * Real.log Γ * (∫ u, F₀ u ^ 2) -
        32 * (Real.log Γ / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 ≤
      ∑ ρ ∈ C_core, ∫ γ in Icc Γ (2 * Γ), coreQ ρ γ := by
    have hs := Finset.sum_le_sum hcore_each
    rw [← Finset.sum_mul, hmult_sum_eq] at hs
    have hp1 : (1 / 8) * Γ * Real.log Γ * (∫ u, F₀ u ^ 2) ≤
        (∑ ξ₀ ∈ W_core, (xiSupportMultiplicity ξ₀ : ℝ)) * (2 * Real.pi * (∫ u, F₀ u ^ 2)) := by
      calc (1 / 8) * Γ * Real.log Γ * (∫ u, F₀ u ^ 2)
          = ((1 / (16 * Real.pi)) * Γ * Real.log Γ) * (2 * Real.pi * (∫ u, F₀ u ^ 2)) := by
            field_simp [Real.pi_ne_zero]; ring
        _ ≤ (∑ ξ₀ ∈ W_core, (xiSupportMultiplicity ξ₀ : ℝ)) *
              (2 * Real.pi * (∫ u, F₀ u ^ 2)) :=
            mul_le_mul_of_nonneg_right hrvm_low (by positivity)
    have hp2 : (∑ ξ₀ ∈ W_core, (xiSupportMultiplicity ξ₀ : ℝ)) *
          ((16 * Real.pi / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2) ≤
        32 * (Real.log Γ / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 := by
      calc (∑ ξ₀ ∈ W_core, (xiSupportMultiplicity ξ₀ : ℝ)) *
            ((16 * Real.pi / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2)
          ≤ ((2 / Real.pi) * Γ * Real.log Γ) *
              ((16 * Real.pi / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2) :=
            mul_le_mul_of_nonneg_right hrvm_high (by positivity)
        _ = 32 * (Real.log Γ / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 := by
            field_simp [Real.pi_ne_zero, hΓ0.ne']; ring
    linarith
  have hGloc_sub : (∑ q ∈ G_loc,
      (∫ γ in Icc Γ (2 * Γ),
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2) / 4) ≤
      (∑ q ∈ G_loc, localZeroWeight A q) * ∫ u, F₀ u ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun q _ => ?_
    obtain ⟨_, hb1, hb2⟩ := integral_norm_paperFT_depthDiff_sq_le hF₀.continuous hF₀c hA0 hsupp
      (q.1 : ℂ) Γ (2 * Γ)
    have hsq_abs : ((q.1 : ℂ).re - 1 / 2) ^ 2 = (foldedRe q - 1 / 2) ^ 2 := by
      rw [foldedRe_sub_half_eq_abs, sq_abs]
    rw [← foldedRe_sub_half_eq_abs q] at hb1 hb2
    rw [hsq_abs] at hb2
    unfold localZeroWeight
    rcases min_cases
      ((Real.pi / 2) * Real.exp (2 * A * (foldedRe q - 1 / 2)))
      (2 * Real.pi * A ^ 2 * (foldedRe q - 1 / 2) ^ 2 * Real.exp (2 * A * (foldedRe q - 1 / 2)))
      with ⟨heq, _⟩ | ⟨heq, _⟩ <;> (rw [heq]; linarith)
  have hsel_bound := hloc_sel Γ ((le_max_left _ _).trans hΓ) A hA0 hA_κ₁ G_loc hG_loc
  have hexpA_half : Real.exp A ≤ Γ ^ (1 / 2 : ℝ) := by
    calc Real.exp A ≤ Real.exp ((1 / 2) * Real.log Γ) := Real.exp_le_exp.mpr hA_half
      _ = Γ ^ (1 / 2 : ℝ) := by rw [Real.rpow_def_of_pos hΓ0, mul_comm]
  have herr_core : (1 / Γ) * (32 * (Real.log Γ / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2) ≤
      32 * K_log1 * Γ ^ (-(4 / 3 : ℝ)) * envelopeWindowNorm F₀ ^ 2 := by
    have hlog1 : Real.log Γ ≤ K_log1 * Γ ^ (1 / 6 : ℝ) := by
      have h1 : Real.log Γ ≤ (1 + Real.log Γ) ^ 1 := by simp
      exact h1.trans (hK_log1 Γ hΓ1)
    have hrpow : (1 / Γ) * (1 / Γ) * Γ ^ (1 / 6 : ℝ) * Γ ^ (1 / 2 : ℝ) = Γ ^ (-(4 / 3 : ℝ)) := by
      have hsq : (1 / Γ) * (1 / Γ) = Γ ^ (-2 : ℝ) := by
        have h1 : (Γ ^ 2)⁻¹ = Γ ^ (-2 : ℝ) := by
          rw [← Real.rpow_natCast Γ 2, ← Real.rpow_neg hΓ0.le]; norm_num
        calc (1 / Γ) * (1 / Γ) = (Γ ^ 2)⁻¹ := by ring
          _ = Γ ^ (-2 : ℝ) := h1
      rw [hsq, ← Real.rpow_add hΓ0, ← Real.rpow_add hΓ0]; norm_num
    calc (1 / Γ) * (32 * (Real.log Γ / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2)
        ≤ (1 / Γ) * (32 * ((K_log1 * Γ ^ (1 / 6 : ℝ)) / Γ) *
            Γ ^ (1 / 2 : ℝ) * envelopeWindowNorm F₀ ^ 2) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              (mul_le_mul
                (mul_le_mul_of_nonneg_left
                  (div_le_div_of_nonneg_right hlog1 hΓ0.le) (by norm_num))
                hexpA_half (Real.exp_pos _).le (by positivity))
              (sq_nonneg _)) (by positivity)
      _ = 32 * K_log1 * ((1 / Γ) * (1 / Γ) * Γ ^ (1 / 6 : ℝ) * Γ ^ (1 / 2 : ℝ)) *
            envelopeWindowNorm F₀ ^ 2 := by ring
      _ = 32 * K_log1 * Γ ^ (-(4 / 3 : ℝ)) * envelopeWindowNorm F₀ ^ 2 := by rw [hrpow]
  have herr_rem : (1 / Γ) * ((32 * reciprocalSquareWeightTotal / Γ) *
      Real.exp A * envelopeWindowNorm F₀ ^ 2) ≤
      32 * reciprocalSquareWeightTotal * Γ ^ (-(4 / 3 : ℝ)) * envelopeWindowNorm F₀ ^ 2 := by
    have hrpow : (1 / Γ) * (1 / Γ) * Γ ^ (1 / 2 : ℝ) ≤ Γ ^ (-(4 / 3 : ℝ)) := by
      have hsq : (1 / Γ) * (1 / Γ) * Γ ^ (1 / 2 : ℝ) = Γ ^ (-(3 / 2 : ℝ)) := by
        have h1 : (Γ ^ 2)⁻¹ = Γ ^ (-2 : ℝ) := by
          rw [← Real.rpow_natCast Γ 2, ← Real.rpow_neg hΓ0.le]; norm_num
        calc (1 / Γ) * (1 / Γ) * Γ ^ (1 / 2 : ℝ) = (Γ ^ 2)⁻¹ * Γ ^ (1 / 2 : ℝ) := by ring
          _ = Γ ^ (-2 : ℝ) * Γ ^ (1 / 2 : ℝ) := by rw [h1]
          _ = Γ ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add hΓ0]; norm_num
      rw [hsq]
      exact Real.rpow_le_rpow_of_exponent_le hΓ1 (by norm_num)
    calc (1 / Γ) * ((32 * reciprocalSquareWeightTotal / Γ) *
          Real.exp A * envelopeWindowNorm F₀ ^ 2)
        ≤ (1 / Γ) * ((32 * reciprocalSquareWeightTotal / Γ) *
            Γ ^ (1 / 2 : ℝ) * envelopeWindowNorm F₀ ^ 2) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hexpA_half
                (by positivity [reciprocalSquareWeightTotal_nonneg]))
              (sq_nonneg _)) (by positivity)
      _ = 32 * reciprocalSquareWeightTotal * ((1 / Γ) * (1 / Γ) * Γ ^ (1 / 2 : ℝ)) *
            envelopeWindowNorm F₀ ^ 2 := by ring
      _ ≤ 32 * reciprocalSquareWeightTotal * Γ ^ (-(4 / 3 : ℝ)) * envelopeWindowNorm F₀ ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hrpow
              (by positivity [reciprocalSquareWeightTotal_nonneg]))
            (sq_nonneg _)
  have hmain_pos : (1 / Γ) * ((1 / 8) * Γ * Real.log Γ * (∫ u, F₀ u ^ 2)) =
      (1 / 8) * Real.log Γ * (∫ u, F₀ u ^ 2) := by field_simp [hΓ0.ne']
  have hsel_mass : (1 / Γ) * ((∑ q ∈ G_loc, localZeroWeight A q) * (∫ u, F₀ u ^ 2)) ≤
      (1 / 16) * Real.log Γ * (∫ u, F₀ u ^ 2) := by
    calc (1 / Γ) * ((∑ q ∈ G_loc, localZeroWeight A q) * (∫ u, F₀ u ^ 2))
        = ((1 / Γ) * ∑ q ∈ G_loc, localZeroWeight A q) * (∫ u, F₀ u ^ 2) := by ring
      _ ≤ ((1 / 16) * Real.log Γ) * (∫ u, F₀ u ^ 2) :=
          mul_le_mul_of_nonneg_right hsel_bound hmass_nn
      _ = (1 / 16) * Real.log Γ * (∫ u, F₀ u ^ 2) := by ring
  have h1 := mul_le_mul_of_nonneg_left hint_ge (by positivity : 0 ≤ 1 / Γ)
  have h2 := mul_le_mul_of_nonneg_left hcore_sum_ge (by positivity : 0 ≤ 1 / Γ)
  have h3 := mul_le_mul_of_nonneg_left (hsub_int.trans (add_le_add hGloc_sub le_rfl))
    (by positivity : 0 ≤ 1 / Γ)
  dsimp [C₀]
  linarith [h1, h2, h3, hmain_pos, hsel_mass, herr_core, herr_rem]

/-- **Positive Lebesgue Measure of Strictly Positive Frequencies at Logarithmic Aperture
(`exists_positive_measure_frequencies_fullZeroForm_cosineSource_pos`):**
Whenever `c₀ (log Γ) ∫ F₀² > C₀ Γ^{-4/3} envelopeWindowNorm F₀ ^ 2` (which holds for every nonzero
`F₀` at all sufficiently large `Γ`), the set of frequencies `γ ∈ [Γ, 2Γ]` where
`0 < fullZeroForm (cosineSource F₀ γ)` has strictly positive Lebesgue measure. -/
theorem exists_positive_measure_frequencies_fullZeroForm_cosineSource_pos :
    ∃ κ₀ c₀ C₀ : ℝ, 0 < κ₀ ∧ 0 < c₀ ∧ 0 ≤ C₀ ∧ ∃ Γ₀ : ℝ, 64 ≤ Γ₀ ∧
      ∀ Γ : ℝ, Γ₀ ≤ Γ → ∀ A : ℝ, 0 ≤ A → A ≤ κ₀ * Real.log Γ →
        ∀ F₀ : ℝ → ℝ, ContDiff ℝ 2 F₀ → HasCompactSupport F₀ →
          (∀ u : ℝ, A < |u| → F₀ u = 0) →
          C₀ * Γ ^ (-(4 / 3 : ℝ)) * envelopeWindowNorm F₀ ^ 2 <
            c₀ * Real.log Γ * (∫ u, F₀ u ^ 2) →
          0 < (MeasureTheory.volume
            {γ ∈ Icc Γ (2 * Γ) | 0 < fullZeroForm (cosineSource F₀ γ)}).toReal := by
  obtain ⟨κ₀, c₀, C₀, hκ₀, hc₀, hC₀, Γ₀, hΓ₀, hpos_avg⟩ :=
    exists_logarithmic_aperture_frequencyAverage_fullZeroForm_cosineSource_pos
  refine ⟨κ₀, c₀, C₀, hκ₀, hc₀, hC₀, Γ₀, hΓ₀,
    fun Γ hΓ A hA0 hA F₀ hF₀ hF₀c hsupp hstrict => ?_⟩
  have hΓ0 : 0 < Γ := lt_of_lt_of_le (by norm_num) (hΓ₀.trans hΓ)
  have havg := hpos_avg Γ hΓ A hA0 hA F₀ hF₀ hF₀c hsupp
  have hint_pos : 0 < ∫ γ in Icc Γ (2 * Γ), fullZeroForm (cosineSource F₀ γ) := by
    have hmul : 0 < (1 / Γ) * ∫ γ in Icc Γ (2 * Γ), fullZeroForm (cosineSource F₀ γ) := by
      linarith
    exact pos_of_mul_pos_right hmul (by positivity)
  let f_cos : ℝ → ℝ := fun γ => fullZeroForm (cosineSource F₀ γ)
  have hf_cont : Continuous f_cos := (continuous_zeta_W_re_modulated hF₀ hF₀c).2
  let g_pos : ℝ → ℝ := fun γ => max 0 (f_cos γ)
  have hg_cont : Continuous g_pos := continuous_const.max hf_cont
  have hg_int_pos : 0 < ∫ γ in Icc Γ (2 * Γ), g_pos γ :=
    hint_pos.trans_le (setIntegral_mono_on hf_cont.integrableOn_Icc hg_cont.integrableOn_Icc
      measurableSet_Icc fun γ _ => le_max_right 0 (f_cos γ))
  let P : Set ℝ := {γ ∈ Icc Γ (2 * Γ) | 0 < f_cos γ}
  have hP_lt_top : MeasureTheory.volume P < ⊤ :=
    (measure_mono (fun _ h => h.1 : P ⊆ Icc Γ (2 * Γ))).trans_lt
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
  have hP_ne_zero : MeasureTheory.volume P ≠ 0 := fun hnull => by
    have hae : g_pos =ᵐ[MeasureTheory.volume.restrict (Icc Γ (2 * Γ))] 0 := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc, Filter.Eventually, mem_ae_iff]
      refine measure_mono_null (fun γ hγ => ?_) hnull
      rw [Set.mem_compl_iff, Set.mem_setOf_eq] at hγ
      push Not at hγ
      refine ⟨hγ.1, ?_⟩
      by_contra hle
      push Not at hle
      exact hγ.2 (max_eq_left hle)
    have hzero : (∫ γ in Icc Γ (2 * Γ), g_pos γ) = 0 :=
      (integral_congr_ae hae).trans (by simp)
    linarith
  exact ENNReal.toReal_pos hP_ne_zero hP_lt_top.ne

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

end

#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.igmDensityExponent_le_one_sub_four_thirds
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.exists_zeroHeightBox_ncard_le_one_sub_four_thirds_uniform
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.exists_sum_exp_foldedRe_deep_decay_up_to_two_thirds_log
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.exists_sum_exp_foldedRe_threeShells_le_subpower
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.exists_frequencyAverage_abs_cosineFiltered_spectralDeficitSum_le
#print axioms GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.exists_frequencyAverage_abs_cosineFiltered_ccmPrimeDeficitIncoming_le
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.fullZeroForm_cosine_add_sine_eq_gammaBracket_add_criticalDeficit
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.scalingSubsurface_defect_cosine_add_sine_eq
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_frequencyAverage_quadrature_fullZeroForm_ge_subpower
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_frequencyAverage_fullZeroForm_cosineSource_ge_subpower
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_frequencyAverage_fullZeroForm_ge_neg_exp_every_pos_rate
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_volume_bad_frequencies_fullZeroForm_cosineSource_le
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_local_shell_depthDiff_weighted_le
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_logarithmic_aperture_frequencyAverage_fullZeroForm_cosineSource_pos
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_logarithmic_aperture_frequencyAverage_quadrature_pos
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_positive_measure_frequencies_fullZeroForm_cosineSource_pos
