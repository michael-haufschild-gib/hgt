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
  rw [hz, Complex.exp_mul_I]
  simp [Complex.mul_re, Real.cos_neg]

theorem complexModulatedSource_im (F₀ : ℝ → ℝ) (γ u : ℝ) :
    (complexModulatedSource F₀ γ u).im = -sineSource F₀ γ u := by
  unfold complexModulatedSource sineSource
  have hz : -Complex.I * (γ : ℂ) * (u : ℂ) = (((-(γ * u)) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hz, Complex.exp_mul_I]
  simp [Complex.mul_im, Real.sin_neg]

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
  simp [ZeroConfig.Wsummand, hft]

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
  rw [deriv_add (hf.differentiable one_ne_zero s) (hg.differentiable one_ne_zero s)]
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
  have h := congrArg (starRingEnd ℂ) (gammaOf_sub_real ρ ω)
  simpa using h

/-- `paperFT` shift law for `complexModulatedSource F₀ γ`. -/
theorem paperFT_complexModulatedSource (F₀ : ℝ → ℝ) (γ : ℝ) (z : ℂ) :
    paperFT (complexModulatedSource F₀ γ) z = paperFT (fun u => (F₀ u : ℂ)) (z - (γ : ℂ)) := by
  unfold paperFT complexModulatedSource
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
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
    · have heq : F₀ =ᶠ[𝓝 u] 0 := Filter.eventually_of_mem (Iio_mem_nhds (neg_lt.mp hu2)) fun s hs =>
        hsupp s (lt_abs.mpr (Or.inr (neg_lt.mpr hs)))
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
    · simp [g, hsupp u (not_le.mp hu)]
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
  rw [gammaOf_sub_real, conj_gammaOf_sub_real]
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_exp]
  have e1 : (((ρ.re - 1 / 2) * u : ℝ) : ℂ) + Complex.I * (ρ.im : ℂ) * (u : ℂ) +
      Complex.I * -(ω : ℂ) * (u : ℂ) =
      Complex.I * (((ρ.im - ω : ℝ) : ℂ) - ((ρ.re - 1 / 2 : ℝ) : ℂ) * Complex.I) * (u : ℂ) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  have e2 : ((-((ρ.re - 1 / 2) * u) : ℝ) : ℂ) + Complex.I * (ρ.im : ℂ) * (u : ℂ) +
      Complex.I * -(ω : ℂ) * (u : ℂ) =
      Complex.I * (((ρ.im - ω : ℝ) : ℂ) + ((ρ.re - 1 / 2 : ℝ) : ℂ) * Complex.I) * (u : ℂ) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [← e1, ← e2, Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_add]
  ring

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
    (f := Real.exp) (f' := Real.exp) (s := Icc (-x) x)
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    (fun t ht => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
      exact Real.exp_le_exp.mpr (ht.2.trans hxr))
    (convex_Icc (-x) x) ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩
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
  set h := depthDiffProfile F₀ ρ
  have hh_cont : Continuous h := by
    unfold h depthDiffProfile
    fun_prop
  have hh_comp : HasCompactSupport h := by
    unfold h depthDiffProfile
    exact ((hF₀c.mul_right).comp_left Complex.ofReal_zero).mul_right
  have hh1 : Integrable h := hh_cont.integrable_of_hasCompactSupport hh_comp
  have hh2 : MemLp h 2 := by
    rw [memLp_two_iff_integrable_sq_norm hh_cont.aestronglyMeasurable]
    exact (hh_cont.norm.pow 2).integrable_of_hasCompactSupport
      ((hh_comp.norm).comp_left (zero_pow two_ne_zero))
  have hint_pos : Integrable fun x : ℝ => ‖paperFT h x‖ ^ 2 := by
    have hfun : (fun x : ℝ => ‖paperFT h x‖ ^ 2) =
        fun x => (fun ξ : ℝ => ‖FourierTransform.fourier h ξ‖ ^ 2) (x / (-(2 * Real.pi))) := by
      funext x; rw [paperFT_ofReal_eq_fourier, neg_div, ← div_neg]
    rw [hfun]
    exact (GaloisForLFunctions.RHTower.integrable_norm_sq_fourier hh1 hh2).comp_div
      (by linarith [Real.pi_pos])
  have heq_fn : (fun γ : ℝ =>
      ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (γ : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (γ : ℂ))‖ ^ 2) =
      fun γ : ℝ => ‖paperFT h (-(γ : ℝ))‖ ^ 2 := by
    funext γ
    rw [← paperFT_depthDiffProfile_eq hF₀ hF₀c ρ γ, Complex.ofReal_neg]
  have hint_neg : Integrable fun γ : ℝ => ‖paperFT h (-(γ : ℝ))‖ ^ 2 := hint_pos.comp_neg
  have hint_lhs : Integrable fun γ : ℝ =>
      ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (γ : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (γ : ℂ))‖ ^ 2 := by
    rwa [heq_fn]
  have hwhole : (∫ γ : ℝ, ‖paperFT h (-(γ : ℝ))‖ ^ 2) = 2 * Real.pi * ∫ u : ℝ, ‖h u‖ ^ 2 := by
    rw [integral_neg_eq_self (fun x : ℝ => ‖paperFT h x‖ ^ 2)]
    exact RHTower.KernelStrip.integral_norm_sq_paperFT_of_memLp hh1 hh2
  have hset_le : (∫ γ in Icc a b,
      ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (γ : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (γ : ℂ))‖ ^ 2) ≤
      2 * Real.pi * ∫ u : ℝ, ‖h u‖ ^ 2 := by
    rw [heq_fn]
    exact (setIntegral_le_integral hint_neg (Eventually.of_forall fun _ => sq_nonneg _)).trans_eq hwhole
  have hint_F₀2 : Integrable fun u : ℝ => F₀ u ^ 2 :=
    (hF₀.pow 2).integrable_of_hasCompactSupport (hF₀c.comp_left (zero_pow two_ne_zero))
  have hnorm_h : ∀ u : ℝ, ‖h u‖ ^ 2 =
      F₀ u ^ 2 * (Real.exp ((ρ.re - 1 / 2) * u) - Real.exp (-((ρ.re - 1 / 2) * u))) ^ 2 := fun u => by
    dsimp [h, depthDiffProfile]
    have hexp_norm : ‖Complex.exp (Complex.I * (ρ.im : ℂ) * (u : ℂ))‖ = 1 := by
      have : Complex.I * (ρ.im : ℂ) * (u : ℂ) = ((ρ.im * u : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, hexp_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
  have hu_b1 : (∫ u : ℝ, ‖h u‖ ^ 2) ≤ Real.exp (2 * A * |ρ.re - 1 / 2|) * ∫ u, F₀ u ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono (hh_cont.norm.pow 2 |>.integrable_of_hasCompactSupport
      ((hh_comp.norm).comp_left (zero_pow two_ne_zero))) (hint_F₀2.const_mul _) fun u => ?_
    rw [hnorm_h u]
    by_cases hu : |u| ≤ A
    · have hb := (exp_sub_exp_neg_sq_le hA hu (δ := ρ.re - 1 / 2)).1
      have := mul_le_mul_of_nonneg_left hb (sq_nonneg (F₀ u))
      linarith
    · simp [hsupp u (not_le.mp hu)]
  have hu_b2 : (∫ u : ℝ, ‖h u‖ ^ 2) ≤
      4 * A ^ 2 * (ρ.re - 1 / 2) ^ 2 * Real.exp (2 * A * |ρ.re - 1 / 2|) * ∫ u, F₀ u ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono (hh_cont.norm.pow 2 |>.integrable_of_hasCompactSupport
      ((hh_comp.norm).comp_left (zero_pow two_ne_zero))) (hint_F₀2.const_mul _) fun u => ?_
    rw [hnorm_h u]
    by_cases hu : |u| ≤ A
    · have hb := (exp_sub_exp_neg_sq_le hA hu (δ := ρ.re - 1 / 2)).2
      have := mul_le_mul_of_nonneg_left hb (sq_nonneg (F₀ u))
      linarith
    · simp [hsupp u (not_le.mp hu)]
  refine ⟨hint_lhs, ?_, ?_⟩
  · calc (∫ γ in Icc a b,
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (γ : ℂ))‖ ^ 2)
        ≤ 2 * Real.pi * ∫ u : ℝ, ‖h u‖ ^ 2 := hset_le
      _ ≤ 2 * Real.pi * (Real.exp (2 * A * |ρ.re - 1 / 2|) * ∫ u, F₀ u ^ 2) :=
          mul_le_mul_of_nonneg_left hu_b1 (by positivity)
      _ = 2 * Real.pi * Real.exp (2 * A * |ρ.re - 1 / 2|) * ∫ u, F₀ u ^ 2 := by ring
  · calc (∫ γ in Icc a b,
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (γ : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (γ : ℂ))‖ ^ 2)
        ≤ 2 * Real.pi * ∫ u : ℝ, ‖h u‖ ^ 2 := hset_le
      _ ≤ 2 * Real.pi * (4 * A ^ 2 * (ρ.re - 1 / 2) ^ 2 *
            Real.exp (2 * A * |ρ.re - 1 / 2|) * ∫ u, F₀ u ^ 2) :=
          mul_le_mul_of_nonneg_left hu_b2 (by positivity)
      _ = 8 * Real.pi * A ^ 2 * (ρ.re - 1 / 2) ^ 2 * Real.exp (2 * A * |ρ.re - 1 / 2|) *
            ∫ u, F₀ u ^ 2 := by ring

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
  obtain ⟨hint, _, _⟩ := integral_norm_paperFT_depthDiff_sq_le hF₀ hF₀c hA hsupp ρ (-b) (-a)
  have hwhole : (∫ γ in Icc a b,
      ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ + (γ : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) + (γ : ℂ))‖ ^ 2) ≤
      ∫ x : ℝ,
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (x : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (x : ℂ))‖ ^ 2 := by
    have heq : (fun γ : ℝ =>
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ + (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) + (γ : ℂ))‖ ^ 2) =
        fun γ : ℝ =>
          ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - ((-γ : ℝ) : ℂ)) -
            paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - ((-γ : ℝ) : ℂ))‖ ^ 2 := by
      funext γ; simp [sub_neg_eq_add]
    rw [heq]
    exact (setIntegral_le_integral hint.comp_neg (Eventually.of_forall fun _ => sq_nonneg _)).trans_eq
      (integral_neg_eq_self _)
  -- Reuse the whole-line evaluation from `depthDiffProfile`
  set h := depthDiffProfile F₀ ρ
  have hh_cont : Continuous h := by unfold h depthDiffProfile; fun_prop
  have hh_comp : HasCompactSupport h :=
    ((hF₀c.mul_right).comp_left Complex.ofReal_zero).mul_right
  have hh1 : Integrable h := hh_cont.integrable_of_hasCompactSupport hh_comp
  have hh2 : MemLp h 2 := by
    rw [memLp_two_iff_integrable_sq_norm hh_cont.aestronglyMeasurable]
    exact (hh_cont.norm.pow 2).integrable_of_hasCompactSupport
      ((hh_comp.norm).comp_left (zero_pow two_ne_zero))
  have heq_fn : (fun x : ℝ =>
      ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf ρ - (x : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf ρ) - (x : ℂ))‖ ^ 2) =
      fun x : ℝ => ‖paperFT h (-x)‖ ^ 2 := by
    funext x
    rw [← paperFT_depthDiffProfile_eq hF₀ hF₀c ρ x, Complex.ofReal_neg]
  rw [heq_fn, integral_neg_eq_self (fun x : ℝ => ‖paperFT h x‖ ^ 2),
    RHTower.KernelStrip.integral_norm_sq_paperFT_of_memLp hh1 hh2] at hwhole
  have hint_F₀2 : Integrable fun u : ℝ => F₀ u ^ 2 :=
    (hF₀.pow 2).integrable_of_hasCompactSupport (hF₀c.comp_left (zero_pow two_ne_zero))
  have hnorm_h : ∀ u : ℝ, ‖h u‖ ^ 2 =
      F₀ u ^ 2 * (Real.exp ((ρ.re - 1 / 2) * u) - Real.exp (-((ρ.re - 1 / 2) * u))) ^ 2 := fun u => by
    dsimp [h, depthDiffProfile]
    have hexp_norm : ‖Complex.exp (Complex.I * (ρ.im : ℂ) * (u : ℂ))‖ = 1 := by
      have : Complex.I * (ρ.im : ℂ) * (u : ℂ) = ((ρ.im * u : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, hexp_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
  have hu_b1 : (∫ u : ℝ, ‖h u‖ ^ 2) ≤ Real.exp (2 * A * |ρ.re - 1 / 2|) * ∫ u, F₀ u ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono (hh_cont.norm.pow 2 |>.integrable_of_hasCompactSupport
      ((hh_comp.norm).comp_left (zero_pow two_ne_zero))) (hint_F₀2.const_mul _) fun u => ?_
    rw [hnorm_h u]
    by_cases hu : |u| ≤ A
    · have hb := (exp_sub_exp_neg_sq_le hA hu (δ := ρ.re - 1 / 2)).1
      linarith [mul_le_mul_of_nonneg_left hb (sq_nonneg (F₀ u))]
    · simp [hsupp u (not_le.mp hu)]
  have hu_b2 : (∫ u : ℝ, ‖h u‖ ^ 2) ≤
      4 * A ^ 2 * (ρ.re - 1 / 2) ^ 2 * Real.exp (2 * A * |ρ.re - 1 / 2|) * ∫ u, F₀ u ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono (hh_cont.norm.pow 2 |>.integrable_of_hasCompactSupport
      ((hh_comp.norm).comp_left (zero_pow two_ne_zero))) (hint_F₀2.const_mul _) fun u => ?_
    rw [hnorm_h u]
    by_cases hu : |u| ≤ A
    · have hb := (exp_sub_exp_neg_sq_le hA hu (δ := ρ.re - 1 / 2)).2
      linarith [mul_le_mul_of_nonneg_left hb (sq_nonneg (F₀ u))]
    · simp [hsupp u (not_le.mp hu)]
  exact ⟨hwhole.trans ((mul_le_mul_of_nonneg_left hu_b1 (by positivity)).trans_eq (by ring)),
    hwhole.trans ((mul_le_mul_of_nonneg_left hu_b2 (by positivity)).trans_eq (by ring))⟩

/-- Exact multiplicity-preserving `tsum` bridge between `XiZeroCopy` and `zetaZeroConfig.carrier`. -/
theorem summable_zetaCarrier_of_xiZeroCopy {g : ℂ → ℝ} (hg0 : ∀ z, 0 ≤ g z)
    (hg : Summable fun q : XiZeroCopy => g (q.1 : ℂ)) :
    Summable fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.mult ρ : ℝ) * g (ρ : ℂ) := by
  rw [← xiDivisorZetaCarrierEquiv.summable_iff]
  set f : XiZeroCopy → ℝ≥0 := fun q => ⟨g (q.1 : ℂ), hg0 _⟩
  have hf : Summable f := NNReal.summable_coe.mp hg
  have hsig : Summable fun ρ : XiDivisorSupport => ∑' i, f ⟨ρ, i⟩ := NNReal.summable_sigma.mp hf
  have hsigR : Summable fun ρ : XiDivisorSupport => ((∑' i, f ⟨ρ, i⟩ : ℝ≥0) : ℝ) :=
    NNReal.summable_coe.mpr hsig
  refine hsigR.congr fun ρ => ?_
  simp only [Function.comp_apply, NNReal.coe_tsum, f, NNReal.coe_mk, tsum_fintype,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
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
      (summable_zetaCarrier_of_xiZeroCopy (fun _ => by positivity)
        summable_inv_norm_sq_xiZeroCopy).mul_left K
    have hcont_on : ContinuousOn (fun γ : ℝ => ∑' ρ, Φ γ ρ) (Metric.closedBall 0 M) :=
      continuousOn_tsum (fun ρ => (hΦ_cont ρ).continuousOn) hsum_base fun ρ γ hγ =>
        hdom γ (by simpa [Metric.mem_closedBall, Real.dist_eq] using hγ) ρ
    exact hcont_on.continuousAt (Metric.closedBall_mem_nhds_of_mem
      (by simp [Metric.mem_closedBall, Real.dist_eq, M]))
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
          simpa [div_eq_mul_one_div] using hb1
      _ ≤ Real.exp (A₀ / 2) * envelopeWindowNorm F₀ *
            (2 * (1 + M) ^ 2 * (2 / ‖(ρ : ℂ)‖ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (Real.exp_pos _).le (envelopeWindowNorm_nonneg F₀))
          exact hinv_peano.trans (mul_le_mul_of_nonneg_left
            (inv_one_add_im_sq_le_two_div_norm_sq hρ.2.1 hρ.2.2) (by positivity))
      _ = Real.exp (A₀ / 2) * envelopeWindowNorm F₀ * (2 * (1 + M) ^ 2) *
            (2 / ‖(ρ : ℂ)‖ ^ 2) := by ring
  set C₀_w : ℝ := Real.exp (A₀ / 2) * envelopeWindowNorm F₀
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
      have hprod := mul_le_mul hs1 hs2 (norm_nonneg _) (by positivity)
      calc (zetaZeroConfig.mult ρ : ℝ) *
            (‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ))‖ *
              ‖paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖)
          ≤ (zetaZeroConfig.mult ρ : ℝ) *
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
      have hprod := mul_le_mul ha hb (norm_nonneg _) (by positivity)
      calc (zetaZeroConfig.mult ρ : ℝ) *
            (‖(paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) +
                paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ))) / 2‖ *
              ‖(paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ)) +
                paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))) / 2‖)
          ≤ (zetaZeroConfig.mult ρ : ℝ) *
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

/-- Master bound on the `Icc Γ (2 * Γ)` integral of the single-shift depth-difference series
`Σ_ρ m_ρ ‖paperFT F₀_ℂ (γ_ρ ∓ γ) - paperFT F₀_ℂ (conj γ_ρ ∓ γ)‖² / 4`, shared by §2, §3, and §4. -/
theorem integral_Icc_tsum_depthDiff_div_four_le {F₀ : ℝ → ℝ}
    (hF₀ : ContDiff ℝ 2 F₀) (hF₀c : HasCompactSupport F₀)
    {Γ A : ℝ} (hΓ : 1 ≤ Γ) (hA : 0 ≤ A) (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0) :
    let d_sub : zetaZeroConfig.carrier → ℝ → ℝ := fun ρ γ =>
      (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) - (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4
    let d_add : zetaZeroConfig.carrier → ℝ → ℝ := fun ρ γ =>
      (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (ρ : ℂ) + (γ : ℂ)) -
          paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))‖ ^ 2 / 4
    (∀ γ : ℝ, Summable fun ρ => d_sub ρ γ) ∧
    (∀ γ : ℝ, Summable fun ρ => d_add ρ γ) ∧
    ContinuousOn (fun γ => ∑' ρ, d_sub ρ γ) (Icc Γ (2 * Γ)) ∧
    ContinuousOn (fun γ => ∑' ρ, d_add ρ γ) (Icc Γ (2 * Γ)) ∧
    ∃ G_loc : Finset XiZeroCopy,
      (∀ q ∈ G_loc, Γ / 2 ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 4 * Γ) ∧
      (∫ γ in Icc Γ (2 * Γ), ∑' ρ, d_sub ρ γ) ≤
        (∑ q ∈ G_loc,
          (∫ γ in Icc Γ (2 * Γ),
            ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
              paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2) / 4) +
          (32 * reciprocalSquareWeightTotal / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 ∧
      (∫ γ in Icc Γ (2 * Γ), ∑' ρ, d_add ρ γ) ≤
        (∑ q ∈ G_loc,
          (∫ γ in Icc Γ (2 * Γ),
            ‖paperFT (fun u => (F₀ u : ℂ)) (gammaOf (q.1 : ℂ) + (γ : ℂ)) -
              paperFT (fun u => (F₀ u : ℂ)) (conj (gammaOf (q.1 : ℂ)) + (γ : ℂ))‖ ^ 2) / 4) +
          (32 * reciprocalSquareWeightTotal / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 := by
  classical
  dsimp only
  set F_c : ℝ → ℂ := fun u => (F₀ u : ℂ)
  set d_sub : zetaZeroConfig.carrier → ℝ → ℝ := fun ρ γ =>
    (zetaZeroConfig.mult ρ : ℝ) *
      ‖paperFT F_c (gammaOf (ρ : ℂ) - (γ : ℂ)) -
        paperFT F_c (conj (gammaOf (ρ : ℂ)) - (γ : ℂ))‖ ^ 2 / 4
  set d_add : zetaZeroConfig.carrier → ℝ → ℝ := fun ρ γ =>
    (zetaZeroConfig.mult ρ : ℝ) *
      ‖paperFT F_c (gammaOf (ρ : ℂ) + (γ : ℂ)) -
        paperFT F_c (conj (gammaOf (ρ : ℂ)) + (γ : ℂ))‖ ^ 2 / 4
  have hS_fin : ({q : XiZeroCopy | Γ / 2 ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 4 * Γ}).Finite :=
    (finite_xiOrdinateWindow (4 * Γ) 0).subset fun q hq => by
      rw [mem_xiOrdinateWindow_iff, sub_zero]; exact hq.2
  obtain ⟨G_loc, hmem_Gloc⟩ : ∃ G_loc : Finset XiZeroCopy,
      ∀ q : XiZeroCopy, q ∈ G_loc ↔ Γ / 2 ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 4 * Γ :=
    ⟨hS_fin.toFinset, fun _ => hS_fin.mem_toFinset⟩
  have hΓ0 : 0 < Γ := by linarith
  -- Continuity of `z ↦ paperFT F_c z`
  have hft_cont : Continuous (fun z : ℂ => paperFT F_c z) := by
    have hint_F₀ : Integrable fun u : ℝ => |F₀ u| :=
      hF₀.continuous.abs.integrable_of_hasCompactSupport hF₀c.abs
    rw [continuous_iff_continuousAt]
    intro z₀
    refine continuousAt_of_dominated
      (bound := fun u : ℝ => |F₀ u| * Real.exp (A * (|z₀.im| + 1)))
      (Eventually.of_forall fun z =>
        (((Complex.continuous_ofReal.comp hF₀.continuous).mul (by fun_prop)).aestronglyMeasurable))
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
    · simp [F_c, hsupp u (not_le.mp hu)]
  -- Pointwise Lorentzian bound on `‖paperFT F_c (gammaOf ρ - ω) - paperFT F_c (conj (gammaOf ρ) - ω)‖² / 4`
  have hdiff_lor : ∀ (z : ℂ) (ω : ℝ), 0 < z.re → z.re < 1 →
      ‖paperFT F_c (gammaOf z - (ω : ℂ)) - paperFT F_c (conj (gammaOf z) - (ω : ℂ))‖ ^ 2 / 4 ≤
        Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / (1 + (z.im - ω) ^ 2) ^ 2) := by
    intro z ω hz0 hz1
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
    have htri : ‖paperFT F_c (gammaOf z - (ω : ℂ)) - paperFT F_c (conj (gammaOf z) - (ω : ℂ))‖ ≤
        2 * Real.exp (A / 2) * envelopeWindowNorm F₀ / (1 + (z.im - ω) ^ 2) := by
      calc ‖paperFT F_c (gammaOf z - (ω : ℂ)) - paperFT F_c (conj (gammaOf z) - (ω : ℂ))‖
          ≤ ‖paperFT F_c (gammaOf z - (ω : ℂ))‖ + ‖paperFT F_c (conj (gammaOf z) - (ω : ℂ))‖ :=
            norm_sub_le _ _
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
    calc ‖paperFT F_c (gammaOf z - (ω : ℂ)) - paperFT F_c (conj (gammaOf z) - (ω : ℂ))‖ ^ 2 / 4
        ≤ (2 * Real.exp (A / 2) * envelopeWindowNorm F₀ / (1 + (z.im - ω) ^ 2)) ^ 2 / 4 :=
          div_le_div_of_nonneg_right hsq (by norm_num)
      _ = Real.exp (A / 2) ^ 2 * envelopeWindowNorm F₀ ^ 2 * (1 / (1 + (z.im - ω) ^ 2) ^ 2) := by
          ring
      _ = Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / (1 + (z.im - ω) ^ 2) ^ 2) := by
          rw [hexpA]
  -- Summability at any fixed `ω : ℝ`
  have hsum_ω : ∀ ω : ℝ, Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT F_c (gammaOf (ρ : ℂ) - (ω : ℂ)) -
          paperFT F_c (conj (gammaOf (ρ : ℂ)) - (ω : ℂ))‖ ^ 2 / 4 := by
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
    set K_ω : ℝ := Real.exp A * envelopeWindowNorm F₀ ^ 2 * (4 * (1 + |ω|) ^ 2)
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun ρ => ?_)
      ((summable_zetaCarrier_of_xiZeroCopy (fun _ => by positivity)
        summable_inv_norm_sq_xiZeroCopy).mul_left K_ω)
    have hρ := ρ.2
    have h1 := (hdiff_lor (ρ : ℂ) ω hρ.2.1 hρ.2.2).trans
      (mul_le_mul_of_nonneg_left (hpeano_ω (ρ : ℂ) hρ.2.1 hρ.2.2)
        (by positivity))
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    calc (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT F_c (gammaOf (ρ : ℂ) - (ω : ℂ)) -
            paperFT F_c (conj (gammaOf (ρ : ℂ)) - (ω : ℂ))‖ ^ 2 / 4
        = (zetaZeroConfig.mult ρ : ℝ) *
            (‖paperFT F_c (gammaOf (ρ : ℂ) - (ω : ℂ)) -
              paperFT F_c (conj (gammaOf (ρ : ℂ)) - (ω : ℂ))‖ ^ 2 / 4) := by ring
      _ ≤ (zetaZeroConfig.mult ρ : ℝ) *
            (Real.exp A * envelopeWindowNorm F₀ ^ 2 *
              (4 * (1 + |ω|) ^ 2 * (1 / ‖(ρ : ℂ)‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left h1 hm
      _ = K_ω * ((zetaZeroConfig.mult ρ : ℝ) * (1 / ‖(ρ : ℂ)‖ ^ 2)) := by dsimp [K_ω]; ring
  -- Uniform majorant on `γ ∈ Icc Γ (2 * Γ)` for both `d_sub` and `d_add`
  set u_dom : zetaZeroConfig.carrier → ℝ := fun ρ =>
    Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 * (1 + 2 * Γ) ^ 2) *
      ((zetaZeroConfig.mult ρ : ℝ) * (1 / ‖(ρ : ℂ)‖ ^ 2))
  have hu_dom_sum : Summable u_dom :=
    (summable_zetaCarrier_of_xiZeroCopy (fun _ => by positivity)
      summable_inv_norm_sq_xiZeroCopy).mul_left _
  have hdom_Icc : ∀ ω : ℝ, |ω| ≤ 2 * Γ → ∀ ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT F_c (gammaOf (ρ : ℂ) - (ω : ℂ)) -
          paperFT F_c (conj (gammaOf (ρ : ℂ)) - (ω : ℂ))‖ ^ 2 / 4 ≤ u_dom ρ := by
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
        4 * (1 + 2 * Γ) ^ 2 * (2 / ‖(ρ : ℂ)‖ ^ 2) := by
      calc 1 / (1 + ((ρ : ℂ).im - ω) ^ 2) ^ 2
          = (1 / (1 + ((ρ : ℂ).im - ω) ^ 2)) * (1 / (1 + ((ρ : ℂ).im - ω) ^ 2)) := by simp [sq]
        _ ≤ (2 * (1 + 2 * Γ) ^ 2 * (2 / ‖(ρ : ℂ)‖ ^ 2)) * 1 := by
            refine mul_le_mul ?_ hinv2 (by positivity) (by positivity)
            exact hinv1.trans (mul_le_mul_of_nonneg_left
              (inv_one_add_im_sq_le_two_div_norm_sq hρ.2.1 hρ.2.2) (by positivity))
        _ = 4 * (1 + 2 * Γ) ^ 2 * (2 / ‖(ρ : ℂ)‖ ^ 2) := by ring
    have h1 := (hdiff_lor (ρ : ℂ) ω hρ.2.1 hρ.2.2).trans
      (mul_le_mul_of_nonneg_left hlor2 (by positivity))
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    calc (zetaZeroConfig.mult ρ : ℝ) *
          ‖paperFT F_c (gammaOf (ρ : ℂ) - (ω : ℂ)) -
            paperFT F_c (conj (gammaOf (ρ : ℂ)) - (ω : ℂ))‖ ^ 2 / 4
        = (zetaZeroConfig.mult ρ : ℝ) *
            (‖paperFT F_c (gammaOf (ρ : ℂ) - (ω : ℂ)) -
              paperFT F_c (conj (gammaOf (ρ : ℂ)) - (ω : ℂ))‖ ^ 2 / 4) := by ring
      _ ≤ (zetaZeroConfig.mult ρ : ℝ) *
            (Real.exp A * envelopeWindowNorm F₀ ^ 2 *
              (4 * (1 + 2 * Γ) ^ 2 * (2 / ‖(ρ : ℂ)‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left h1 hm
      _ ≤ u_dom ρ := by
          dsimp [u_dom]
          have : 0 ≤ Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 + 2 * Γ) ^ 2 *
              ((zetaZeroConfig.mult ρ : ℝ) * (1 / ‖(ρ : ℂ)‖ ^ 2)) := by positivity
          linarith
  have hd_sub_cont : ∀ ρ, Continuous (d_sub ρ) := fun ρ => by dsimp [d_sub]; fun_prop
  have hd_add_cont : ∀ ρ, Continuous (d_add ρ) := fun ρ => by dsimp [d_add]; fun_prop
  obtain ⟨hc_sub, hswap_sub⟩ := integral_tsum_nonneg_Icc hd_sub_cont
    (fun _ _ => by dsimp [d_sub]; positivity) hu_dom_sum
    (fun ρ γ hγ => hdom_Icc γ (abs_le.mpr ⟨by linarith [hγ.1], hγ.2⟩) ρ)
  obtain ⟨hc_add, hswap_add⟩ := integral_tsum_nonneg_Icc hd_add_cont
    (fun _ _ => by dsimp [d_add]; positivity) hu_dom_sum
    (fun ρ γ hγ => by
      simpa [d_add, sub_neg_eq_add] using
        hdom_Icc (-γ) (by rw [abs_neg]; exact abs_le.mpr ⟨by linarith [hγ.1], hγ.2⟩) ρ)
  -- Convert `∑' ρ : zetaZeroConfig.carrier` to `∑' q : XiZeroCopy` via `tsum_xiZeroCopy_eq_zetaCarrier`
  set g_sub : ℂ → ℝ := fun z =>
    (∫ γ in Icc Γ (2 * Γ),
      ‖paperFT F_c (gammaOf z - (γ : ℂ)) - paperFT F_c (conj (gammaOf z) - (γ : ℂ))‖ ^ 2) / 4
  set g_add : ℂ → ℝ := fun z =>
    (∫ γ in Icc Γ (2 * Γ),
      ‖paperFT F_c (gammaOf z + (γ : ℂ)) - paperFT F_c (conj (gammaOf z) + (γ : ℂ))‖ ^ 2) / 4
  have hg_sub_xi_sum : Summable fun q : XiZeroCopy => g_sub (q.1 : ℂ) := by
    refine Summable.of_nonneg_of_le (fun q => div_nonneg (integral_nonneg fun _ => sq_nonneg _) (by norm_num))
      (fun q => ?_)
      (summable_inv_norm_sq_xiZeroCopy.mul_left
        (Γ * (Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 * (1 + 2 * Γ) ^ 2))))
    set ρ_c : zetaZeroConfig.carrier := xiDivisorZetaCarrierEquiv q.1
    have hpt_q : ∀ γ ∈ Icc Γ (2 * Γ),
        ‖paperFT F_c (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
          paperFT F_c (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2 / 4 ≤
          Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 * (1 + 2 * Γ) ^ 2) *
            (1 / ‖(q.1 : ℂ)‖ ^ 2) := fun γ hγ => by
      have hm1 : 1 ≤ (zetaZeroConfig.mult ρ_c : ℝ) := by
        exact_mod_cast zetaZeroConfig.one_le_mult (ρ_c : ℂ) ρ_c.2
      have hd := hdom_Icc γ (abs_le.mpr ⟨by linarith [hγ.1], hγ.2⟩) ρ_c
      have hrc : (ρ_c : ℂ) = (q.1 : ℂ) := rfl
      rw [hrc] at hd
      dsimp [u_dom] at hd
      rw [hrc] at hd
      have hm_pos : 0 < (zetaZeroConfig.mult ρ_c : ℝ) := by linarith
      have hd' : (zetaZeroConfig.mult ρ_c : ℝ) *
          (‖paperFT F_c (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
            paperFT F_c (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2 / 4) ≤
          (zetaZeroConfig.mult ρ_c : ℝ) *
            (Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 * (1 + 2 * Γ) ^ 2) *
              (1 / ‖(q.1 : ℂ)‖ ^ 2)) := by linarith
      exact le_of_mul_le_mul_left hd' hm_pos
    have hdiv_int : g_sub (q.1 : ℂ) = ∫ γ in Icc Γ (2 * Γ),
        ‖paperFT F_c (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
          paperFT F_c (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2 / 4 :=
      (integral_div 4 _).symm
    rw [hdiv_int]
    calc (∫ γ in Icc Γ (2 * Γ),
          ‖paperFT F_c (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
            paperFT F_c (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2 / 4)
        ≤ ∫ _γ in Icc Γ (2 * Γ),
            Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 * (1 + 2 * Γ) ^ 2) *
              (1 / ‖(q.1 : ℂ)‖ ^ 2) :=
          setIntegral_mono_on (by fun_prop : Continuous fun γ : ℝ =>
            ‖paperFT F_c (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
              paperFT F_c (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2 / 4).integrableOn_Icc
            continuous_const.integrableOn_Icc measurableSet_Icc hpt_q
      _ = Γ * (Real.exp A * envelopeWindowNorm F₀ ^ 2 * (16 * (1 + 2 * Γ) ^ 2)) *
            (1 / ‖(q.1 : ℂ)‖ ^ 2) := by
          rw [setIntegral_const, Measure.real, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * Γ - Γ),
            show 2 * Γ - Γ = Γ by ring, smul_eq_mul, mul_assoc]
  have hg_add_xi_sum : Summable fun q : XiZeroCopy => g_add (q.1 : ℂ) := by
    have hrefl : (fun q : XiZeroCopy => g_add (q.1 : ℂ)) =
        fun q : XiZeroCopy => g_sub ((xiZeroCopyConjEquiv q).1 : ℂ) := by
      funext q
      have hcq : ((xiZeroCopyConjEquiv q).1 : ℂ) = conj (q.1 : ℂ) := rfl
      dsimp [g_add, g_sub]
      congr 1
      refine setIntegral_congr_fun measurableSet_Icc fun γ _ => ?_
      rw [hcq]
      -- `‖A - B‖²` is invariant under complex conjugation `conj (paperFT F_c z) = paperFT F_c (-conj z)`
      have hreal_ft : ∀ w : ℂ, conj (paperFT F_c w) = paperFT F_c (-conj w) := fun w => by
        unfold paperFT
        have hint : Integrable fun u : ℝ => F_c u * Complex.exp (Complex.I * w * (u : ℂ)) :=
          ((Complex.continuous_ofReal.comp hF₀.continuous).mul
            (by fun_prop)).integrable_of_hasCompactSupport ((hF₀c.comp_left Complex.ofReal_zero).mul_right)
        rw [← Complex.conjCLE.integral_comp_comm hint]
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only [Complex.conjCLE_apply, map_mul, F_c, Complex.conj_ofReal, ← Complex.exp_conj]
        congr 2
        simp
      have hz1 : -conj (gammaOf (conj (q.1 : ℂ)) - (γ : ℂ)) = conj (gammaOf (q.1 : ℂ)) + (γ : ℂ) := by
        rw [gammaOf_sub_real, conj_gammaOf_sub_real]; apply Complex.ext <;> simp
      have hz2 : -conj (conj (gammaOf (conj (q.1 : ℂ))) - (γ : ℂ)) = gammaOf (q.1 : ℂ) + (γ : ℂ) := by
        rw [gammaOf_sub_real, conj_gammaOf_sub_real]; apply Complex.ext <;> simp
      have hnorm_eq : ‖paperFT F_c (gammaOf (conj (q.1 : ℂ)) - (γ : ℂ)) -
            paperFT F_c (conj (gammaOf (conj (q.1 : ℂ))) - (γ : ℂ))‖ =
          ‖paperFT F_c (gammaOf (q.1 : ℂ) + (γ : ℂ)) -
            paperFT F_c (conj (gammaOf (q.1 : ℂ)) + (γ : ℂ))‖ := by
        rw [← Complex.norm_conj (paperFT F_c (gammaOf (conj (q.1 : ℂ)) - (γ : ℂ)) -
          paperFT F_c (conj (gammaOf (conj (q.1 : ℂ))) - (γ : ℂ))),
          map_sub, hreal_ft, hreal_ft, hz1, hz2, norm_sub_rev]
      rw [hnorm_eq]
    rw [hrefl]
    exact xiZeroCopyConjEquiv.summable_iff.mpr hg_sub_xi_sum
  -- Split `∑' q : XiZeroCopy, g_sub (q.1 : ℂ)` and `g_add` into `G_loc` + remote
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
  have hg_sub_rem : ∀ q : XiZeroCopy, (|(q.1 : ℂ).im| < Γ / 2 ∨ 4 * Γ < |(q.1 : ℂ).im|) →
      g_sub (q.1 : ℂ) ≤ (32 / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 *
        (1 / ‖(q.1 : ℂ)‖ ^ 2) := fun q hq => by
    have hdiv_int : g_sub (q.1 : ℂ) = ∫ γ in Icc Γ (2 * Γ),
        ‖paperFT F_c (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
          paperFT F_c (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2 / 4 := (integral_div 4 _).symm
    rw [hdiv_int]
    have hpt : ∀ γ ∈ Icc Γ (2 * Γ),
        ‖paperFT F_c (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
          paperFT F_c (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2 / 4 ≤
          (32 / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / ‖(q.1 : ℂ)‖ ^ 2) :=
      fun γ hγ => by
        have h1 := hdiff_lor (q.1 : ℂ) γ (xiZeroCopy_re_pos q) (xiZeroCopy_re_lt_one q)
        have h2 := (inv_one_add_sq_remote_le hΓ hγ.1 hγ.2 hq).2
        have h3 := inv_one_add_im_sq_le_two_div_norm_sq (xiZeroCopy_re_pos q) (xiZeroCopy_re_lt_one q)
        calc ‖paperFT F_c (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
              paperFT F_c (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2 / 4
            ≤ Real.exp A * envelopeWindowNorm F₀ ^ 2 *
                ((16 / Γ ^ 2) * (2 / ‖(q.1 : ℂ)‖ ^ 2)) :=
              h1.trans (mul_le_mul_of_nonneg_left
                (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))) (by positivity))
          _ = (32 / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / ‖(q.1 : ℂ)‖ ^ 2) := by
              ring
    calc (∫ γ in Icc Γ (2 * Γ),
          ‖paperFT F_c (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
            paperFT F_c (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2 / 4)
        ≤ ∫ _γ in Icc Γ (2 * Γ),
            (32 / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / ‖(q.1 : ℂ)‖ ^ 2) :=
          setIntegral_mono_on (by fun_prop : Continuous fun γ : ℝ =>
            ‖paperFT F_c (gammaOf (q.1 : ℂ) - (γ : ℂ)) -
              paperFT F_c (conj (gammaOf (q.1 : ℂ)) - (γ : ℂ))‖ ^ 2 / 4).integrableOn_Icc
            continuous_const.integrableOn_Icc measurableSet_Icc hpt
      _ = Γ * ((32 / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / ‖(q.1 : ℂ)‖ ^ 2)) := by
          rw [setIntegral_const, Measure.real, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * Γ - Γ),
            show 2 * Γ - Γ = Γ by ring, smul_eq_mul]
      _ = (32 / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / ‖(q.1 : ℂ)‖ ^ 2) := by
          field_simp [hΓ0.ne']
  have hg_add_rem : ∀ q : XiZeroCopy, (|(q.1 : ℂ).im| < Γ / 2 ∨ 4 * Γ < |(q.1 : ℂ).im|) →
      g_add (q.1 : ℂ) ≤ (32 / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 *
        (1 / ‖(q.1 : ℂ)‖ ^ 2) := fun q hq => by
    have hdiv_int : g_add (q.1 : ℂ) = ∫ γ in Icc Γ (2 * Γ),
        ‖paperFT F_c (gammaOf (q.1 : ℂ) + (γ : ℂ)) -
          paperFT F_c (conj (gammaOf (q.1 : ℂ)) + (γ : ℂ))‖ ^ 2 / 4 := (integral_div 4 _).symm
    rw [hdiv_int]
    have hpt : ∀ γ ∈ Icc Γ (2 * Γ),
        ‖paperFT F_c (gammaOf (q.1 : ℂ) + (γ : ℂ)) -
          paperFT F_c (conj (gammaOf (q.1 : ℂ)) + (γ : ℂ))‖ ^ 2 / 4 ≤
          (32 / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / ‖(q.1 : ℂ)‖ ^ 2) :=
      fun γ hγ => by
        have h1 : ‖paperFT F_c (gammaOf (q.1 : ℂ) + (γ : ℂ)) -
            paperFT F_c (conj (gammaOf (q.1 : ℂ)) + (γ : ℂ))‖ ^ 2 / 4 ≤
            Real.exp A * envelopeWindowNorm F₀ ^ 2 *
              (1 / (1 + ((q.1 : ℂ).im + γ) ^ 2) ^ 2) := by
          simpa [sub_neg_eq_add] using
            hdiff_lor (q.1 : ℂ) (-γ) (xiZeroCopy_re_pos q) (xiZeroCopy_re_lt_one q)
        have h2 := (inv_one_add_sq_remote_add_le hΓ hγ.1 hγ.2 hq).2
        have h3 := inv_one_add_im_sq_le_two_div_norm_sq (xiZeroCopy_re_pos q) (xiZeroCopy_re_lt_one q)
        calc ‖paperFT F_c (gammaOf (q.1 : ℂ) + (γ : ℂ)) -
              paperFT F_c (conj (gammaOf (q.1 : ℂ)) + (γ : ℂ))‖ ^ 2 / 4
            ≤ Real.exp A * envelopeWindowNorm F₀ ^ 2 *
                ((16 / Γ ^ 2) * (2 / ‖(q.1 : ℂ)‖ ^ 2)) :=
              h1.trans (mul_le_mul_of_nonneg_left
                (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))) (by positivity))
          _ = (32 / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / ‖(q.1 : ℂ)‖ ^ 2) := by
              ring
    calc (∫ γ in Icc Γ (2 * Γ),
          ‖paperFT F_c (gammaOf (q.1 : ℂ) + (γ : ℂ)) -
            paperFT F_c (conj (gammaOf (q.1 : ℂ)) + (γ : ℂ))‖ ^ 2 / 4)
        ≤ ∫ _γ in Icc Γ (2 * Γ),
            (32 / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / ‖(q.1 : ℂ)‖ ^ 2) :=
          setIntegral_mono_on (by fun_prop : Continuous fun γ : ℝ =>
            ‖paperFT F_c (gammaOf (q.1 : ℂ) + (γ : ℂ)) -
              paperFT F_c (conj (gammaOf (q.1 : ℂ)) + (γ : ℂ))‖ ^ 2 / 4).integrableOn_Icc
            continuous_const.integrableOn_Icc measurableSet_Icc hpt
      _ = Γ * ((32 / Γ ^ 2) * Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / ‖(q.1 : ℂ)‖ ^ 2)) := by
          rw [setIntegral_const, Measure.real, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * Γ - Γ),
            show 2 * Γ - Γ = Γ by ring, smul_eq_mul]
      _ = (32 / Γ) * Real.exp A * envelopeWindowNorm F₀ ^ 2 * (1 / ‖(q.1 : ℂ)‖ ^ 2) := by
          field_simp [hΓ0.ne']
  have htsum_sub_eq : (∑' ρ, ∫ γ in Icc Γ (2 * Γ), d_sub ρ γ) = ∑' q : XiZeroCopy, g_sub (q.1 : ℂ) := by
    rw [tsum_xiZeroCopy_eq_zetaCarrier hg_sub_xi_sum]
    refine tsum_congr fun ρ => ?_
    dsimp [d_sub, g_sub]
    rw [integral_div, integral_const_mul, mul_div_assoc]
  have htsum_add_eq : (∑' ρ, ∫ γ in Icc Γ (2 * Γ), d_add ρ γ) = ∑' q : XiZeroCopy, g_add (q.1 : ℂ) := by
    rw [tsum_xiZeroCopy_eq_zetaCarrier hg_add_xi_sum]
    refine tsum_congr fun ρ => ?_
    dsimp [d_add, g_add]
    rw [integral_div, integral_const_mul, mul_div_assoc]
  refine ⟨fun γ => hsum_ω γ, fun γ => by simpa [d_add, sub_neg_eq_add] using hsum_ω (-γ),
    hc_sub, hc_add, G_loc, fun q hq => (hmem_Gloc q).mp hq, ?_, ?_⟩
  · rw [hswap_sub, htsum_sub_eq]
    exact hbound_xi g_sub hg_sub_xi_sum
      (fun _ => div_nonneg (integral_nonneg fun _ => sq_nonneg _) (by norm_num)) hg_sub_rem
  · rw [hswap_add, htsum_add_eq]
    exact hbound_xi g_add hg_add_xi_sum
      (fun _ => div_nonneg (integral_nonneg fun _ => sq_nonneg _) (by norm_num)) hg_add_rem
