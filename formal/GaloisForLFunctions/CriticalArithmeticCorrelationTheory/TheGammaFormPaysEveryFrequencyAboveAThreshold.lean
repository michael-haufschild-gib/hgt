import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheTiltedSplineKeepsAGammaReserveAtEveryOverlap
import GaloisForLFunctions.RHTower.LebesgueAtomWeilPositivity
import GaloisForLFunctions.RHTower.EvenSectorFarBumpPoleFreeCombination

/-!
# The Gamma form pays every frequency above a threshold

The archimedean form of a real test is `archForm f = (1/2π) ∫ |f̂(r)|² Ω(r) dr` with
`Ω(r) ≥ log |r| − G₀` for `|r| ≥ T > 0` and `Ω ≥ −(G₀ + log 2)` everywhere. Splitting the Fourier
mass at `|r| = T` (`lowFourierMass`, `highFourierMass`, which add up to `∫ f²`) gives

`archForm f ≥ (log T − G₀) high_T(f) + (log R − log T) band_R(f) − (G₀ + log 2) low_T(f)`

for `0 < T ≤ R`, where `band_R` is the mass on `[R, 101R]` (`archForm_ge_high_band`). Polarized
Plancherel (`integral_mul_eq_paperFT_re`) turns a pairing `∫ f h` into the same frequency split,
and weighted AM-GM on each side gives
`2|∫ f h| ≤ μ low_T(f) + μ⁻¹ low_T(h) + λ high_T(f) + λ⁻¹ high_T(h)`
(`two_mul_abs_integral_mul_le`): a high-frequency partner is paid by `log T` per unit of its own
high mass.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Zeta23 RHTower
open scoped ComplexConjugate

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open ArithmeticCastelnuovoSeveri ArithmeticPositivityTheory

/-- The frequencies at or above a threshold. -/
def highFrequencies (T : ℝ) : Set ℝ := {r : ℝ | T ≤ |r|}

theorem measurableSet_highFrequencies (T : ℝ) : MeasurableSet (highFrequencies T) :=
  measurableSet_le measurable_const continuous_abs.measurable

/-- The Fourier mass of a real test at frequencies `|r| ≥ T`, normalized as `∫ f²`. -/
def highFourierMass (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  1 / (2 * Real.pi) * ∫ r in highFrequencies T, ‖paperFT (cx f) r‖ ^ 2

/-- The Fourier mass of a real test at frequencies `|r| < T`. -/
def lowFourierMass (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  1 / (2 * Real.pi) * ∫ r in (highFrequencies T)ᶜ, ‖paperFT (cx f) r‖ ^ 2

theorem highFourierMass_nonneg (f : ℝ → ℝ) (T : ℝ) : 0 ≤ highFourierMass f T :=
  mul_nonneg (by positivity) (setIntegral_nonneg (measurableSet_highFrequencies T)
    fun _ _ => sq_nonneg _)

theorem lowFourierMass_nonneg (f : ℝ → ℝ) (T : ℝ) : 0 ≤ lowFourierMass f T :=
  mul_nonneg (by positivity) (setIntegral_nonneg (measurableSet_highFrequencies T).compl
    fun _ _ => sq_nonneg _)

/-- **Plancherel split**: the low and high Fourier masses add up to `∫ f²`. -/
theorem lowFourierMass_add_highFourierMass {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (T : ℝ) :
    lowFourierMass f T + highFourierMass f T = ∫ u, f u ^ 2 := by
  have hint := integrable_normSq_paperFT_ofReal hf hfc
  have hsplit := integral_add_compl (measurableSet_highFrequencies T) hint
  have hpl := LebesgueAtomWeil.integral_norm_sq_paperFT_eq
    (Complex.ofRealCLM.contDiff.comp hf) (hfc.comp_left Complex.ofReal_zero)
  simp only [Function.comp_def, Complex.ofRealCLM_apply, Complex.norm_real, Real.norm_eq_abs,
    sq_abs] at hpl
  unfold lowFourierMass highFourierMass cx
  rw [← mul_add, add_comm, hsplit]
  exact hpl

/-- **The Gamma form pays the high frequencies.** For `0 < T ≤ R`, the archimedean form keeps
`log T` (less the offset) on every frequency `|r| ≥ T`, an extra `log R − log T` on the band
`[R, 101R]`, and loses at most `G₀ + log 2` on the low frequencies. -/
theorem archForm_ge_high_band {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {T R : ℝ} (hT : 0 < T) (hTR : T ≤ R) :
    (Real.log T - factorialSpanGammaOffset) * highFourierMass f T +
        (Real.log R - Real.log T) * (1 / (2 * Real.pi) *
          ∫ r in Icc R (101 * R), ‖paperFT (cx f) r‖ ^ 2) -
      (factorialSpanGammaOffset + Real.log 2) * lowFourierMass f T ≤ archForm f := by
  set F : ℝ → ℝ := fun r => ‖paperFT (cx f) r‖ ^ 2
  have hFi : Integrable F := integrable_normSq_paperFT_ofReal hf hfc
  have hGi : Integrable (fun r => F r * EF.gammaBracket r) :=
    integrable_normSq_paperFT_mul_gammaBracket hf hfc
  set H := highFrequencies T
  set B := Icc R (101 * R)
  have hHm : MeasurableSet H := measurableSet_highFrequencies T
  have hBm : MeasurableSet B := measurableSet_Icc
  have hBH : B ⊆ H := fun r hr => hTR.trans (hr.1.trans (le_abs_self r))
  have hF0 : ∀ r, 0 ≤ F r := fun r => sq_nonneg _
  have hlogTR : 0 ≤ Real.log R - Real.log T := sub_nonneg.mpr (Real.log_le_log hT hTR)
  set a := Real.log T - factorialSpanGammaOffset
  set b := Real.log R - Real.log T
  set d := factorialSpanGammaOffset + Real.log 2
  set ℓ : ℝ → ℝ := fun r => a * H.indicator F r + b * B.indicator F r - d * Hᶜ.indicator F r
  have hpt : ∀ r, ℓ r ≤ F r * EF.gammaBracket r := by
    intro r
    dsimp only [ℓ]
    by_cases hrH : r ∈ H
    · have hγ := gammaBracket_ge_log_of_le_abs hT hrH
      rw [indicator_of_mem hrH, indicator_of_notMem (fun h : r ∈ Hᶜ => h hrH), mul_zero, sub_zero]
      by_cases hrB : r ∈ B
      · have hγR := gammaBracket_ge_log_of_le_abs (hT.trans_le hTR)
          (hrB.1.trans (le_abs_self r))
        rw [indicator_of_mem hrB]
        have := mul_le_mul_of_nonneg_left hγR (hF0 r)
        dsimp only [a, b]; nlinarith
      · rw [indicator_of_notMem hrB, mul_zero, add_zero]
        have := mul_le_mul_of_nonneg_left hγ (hF0 r)
        dsimp only [a]; nlinarith
    · have hγ := gammaBracket_ge_neg_offset r
      rw [indicator_of_notMem hrH, indicator_of_mem (show r ∈ Hᶜ from hrH),
        indicator_of_notMem (fun h => hrH (hBH h))]
      have := mul_le_mul_of_nonneg_left hγ (hF0 r)
      dsimp only [d]; nlinarith
  have hA : Integrable (fun r => a * H.indicator F r) := (hFi.indicator hHm).const_mul a
  have hB : Integrable (fun r => b * B.indicator F r) := (hFi.indicator hBm).const_mul b
  have hC : Integrable (fun r => d * Hᶜ.indicator F r) := (hFi.indicator hHm.compl).const_mul d
  have hAB : Integrable (fun r => a * H.indicator F r + b * B.indicator F r) := hA.add hB
  have hℓi : Integrable ℓ := hAB.sub hC
  have hint : ∫ r, ℓ r = a * (∫ r in H, F r) + b * (∫ r in B, F r) - d * ∫ r in Hᶜ, F r := by
    have e1 := integral_sub (f := fun r => a * H.indicator F r + b * B.indicator F r)
      (g := fun r => d * Hᶜ.indicator F r) hAB hC
    have e2 := integral_add (f := fun r => a * H.indicator F r)
      (g := fun r => b * B.indicator F r) hA hB
    dsimp only [ℓ]
    rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_indicator hHm, integral_indicator hBm, integral_indicator hHm.compl]
  have hmono := integral_mono hℓi hGi hpt
  have harch : archForm f = 1 / (2 * Real.pi) * ∫ r, F r * EF.gammaBracket r := rfl
  have hhigh : highFourierMass f T = 1 / (2 * Real.pi) * ∫ r in H, F r := rfl
  have hlow : lowFourierMass f T = 1 / (2 * Real.pi) * ∫ r in Hᶜ, F r := rfl
  rw [harch, hhigh, hlow]
  rw [hint] at hmono
  have hpi : 0 < 1 / (2 * Real.pi) := by positivity
  have := mul_le_mul_of_nonneg_left hmono hpi.le
  have hBi : (1 / (2 * Real.pi) * ∫ r in Icc R (101 * R), ‖paperFT (cx f) r‖ ^ 2) =
      1 / (2 * Real.pi) * ∫ r in B, F r := rfl
  rw [hBi]
  linarith

/-- The transform of `f + s h` is `f̂ + s ĥ`. -/
private theorem paperFT_add_smul_cx {f h : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hh : Continuous h) (hhc : HasCompactSupport h) (s r : ℝ) :
    paperFT (cx fun u => f u + s * h u) r = paperFT (cx f) r + s * paperFT (cx h) r := by
  have := EvenSector.paperFT_ofReal_add_smul hf hfc hh hhc 1 s r
  simp only [one_mul, Complex.ofReal_one] at this
  exact this

/-- Plancherel for `f + s h`, written through the two transforms. -/
private theorem plancherel_add_smul {f h : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hh : ContDiff ℝ 2 h) (hhc : HasCompactSupport h) (s : ℝ) :
    Integrable (fun r : ℝ => ‖paperFT (cx f) r + s * paperFT (cx h) r‖ ^ 2) ∧
      1 / (2 * Real.pi) * ∫ r : ℝ, ‖paperFT (cx f) r + s * paperFT (cx h) r‖ ^ 2 =
        ∫ u, (f u + s * h u) ^ 2 := by
  have hg : ContDiff ℝ 2 (fun u => f u + s * h u) := hf.add (contDiff_const.mul hh)
  have hgc : HasCompactSupport (fun u => f u + s * h u) := hfc.add (hhc.mul_left)
  have hlin := paperFT_add_smul_cx hf.continuous hfc hh.continuous hhc s
  have hint := integrable_normSq_paperFT_ofReal hg hgc
  have hpl := LebesgueAtomWeil.integral_norm_sq_paperFT_eq
    (Complex.ofRealCLM.contDiff.comp hg) (hgc.comp_left Complex.ofReal_zero)
  simp only [Function.comp_def, Complex.ofRealCLM_apply, Complex.norm_real, Real.norm_eq_abs,
    sq_abs] at hpl
  have hfun : (fun r : ℝ => ‖paperFT (fun u => ((f u + s * h u : ℝ) : ℂ)) r‖ ^ 2) =
      fun r : ℝ => ‖paperFT (cx f) r + s * paperFT (cx h) r‖ ^ 2 := by
    funext r; rw [← hlin r]; rfl
  refine ⟨?_, ?_⟩
  · rw [← hfun]; exact hint
  · rw [← hfun]; exact hpl

/-- The real part of `a · conj b` by polarization. -/
private theorem re_mul_conj_eq_polar (a b : ℂ) :
    (a * conj b).re = (‖a + ((1 : ℝ) : ℂ) * b‖ ^ 2 - ‖a + ((-1 : ℝ) : ℂ) * b‖ ^ 2) / 4 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.ofReal_one, one_mul,
    Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul, ← sub_eq_add_neg, Complex.normSq_add,
    Complex.normSq_sub]
  ring

/-- `2xy ≤ t x² + t⁻¹ y²` for `t > 0`. -/
private theorem two_mul_le_weighted {x y t : ℝ} (ht : 0 < t) :
    2 * (x * y) ≤ t * x ^ 2 + t⁻¹ * y ^ 2 := by
  have key : t * (2 * (x * y)) ≤ t * (t * x ^ 2 + t⁻¹ * y ^ 2) := by
    have e : t * (t * x ^ 2 + t⁻¹ * y ^ 2) = t ^ 2 * x ^ 2 + y ^ 2 := by field_simp
    rw [e]; nlinarith [sq_nonneg (t * x - y)]
  exact le_of_mul_le_mul_left key ht

/-- The polarized integrand is integrable. -/
theorem integrable_re_paperFT_mul_conj {f h : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hh : ContDiff ℝ 2 h) (hhc : HasCompactSupport h) :
    Integrable (fun r : ℝ => (paperFT (cx f) r * conj (paperFT (cx h) r)).re) := by
  have hi₁ := (plancherel_add_smul hf hfc hh hhc 1).1
  have hi₂ := (plancherel_add_smul hf hfc hh hhc (-1)).1
  have hI : Integrable (fun r : ℝ => (‖paperFT (cx f) r + ((1 : ℝ) : ℂ) * paperFT (cx h) r‖ ^ 2 -
      ‖paperFT (cx f) r + ((-1 : ℝ) : ℂ) * paperFT (cx h) r‖ ^ 2) / 4) :=
    (hi₁.sub hi₂).div_const 4
  exact hI.congr (Filter.Eventually.of_forall fun r => (re_mul_conj_eq_polar _ _).symm)

/-- **Polarized Plancherel** for real tests: `∫ f h = (1/2π) ∫ Re(f̂ · conj ĥ)`. -/
theorem integral_mul_eq_paperFT_re {f h : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hh : ContDiff ℝ 2 h) (hhc : HasCompactSupport h) :
    ∫ u, f u * h u = 1 / (2 * Real.pi) *
      ∫ r : ℝ, (paperFT (cx f) r * conj (paperFT (cx h) r)).re := by
  obtain ⟨hi₁, hp₁⟩ := plancherel_add_smul hf hfc hh hhc 1
  obtain ⟨hi₂, hp₂⟩ := plancherel_add_smul hf hfc hh hhc (-1)
  have hre : ∫ r : ℝ, (paperFT (cx f) r * conj (paperFT (cx h) r)).re =
      ((∫ r : ℝ, ‖paperFT (cx f) r + ((1 : ℝ) : ℂ) * paperFT (cx h) r‖ ^ 2) -
        ∫ r : ℝ, ‖paperFT (cx f) r + ((-1 : ℝ) : ℂ) * paperFT (cx h) r‖ ^ 2) / 4 := by
    rw [← integral_sub hi₁ hi₂, ← integral_div]
    exact integral_congr_ae (Filter.Eventually.of_forall fun r => re_mul_conj_eq_polar _ _)
  have hf2 : Integrable (fun u => f u ^ 2) :=
    SpacingScaleHarmonicAnalysis.integrable_sq_of_continuous hf.continuous hfc
  have hh2 : Integrable (fun u => h u ^ 2) :=
    SpacingScaleHarmonicAnalysis.integrable_sq_of_continuous hh.continuous hhc
  have hfh : Integrable (fun u => f u * h u) :=
    (hf.continuous.mul hh.continuous).integrable_of_hasCompactSupport hfc.mul_right
  have hexp : ∀ s : ℝ, ∫ u, (f u + s * h u) ^ 2 =
      (∫ u, f u ^ 2) + 2 * s * (∫ u, f u * h u) + s ^ 2 * ∫ u, h u ^ 2 := by
    intro s
    have e : (fun u => (f u + s * h u) ^ 2) =
        fun u => (f u ^ 2 + (2 * s) * (f u * h u)) + s ^ 2 * h u ^ 2 := by
      funext u; ring
    have i1 : Integrable (fun u => f u ^ 2 + (2 * s) * (f u * h u)) :=
      hf2.add (hfh.const_mul (2 * s))
    have i2 : Integrable (fun u => s ^ 2 * h u ^ 2) := hh2.const_mul (s ^ 2)
    rw [e, integral_add i1 i2, integral_add hf2 (hfh.const_mul (2 * s)), integral_const_mul,
      integral_const_mul]
  have k1 := hexp 1
  have k2 := hexp (-1)
  rw [hre]
  linarith

/-- **Frequency-split pairing.** For real tests `f, h` and weights `μ, λ > 0`,
`2 |∫ f h| ≤ μ low(f) + μ⁻¹ low(h) + λ high(f) + λ⁻¹ high(h)` at any threshold `T`. -/
theorem two_mul_abs_integral_mul_le {f h : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hh : ContDiff ℝ 2 h) (hhc : HasCompactSupport h) (T : ℝ)
    {μ lam : ℝ} (hμ : 0 < μ) (hlam : 0 < lam) :
    2 * |∫ u, f u * h u| ≤ μ * lowFourierMass f T + μ⁻¹ * lowFourierMass h T +
      lam * highFourierMass f T + lam⁻¹ * highFourierMass h T := by
  have hint := integrable_re_paperFT_mul_conj hf hfc hh hhc
  have heq := integral_mul_eq_paperFT_re hf hfc hh hhc
  have hAi : Integrable (fun r : ℝ => ‖paperFT (cx f) r‖ ^ 2) :=
    integrable_normSq_paperFT_ofReal hf hfc
  have hBi : Integrable (fun r : ℝ => ‖paperFT (cx h) r‖ ^ 2) :=
    integrable_normSq_paperFT_ofReal hh hhc
  have hamgm : ∀ (t : ℝ), 0 < t → ∀ r : ℝ,
      2 * |(paperFT (cx f) r * conj (paperFT (cx h) r)).re| ≤
        t * ‖paperFT (cx f) r‖ ^ 2 + t⁻¹ * ‖paperFT (cx h) r‖ ^ 2 := by
    intro t ht r
    have h1 : |(paperFT (cx f) r * conj (paperFT (cx h) r)).re| ≤
        ‖paperFT (cx f) r‖ * ‖paperFT (cx h) r‖ := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, Complex.norm_conj]
    have h2 := two_mul_le_weighted (x := ‖paperFT (cx f) r‖) (y := ‖paperFT (cx h) r‖) ht
    linarith
  have hHm := measurableSet_highFrequencies T
  have habs := hint.abs
  have hsplit := integral_add_compl hHm habs
  have hH : ∫ r in highFrequencies T, 2 * |(paperFT (cx f) r * conj (paperFT (cx h) r)).re| ≤
      ∫ r in highFrequencies T, (lam * ‖paperFT (cx f) r‖ ^ 2 + lam⁻¹ * ‖paperFT (cx h) r‖ ^ 2) :=
    setIntegral_mono_on (habs.integrableOn.const_mul 2)
      ((hAi.integrableOn.const_mul lam).add (hBi.integrableOn.const_mul lam⁻¹)) hHm
      fun r _ => hamgm lam hlam r
  rw [integral_const_mul, integral_add (hAi.integrableOn.const_mul lam)
    (hBi.integrableOn.const_mul lam⁻¹), integral_const_mul, integral_const_mul] at hH
  have hL : ∫ r in (highFrequencies T)ᶜ, 2 * |(paperFT (cx f) r * conj (paperFT (cx h) r)).re| ≤
      ∫ r in (highFrequencies T)ᶜ, (μ * ‖paperFT (cx f) r‖ ^ 2 + μ⁻¹ * ‖paperFT (cx h) r‖ ^ 2) :=
    setIntegral_mono_on (habs.integrableOn.const_mul 2)
      ((hAi.integrableOn.const_mul μ).add (hBi.integrableOn.const_mul μ⁻¹)) hHm.compl
      fun r _ => hamgm μ hμ r
  rw [integral_const_mul, integral_add (hAi.integrableOn.const_mul μ)
    (hBi.integrableOn.const_mul μ⁻¹), integral_const_mul, integral_const_mul] at hL
  have habsint := abs_integral_le_integral_abs (f := fun r : ℝ =>
    (paperFT (cx f) r * conj (paperFT (cx h) r)).re) (μ := volume)
  have hpi : 0 < 1 / (2 * Real.pi) := by positivity
  rw [heq, abs_mul, abs_of_pos hpi]
  unfold lowFourierMass highFourierMass
  have key : 2 * |∫ r : ℝ, (paperFT (cx f) r * conj (paperFT (cx h) r)).re| ≤
      μ * (∫ r in (highFrequencies T)ᶜ, ‖paperFT (cx f) r‖ ^ 2) +
        μ⁻¹ * (∫ r in (highFrequencies T)ᶜ, ‖paperFT (cx h) r‖ ^ 2) +
      (lam * (∫ r in highFrequencies T, ‖paperFT (cx f) r‖ ^ 2) +
        lam⁻¹ * (∫ r in highFrequencies T, ‖paperFT (cx h) r‖ ^ 2)) := by
    linarith
  have := mul_le_mul_of_nonneg_left key hpi.le
  linarith

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
