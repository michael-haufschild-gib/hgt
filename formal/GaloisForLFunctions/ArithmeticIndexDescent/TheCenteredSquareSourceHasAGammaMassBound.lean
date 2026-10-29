import GaloisForLFunctions.ArithmeticIndexDescent.TheCenteredSquareBoundaryHasAGammaMassBound
import GaloisForLFunctions.ArithmeticIndexDescent.TheSquarePrimeEstimateHoldsOnCompleteProfiles
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCCMMixedScrewWeilBridge

/-!
# A Gamma and mass bound for the centred physical square source

The exact Fourier boundary identity transfers the centred multiplier estimate
to smooth mixed sources. Pole-preserving convolution then gives the same bound
on compact BV profiles. Mean and ordinary mass corrections stay explicit, so
no orthogonality is required during smoothing.
-/

noncomputable section
open MeasureTheory Set Filter Topology FourierTransform SchwartzMap Complex
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent
open GaloisForLFunctions.RHTower ArithmeticCastelnuovoSeveri.LogCells
open HTGeometry SpacingScaleHarmonicAnalysis

/-- The square source with its ordinary mean pole and constant Fourier multiplier removed. -/
def centeredSquarePrimeSource (f : ℝ → ℝ) : ℝ :=
  squarePrimeSource f - (1 / 2 : ℝ) * (∫ x, f x) ^ 2 -
    squarePrimeRegularSymbol 0 * ∫ x, f x ^ 2

private def centeredSquareDensity (U : SchwartzMap ℝ ℂ) (ξ : ℝ) : ℝ :=
  (squarePrimeRegularSymbol (2 * Real.pi * ξ) - squarePrimeRegularSymbol 0) *
    ‖𝓕 (U : ℝ → ℂ) ξ‖ ^ 2

private theorem integrable_centeredSquareDensity (U : SchwartzMap ℝ ℂ) :
    Integrable (centeredSquareDensity U) := by
  have he : centeredSquareDensity U = fun ξ => regularSquareDampedSpectralDensity U 0 ξ -
      squarePrimeRegularSymbol 0 * ‖𝓕 (U : ℝ → ℂ) ξ‖ ^ 2 := by
    funext ξ
    rw [centeredSquareDensity, regularSquareDensity_zero_eq, sub_mul]
  rw [he]
  exact (integrable_regularSquareDampedSpectralDensity U (le_refl 0)).sub
    ((integrable_spectralDensity U).const_mul _)

private theorem centeredSquarePrimeSource_core {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    centeredSquarePrimeSource u = ∫ ξ, centeredSquareDensity (suzukiRestrictedWeilCoreSchwartz u) ξ := by
  have he : centeredSquareDensity (suzukiRestrictedWeilCoreSchwartz u) = fun ξ =>
      regularSquareDampedSpectralDensity (suzukiRestrictedWeilCoreSchwartz u) 0 ξ -
        squarePrimeRegularSymbol 0 * ‖𝓕 (suzukiRestrictedWeilCoreSchwartz u : ℝ → ℂ) ξ‖ ^ 2 := by
    funext ξ
    rw [centeredSquareDensity, regularSquareDensity_zero_eq, sub_mul]
  rw [he, integral_sub
    (integrable_regularSquareDampedSpectralDensity _ (le_refl 0))
    ((integrable_spectralDensity _).const_mul _), integral_const_mul,
    integral_core_spectralDensity, centeredSquarePrimeSource,
    squarePrimeSource_eq_regular_add_real_mean]
  ring

private theorem abs_complex_mixed_sq_le (z w : ℂ) :
    |‖z + w‖ ^ 2 - ‖z‖ ^ 2 - ‖w‖ ^ 2| ≤ 2 * ‖z‖ * ‖w‖ := by
  have he : ‖z + w‖ ^ 2 - ‖z‖ ^ 2 - ‖w‖ ^ 2 = 2 * (z * (starRingEnd ℂ) w).re := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [he, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc 2 * |(z * (starRingEnd ℂ) w).re| ≤ 2 * ‖z * (starRingEnd ℂ) w‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
    _ = _ := by rw [norm_mul, Complex.norm_conj]; ring

private theorem coreSchwartz_add {a : ℝ} (u v : SuzukiRestrictedWeilCore a) :
    suzukiRestrictedWeilCoreSchwartz (suzukiRestrictedWeilCoreAdd u v) =
      suzukiRestrictedWeilCoreSchwartz u + suzukiRestrictedWeilCoreSchwartz v := by
  ext x
  exact Complex.ofReal_add (u x) (v x)

private theorem fourier_schwartz_add (U V : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    𝓕 ((U + V : SchwartzMap ℝ ℂ) : ℝ → ℂ) ξ =
      𝓕 (U : ℝ → ℂ) ξ + 𝓕 (V : ℝ → ℂ) ξ := by
  change (𝓕 (U + V)) ξ = (𝓕 U) ξ + (𝓕 V) ξ
  rw [FourierTransform.fourier_add]
  rfl

/-- A support-independent bound on the mixed centred square source of real smooth cores. -/
theorem exists_centeredSquareSource_gamma_mass_core {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ) (u v : SuzukiRestrictedWeilCore a),
      |centeredSquarePrimeSource (fun x => u x + v x) - centeredSquarePrimeSource u -
          centeredSquarePrimeSource v| ≤
        ε * (levyEnergy u + levyEnergy v) + C * ∫ x, v x ^ 2 := by
  obtain ⟨C, hC, hsymbol⟩ := exists_centeredSquare_gamma_mass_bound hε
  refine ⟨C, hC, ?_⟩
  intro a u v
  let U := suzukiRestrictedWeilCoreSchwartz u
  let V := suzukiRestrictedWeilCoreSchwartz v
  have hU := integrable_centeredSquareDensity U
  have hV := integrable_centeredSquareDensity V
  have hS := integrable_centeredSquareDensity (U + V)
  have hGu : Integrable (fun ξ : ℝ => gammaIncrementSymbol (2 * Real.pi * ξ) *
      ‖𝓕 (U : ℝ → ℂ) ξ‖ ^ 2) := integrable_core_gammaDensity u
  have hGv : Integrable (fun ξ : ℝ => gammaIncrementSymbol (2 * Real.pi * ξ) *
      ‖𝓕 (V : ℝ → ℂ) ξ‖ ^ 2) := integrable_core_gammaDensity v
  have hρ := integrable_spectralDensity V
  have hpoint (ξ : ℝ) :
      |centeredSquareDensity (U + V) ξ - centeredSquareDensity U ξ -
          centeredSquareDensity V ξ| ≤
        ε * (gammaIncrementSymbol (2 * Real.pi * ξ) * ‖𝓕 (U : ℝ → ℂ) ξ‖ ^ 2 +
          gammaIncrementSymbol (2 * Real.pi * ξ) * ‖𝓕 (V : ℝ → ℂ) ξ‖ ^ 2) +
          C * ‖𝓕 (V : ℝ → ℂ) ξ‖ ^ 2 := by
    have he : centeredSquareDensity (U + V) ξ - centeredSquareDensity U ξ -
        centeredSquareDensity V ξ =
        (squarePrimeRegularSymbol (2 * Real.pi * ξ) - squarePrimeRegularSymbol 0) *
          (‖𝓕 (U : ℝ → ℂ) ξ + 𝓕 (V : ℝ → ℂ) ξ‖ ^ 2 -
            ‖𝓕 (U : ℝ → ℂ) ξ‖ ^ 2 - ‖𝓕 (V : ℝ → ℂ) ξ‖ ^ 2) := by
      simp only [centeredSquareDensity, fourier_schwartz_add]
      ring
    rw [he, abs_mul]
    have hpol := mul_le_mul_of_nonneg_left
      (abs_complex_mixed_sq_le (𝓕 (U : ℝ → ℂ) ξ) (𝓕 (V : ℝ → ℂ) ξ))
      (abs_nonneg (squarePrimeRegularSymbol (2 * Real.pi * ξ) - squarePrimeRegularSymbol 0))
    have hs := hsymbol (2 * Real.pi * ξ) ‖𝓕 (U : ℝ → ℂ) ξ‖ ‖𝓕 (V : ℝ → ℂ) ξ‖
    rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at hs
    linarith only [hpol, hs]
  have hSU : Integrable (fun ξ => centeredSquareDensity (U + V) ξ - centeredSquareDensity U ξ) :=
    hS.sub hU
  have hmix : Integrable (fun ξ => centeredSquareDensity (U + V) ξ -
      centeredSquareDensity U ξ - centeredSquareDensity V ξ) := hSU.sub hV
  have hGsum : Integrable (fun ξ : ℝ =>
      gammaIncrementSymbol (2 * Real.pi * ξ) * ‖𝓕 (U : ℝ → ℂ) ξ‖ ^ 2 +
        gammaIncrementSymbol (2 * Real.pi * ξ) * ‖𝓕 (V : ℝ → ℂ) ξ‖ ^ 2) := hGu.add hGv
  have hright : Integrable (fun ξ : ℝ =>
      ε * (gammaIncrementSymbol (2 * Real.pi * ξ) * ‖𝓕 (U : ℝ → ℂ) ξ‖ ^ 2 +
        gammaIncrementSymbol (2 * Real.pi * ξ) * ‖𝓕 (V : ℝ → ℂ) ξ‖ ^ 2) +
        C * ‖𝓕 (V : ℝ → ℂ) ξ‖ ^ 2) := (hGsum.const_mul ε).add (hρ.const_mul C)
  have hi := (norm_integral_le_integral_norm
    (fun ξ => centeredSquareDensity (U + V) ξ - centeredSquareDensity U ξ -
      centeredSquareDensity V ξ)).trans
      (integral_mono hmix.norm hright (fun ξ => by
        simpa only [Real.norm_eq_abs] using hpoint ξ))
  simp only [Real.norm_eq_abs] at hi
  rw [integral_sub hSU hV, integral_sub hS hU,
    integral_add (hGsum.const_mul ε) (hρ.const_mul C), integral_const_mul,
    integral_const_mul, integral_add hGu hGv] at hi
  change |centeredSquarePrimeSource (suzukiRestrictedWeilCoreAdd u v) -
    centeredSquarePrimeSource u - centeredSquarePrimeSource v| ≤ _
  rw [centeredSquarePrimeSource_core, centeredSquarePrimeSource_core,
    centeredSquarePrimeSource_core, coreSchwartz_add]
  dsimp only [U, V] at hi
  rw [integral_core_gammaDensity, integral_core_gammaDensity, integral_core_spectralDensity] at hi
  exact hi

private theorem poleSmooth_add_compact_bv {f g : ℝ → ℝ}
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ) (n : ℕ) :
    poleSmooth (fun x => f x + g x) n = fun x => poleSmooth f n x + poleSmooth g n x := by
  apply poleSmooth_add (measurable_of_boundedVariation_univ hf) (measurable_of_boundedVariation_univ hg)
    (show 0 ≤ ‖f 0‖ + (eVariationOn f univ).toReal by positivity)
    (show 0 ≤ ‖g 0‖ + (eVariationOn g univ).toReal by positivity)
  · intro x
    simpa only [Real.norm_eq_abs] using norm_le_of_boundedVariation_univ hf x
  · intro x
    simpa only [Real.norm_eq_abs] using norm_le_of_boundedVariation_univ hg x

/-- The centred literal source converges under the common pole-preserving smoothing. -/
theorem tendsto_poleSmooth_centeredSquareSource {f : ℝ → ℝ}
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    Tendsto (fun n => centeredSquarePrimeSource (poleSmooth f n)) atTop
      (𝓝 (centeredSquarePrimeSource f)) := by
  obtain ⟨R, _, hR⟩ := exists_nonneg_supported_radius hc
  have hf2 := memLp_compact_bv hv hc
  have hf1 : Integrable f := by
    simpa only [mul_one] using integrable_compact_bv_mul hv hc
      (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))
  exact ((tendsto_poleSmooth_squarePrimeSource hf2 hR).sub
    (((tendsto_poleSmooth_mean hf1).pow 2).const_mul (1 / 2 : ℝ))).sub
      ((tendsto_poleSmooth_square_mass hf2).const_mul (squarePrimeRegularSymbol 0))

/-- Arbitrarily little Gamma plus mass of only the second profile controls every centred BV mix. -/
theorem exists_centeredSquareSource_gamma_mass_bv {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : ℝ → ℝ),
      BoundedVariationOn f univ → HasCompactSupport f →
      BoundedVariationOn g univ → HasCompactSupport g →
      |centeredSquarePrimeSource (fun x => f x + g x) - centeredSquarePrimeSource f -
          centeredSquarePrimeSource g| ≤
        ε * (levyEnergy f + levyEnergy g) + C * ∫ x, g x ^ 2 := by
  obtain ⟨C, hC, hcore⟩ := exists_centeredSquareSource_gamma_mass_core hε
  refine ⟨C, hC, ?_⟩
  intro f g hfv hfc hgv hgc
  obtain ⟨Rf, hRf, hfR⟩ := exists_nonneg_supported_radius hfc
  obtain ⟨Rg, hRg, hgR⟩ := exists_nonneg_supported_radius hgc
  have hR : 0 ≤ max Rf Rg := hRf.trans (le_max_left _ _)
  have hfR' : SupportedIn (max Rf Rg) f :=
    fun x hx => hfR x ((le_max_left _ _).trans_lt hx)
  have hgR' : SupportedIn (max Rf Rg) g :=
    fun x hx => hgR x ((le_max_right _ _).trans_lt hx)
  have hf2 := memLp_compact_bv hfv hfc
  have hg2 := memLp_compact_bv hgv hgc
  have hsumv : BoundedVariationOn (fun x => f x + g x) univ := by
    simpa only [neg_one_mul, sub_neg_eq_add] using
      boundedVariationOn_sub hfv (bv_const_mul (-1) hgv)
  have hsumc : HasCompactSupport (fun x => f x + g x) := hfc.add hgc
  have hl := (((tendsto_poleSmooth_centeredSquareSource hsumv hsumc).sub
    (tendsto_poleSmooth_centeredSquareSource hfv hfc)).sub
      (tendsto_poleSmooth_centeredSquareSource hgv hgc)).abs
  have hr := (((tendsto_poleSmooth_levyEnergy hfv hfc).add
    (tendsto_poleSmooth_levyEnergy hgv hgc)).const_mul ε).add
      ((tendsto_poleSmooth_square_mass hg2).const_mul C)
  apply le_of_tendsto_of_tendsto hl hr
  apply Eventually.of_forall
  intro n
  dsimp only
  rw [poleSmooth_add_compact_bv hfv hgv n]
  exact hcore (max Rf Rg + 1) (squarePrimeSmoothCore hf2 hR hfR' n)
    (squarePrimeSmoothCore hg2 hR hgR' n)

end GaloisForLFunctions.ArithmeticIndexDescent
