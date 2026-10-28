import GaloisForLFunctions.ArithmeticIndexDescent.TheSquarePrimeSourceIsItsBoundaryPairing
import GaloisForLFunctions.ArithmeticIndexDescent.TheSquarePrimeBoundaryRetainsGammaEnergy
import GaloisForLFunctions.RHTower.WeilMarkovOddSectorTrivialZeroSquares

/-!
# Coercivity of the literal square-prime source

Plancherel and the Gamma jump identity transport the exact boundary gap
to the original real smooth profile. The mean pole remains explicit.
The resulting lower bound retains both a uniform Gamma share and a
positive ordinary L² mass floor.
-/

noncomputable section
open MeasureTheory Set Filter Topology FourierTransform SchwartzMap Complex
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent
open GaloisForLFunctions.RHTower

theorem coreSchwartz_coe {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    (suzukiRestrictedWeilCoreSchwartz u : ℝ → ℂ) = fun x => (u x : ℂ) := by
  funext x
  exact suzukiRestrictedWeilCoreSchwartz_apply u x

theorem integrable_core_gammaDensity {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    Integrable (fun ξ : ℝ => gammaIncrementSymbol (2 * Real.pi * ξ) *
      ‖𝓕 (suzukiRestrictedWeilCoreSchwartz u : ℝ → ℂ) ξ‖ ^ 2) := by
  have hcont : Continuous (fun x => (u x : ℂ)) := Complex.continuous_ofReal.comp u.continuous
  have hc : HasCompactSupport (fun x => (u x : ℂ)) :=
    u.hasCompactSupport.comp_left Complex.ofReal_zero
  rw [coreSchwartz_coe]
  exact integrable_archSymbol_sub_zero_mul_normSq_fourier
    (hcont.integrable_of_hasCompactSupport hc) (hcont.memLp_of_hasCompactSupport hc)
    (integrable_gammaHardy_normSq_fourier_ofReal (u.smooth.of_le (by norm_num)) u.hasCompactSupport)

/-- The Gamma increment is the original jump energy, without any archimedean mass shift. -/
theorem integral_core_gammaDensity {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    (∫ ξ : ℝ, gammaIncrementSymbol (2 * Real.pi * ξ) *
      ‖𝓕 (suzukiRestrictedWeilCoreSchwartz u : ℝ → ℂ) ξ‖ ^ 2) = levyEnergy u := by
  have hcont : Continuous (fun x => (u x : ℂ)) := Complex.continuous_ofReal.comp u.continuous
  have hc : HasCompactSupport (fun x => (u x : ℂ)) :=
    u.hasCompactSupport.comp_left Complex.ofReal_zero
  have hi := integrable_core_gammaDensity u
  rw [coreSchwartz_coe] at hi ⊢
  have hn (ξ : ℝ) : 0 ≤ gammaIncrementSymbol (2 * Real.pi * ξ) *
      ‖𝓕 (fun x => (u x : ℂ)) ξ‖ ^ 2 :=
    mul_nonneg (gammaIncrementSymbol_nonneg _) (sq_nonneg _)
  have he := lintegral_archSymbol_mul_normSq_fourier
    (hcont.integrable_of_hasCompactSupport hc) (hcont.memLp_of_hasCompactSupport hc)
  change (∫⁻ ξ : ℝ, ENNReal.ofReal (gammaIncrementSymbol (2 * Real.pi * ξ) *
      ‖𝓕 (fun x => (u x : ℂ)) ξ‖ ^ 2)) = _ at he
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn), lintegral_levy_eq] at he
  have hr := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_ofReal (integral_nonneg hn),
    ← integral_eq_lintegral_of_nonneg_ae (levyIntegrand_nonneg u)
      (aestronglyMeasurable_levyIntegrand u.continuous)] at hr
  exact hr

theorem integral_core_spectralDensity {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    (∫ ξ : ℝ, ‖𝓕 (suzukiRestrictedWeilCoreSchwartz u : ℝ → ℂ) ξ‖ ^ 2) =
      ∫ x : ℝ, u x ^ 2 := by
  rw [coreSchwartz_coe]
  have hcont : Continuous (fun x => (u x : ℂ)) := Complex.continuous_ofReal.comp u.continuous
  have hc : HasCompactSupport (fun x => (u x : ℂ)) :=
    u.hasCompactSupport.comp_left Complex.ofReal_zero
  rw [GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq
    (hcont.integrable_of_hasCompactSupport hc) (hcont.memLp_of_hasCompactSupport hc)]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem norm_integral_coreSchwartz_sq {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    ‖∫ x : ℝ, suzukiRestrictedWeilCoreSchwartz u x‖ ^ 2 = (∫ x : ℝ, u x) ^ 2 := by
  have hi := u.continuous.integrable_of_hasCompactSupport u.hasCompactSupport
  have he : (∫ x : ℝ, (u x : ℂ)) = ((∫ x : ℝ, u x) : ℂ) := by
    rw [← Complex.ofRealCLM_apply,
      ← ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM hi]
    rfl
  rw [show (fun x => suzukiRestrictedWeilCoreSchwartz u x) = (fun x => (u x : ℂ))
    from coreSchwartz_coe u, he, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem regularSquareDensity_zero_eq (u : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    regularSquareDampedSpectralDensity u 0 ξ =
      squarePrimeRegularSymbol (2 * Real.pi * ξ) * ‖𝓕 (u : ℝ → ℂ) ξ‖ ^ 2 := by
  unfold regularSquareDampedSpectralDensity squarePrimeRegularSymbol
  congr 3
  push_cast
  ring

/-- The exact regular Fourier pairing and the ordinary mean reconstruct the literal even source. -/
theorem squarePrimeSource_eq_regular_add_real_mean {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    squarePrimeSource u =
      (∫ ξ : ℝ, regularSquareDampedSpectralDensity (suzukiRestrictedWeilCoreSchwartz u) 0 ξ) +
        (1 / 2 : ℝ) * (∫ x : ℝ, u x) ^ 2 := by
  rw [squarePrimeSource_eq_regular_add_mean, norm_integral_coreSchwartz_sq]

/-- The literal square-prime source leaves the Euler-constant mass gap after its mean pole is restored. -/
theorem squarePrimeSource_gamma_gap_core {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    Real.eulerMascheroniConstant * (∫ x : ℝ, u x ^ 2) ≤
      levyEnergy u - squarePrimeSource u + (1 / 2 : ℝ) * (∫ x : ℝ, u x) ^ 2 := by
  let U := suzukiRestrictedWeilCoreSchwartz u
  have hG := integrable_core_gammaDensity u
  have hR := integrable_regularSquareDampedSpectralDensity U (le_refl 0)
  have hp (ξ : ℝ) : Real.eulerMascheroniConstant * ‖𝓕 (U : ℝ → ℂ) ξ‖ ^ 2 ≤
      gammaIncrementSymbol (2 * Real.pi * ξ) * ‖𝓕 (U : ℝ → ℂ) ξ‖ ^ 2 -
        regularSquareDampedSpectralDensity U 0 ξ := by
    rw [regularSquareDensity_zero_eq, ← sub_mul]
    exact mul_le_mul_of_nonneg_right
      (eulerConstant_le_gammaIncrement_sub_squarePrimeRegular _) (sq_nonneg _)
  have hi := integral_mono ((integrable_spectralDensity U).const_mul _)
    (hG.sub hR) hp
  rw [integral_const_mul, integral_sub hG hR] at hi
  change Real.eulerMascheroniConstant * (∫ ξ, ‖𝓕 (suzukiRestrictedWeilCoreSchwartz u : ℝ → ℂ) ξ‖ ^ 2) ≤ _ at hi
  rw [integral_core_spectralDensity, integral_core_gammaDensity] at hi
  have hs := squarePrimeSource_eq_regular_add_real_mean u
  dsimp only [U] at hi
  linarith only [hi, hs]

/-- One uniform Gamma share and half the Euler-constant mass gap survive on every real compact smooth core. -/
theorem exists_squarePrime_retained_gamma_core :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a : ℝ) (u : SuzukiRestrictedWeilCore a),
      δ * levyEnergy u + (Real.eulerMascheroniConstant / 2) * (∫ x : ℝ, u x ^ 2) ≤
        levyEnergy u - squarePrimeSource u + (1 / 2 : ℝ) * (∫ x : ℝ, u x) ^ 2 := by
  obtain ⟨δ, hδ, hsymbol⟩ := exists_squarePrime_regular_retained_gamma
  refine ⟨δ, hδ, ?_⟩
  intro a u
  let U := suzukiRestrictedWeilCoreSchwartz u
  have hG := integrable_core_gammaDensity u
  have hρ := integrable_spectralDensity U
  have hR := integrable_regularSquareDampedSpectralDensity U (le_refl 0)
  have hp (ξ : ℝ) : δ * (gammaIncrementSymbol (2 * Real.pi * ξ) * ‖𝓕 (U : ℝ → ℂ) ξ‖ ^ 2) +
      (Real.eulerMascheroniConstant / 2) * ‖𝓕 (U : ℝ → ℂ) ξ‖ ^ 2 ≤
      gammaIncrementSymbol (2 * Real.pi * ξ) * ‖𝓕 (U : ℝ → ℂ) ξ‖ ^ 2 -
        regularSquareDampedSpectralDensity U 0 ξ := by
    rw [regularSquareDensity_zero_eq]
    have h := mul_le_mul_of_nonneg_right (hsymbol (2 * Real.pi * ξ))
      (sq_nonneg ‖𝓕 (U : ℝ → ℂ) ξ‖)
    nlinarith only [h]
  have hi := integral_mono ((hG.const_mul δ).add (hρ.const_mul _)) (hG.sub hR) hp
  rw [integral_add (hG.const_mul δ) (hρ.const_mul _), integral_const_mul,
    integral_const_mul, integral_sub hG hR] at hi
  change δ * (∫ ξ, gammaIncrementSymbol (2 * Real.pi * ξ) *
      ‖𝓕 (suzukiRestrictedWeilCoreSchwartz u : ℝ → ℂ) ξ‖ ^ 2) + _ ≤ _ at hi
  dsimp only [U] at hi
  rw [integral_core_gammaDensity, integral_core_spectralDensity] at hi
  have hs := squarePrimeSource_eq_regular_add_real_mean u
  linarith only [hi, hs]

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.squarePrimeSource_eq_regular_add_real_mean
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.squarePrimeSource_gamma_gap_core
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_squarePrime_retained_gamma_core
