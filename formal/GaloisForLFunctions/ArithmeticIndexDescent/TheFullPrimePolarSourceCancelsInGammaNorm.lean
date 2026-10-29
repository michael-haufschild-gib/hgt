import GaloisForLFunctions.ArithmeticIndexDescent.ThePrimePolarCutoffIsSmallInGammaNorm
import GaloisForLFunctions.ArithmeticIndexDescent.ThePrimePolarCutoffRepresentsTheFullSource

/-!
# Uniform prime–polar cancellation on compact BV sources

The literal full prime sum minus both exponential pole moments is lower order
than the natural half-exponential aperture mass in Gamma plus square mass.
The estimate is uniform over the original profiles. Pole-preserving smoothing
transfers it to compact BV functions without introducing a derivative norm.
-/

noncomputable section
open MeasureTheory Set Filter Topology FourierTransform SchwartzMap
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent
open GaloisForLFunctions.RHTower ArithmeticCompensationTheory
open ArithmeticCastelnuovoSeveri.LogCells SpacingScaleHarmonicAnalysis

/-- The multiplier bound pays the original smooth source in Gamma energy and square mass. -/
theorem eventually_primePolar_gamma_bound_core {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ S : ℝ in atTop, ∀ (a : ℝ) (u : SuzukiRestrictedWeilCore a),
      2 * u.supportRadius + 1 ≤ S →
      |primeSum u - (2 * coshHalfMoment u ^ 2 - 2 * sinhHalfMoment u ^ 2)| ≤
        ε * Real.exp (S / 2) * (levyEnergy u + ∫ x, u x ^ 2) := by
  filter_upwards [eventually_primePolarCutoffSymbol_gamma_small hε] with S hsymbol
  intro a u hsupp
  have hi := integrable_primePolarCutoffSymbol_density (suzukiRestrictedWeilCoreSchwartz u)
    hsymbol.1
  have hG := integrable_core_gammaDensity u
  have hM := _root_.RHTower.integrable_spectralDensity (suzukiRestrictedWeilCoreSchwartz u)
  have hright := (hG.add hM).const_mul (ε * Real.exp (S / 2))
  have hpoint (ξ : ℝ) :
      |primePolarCutoffSymbol S (2 * Real.pi * ξ) *
        ‖𝓕 (suzukiRestrictedWeilCoreSchwartz u : ℝ → ℂ) ξ‖ ^ 2| ≤
      (ε * Real.exp (S / 2)) *
        (gammaIncrementSymbol (2 * Real.pi * ξ) *
          ‖𝓕 (suzukiRestrictedWeilCoreSchwartz u : ℝ → ℂ) ξ‖ ^ 2 +
            ‖𝓕 (suzukiRestrictedWeilCoreSchwartz u : ℝ → ℂ) ξ‖ ^ 2) := by
    rw [abs_mul, abs_of_nonneg
      (sq_nonneg ‖𝓕 (suzukiRestrictedWeilCoreSchwartz u : ℝ → ℂ) ξ‖)]
    calc _ ≤ (ε * Real.exp (S / 2) * (1 + gammaIncrementSymbol (2 * Real.pi * ξ))) *
        ‖𝓕 (suzukiRestrictedWeilCoreSchwartz u : ℝ → ℂ) ξ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hsymbol.2 _) (sq_nonneg _)
      _ = _ := by ring
  rw [primeSum_sub_poles_eq_primePolarCutoff_integral u hsupp]
  have hb := (abs_integral_le_integral_abs (f := fun ξ =>
    primePolarCutoffSymbol S (2 * Real.pi * ξ) *
      ‖𝓕 (suzukiRestrictedWeilCoreSchwartz u : ℝ → ℂ) ξ‖ ^ 2)).trans
        (integral_mono hi.abs hright hpoint)
  simp only [Pi.add_apply] at hb
  rw [integral_const_mul, integral_add hG hM,
    integral_core_gammaDensity, integral_core_spectralDensity] at hb
  exact hb

/-- Actual prime–polar cancellation holds uniformly on every Gamma-plus-mass unit ball
of compact BV profiles, with every prime power and both signed pole moments retained. -/
theorem exists_primePolar_gamma_bound_bv {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ f : ℝ → ℝ,
      BoundedVariationOn f univ → SupportedIn R f →
      |primeSum f - (2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2)| ≤
        ε * Real.exp R * (levyEnergy f + ∫ x, f x ^ 2) := by
  obtain ⟨S₀, hS₀⟩ := eventually_atTop.mp
    (eventually_primePolar_gamma_bound_core
      (show 0 < ε / Real.exp 1 by positivity))
  refine ⟨max 0 S₀, le_max_left _ _, ?_⟩
  intro R hR f hv hsupp
  have hR0 : 0 ≤ R := (le_max_left _ _).trans hR
  have hSR : S₀ ≤ R := (le_max_right _ _).trans hR
  have hc : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact (K := Icc (-R) R) isCompact_Icc
    intro x hx
    apply abs_le.mp
    by_contra hh
    exact hx (hsupp x (lt_of_not_ge hh))
  have hf := memLp_compact_bv hv hc
  have hscale : (ε / Real.exp 1) * Real.exp ((2 * R + 2) / 2) = ε * Real.exp R := by
    rw [show (2 * R + 2) / 2 = R + 1 by ring, Real.exp_add]
    field_simp
  have hn (n : ℕ) :
      |primeSum (poleSmooth f n) - (2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2)| ≤
        ε * Real.exp R * (levyEnergy (poleSmooth f n) + ∫ x, poleSmooth f n x ^ 2) := by
    have h := hS₀ (2 * R + 2) (by linarith only [hSR, hR0]) (R + 1)
      (squarePrimeSmoothCore hf hR0 hsupp n) (by
        change 2 * (R + 1 / 2) + 1 ≤ 2 * R + 2
        linarith)
    change |primeSum (poleSmooth f n) -
      (2 * coshHalfMoment (poleSmooth f n) ^ 2 - 2 * sinhHalfMoment (poleSmooth f n) ^ 2)| ≤
        (ε / Real.exp 1) * Real.exp ((2 * R + 2) / 2) *
          (levyEnergy (poleSmooth f n) + ∫ x, poleSmooth f n x ^ 2) at h
    rw [hscale, (poleSmooth_halfMoments hv hc n).1, (poleSmooth_halfMoments hv hc n).2] at h
    exact h
  have hl := ((tendsto_poleSmooth_primeSum hf hsupp).sub
    (tendsto_const_nhds (x := 2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2))).abs
  have hr := ((tendsto_poleSmooth_levyEnergy hv hc).add
    (tendsto_poleSmooth_square_mass hf)).const_mul (ε * Real.exp R)
  exact le_of_tendsto_of_tendsto' hl hr hn

end GaloisForLFunctions.ArithmeticIndexDescent
