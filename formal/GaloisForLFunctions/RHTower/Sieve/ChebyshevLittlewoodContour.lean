import GaloisForLFunctions.RHTower.Sieve.ChebyshevLittlewoodData
import GaloisForLFunctions.RHTower.Sieve.ChebyshevExplicitBound
import GaloisForLFunctions.RHTower.Sieve.MellinDecayUniform

/-!
# The Chebyshev contour bound at a rectangle of arbitrary exponent-one width

The five-term estimate instantiated at the Littlewood data.  The left abscissa is
`1 - A/log T` for an arbitrary `A > 0`, so the left edge carries the saving
`exp(-A·log(N+H)/log T)` where the exponent-one contour is limited to `A = 1/40000`; and every edge
bound is `Cr·log²T/log log T` rather than `Cr·log²T`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- **The Chebyshev contour bound at the rectangle of width `A/log T`.** -/
theorem exists_norm_tsum_vonMangoldt_littlewood_general (A : ℝ) (hA : 0 < A) :
    ∃ Cm Cr L₀ : ℝ, 0 ≤ Cm ∧ 0 < Cr ∧ max 8 (2 * A) ≤ L₀ ∧
      ∀ N H : ℝ, 0 < N → 0 < H → ∀ T : ℝ, 1 ≤ T → L₀ ≤ Real.log T →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
            ((vonMangoldt n : ℝ) : ℂ) * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))
          - mellin (fun x : ℝ => ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) 1
              * (((2 * Real.arctan (T / (chebRightTwo T - 1))
                    - 2 * Real.arctan (T / (chebLeftLw A T - 1)) : ℝ)) : ℂ)‖
        ≤ 2 * ((∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-(chebRightTwo T)))
              * (Cm / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ chebRightTwo T)) / T
          + ((1 - chebLeftLw A T)⁻¹
              * (2 * ((N + H) ^ chebLeftLw A T / chebLeftLw A T)
                + 2 * (Cm / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ chebLeftLw A T))
            + 2 * ((chebRightTwo T - chebLeftLw A T)
                * (((Cm / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ chebRightTwo T) / T ^ (1 + 1)
                    + ‖mellin (fun x : ℝ => ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) 1‖) / T)))
          + (Cr * Real.log T ^ 2 / Real.log (Real.log T)
              * (2 * ((N + H) ^ chebLeftLw A T / chebLeftLw A T)
                + 2 * (Cm / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ chebLeftLw A T))
            + 2 * ((chebRightTwo T - chebLeftLw A T)
                * (Cr * Real.log T ^ 2 / Real.log (Real.log T)
                    * ((Cm / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ chebRightTwo T)
                        / T ^ (1 + 1))))) := by
  obtain ⟨Cm, hCm, hdec⟩ := exists_bound_mellin_smoothWeight_uniform_upto 1
  obtain ⟨Cr, L₀, hCr0, hL₀8, hdata⟩ := exists_cheb_littlewood_data A hA
  refine ⟨Cm, Cr, L₀, hCm, hCr0, hL₀8, fun N H hN hH T hT1 hT => ?_⟩
  obtain ⟨hzfrect, hzfline, hregline, hregtop, hregbot⟩ := hdata T hT1 hT
  have hT8 : (8 : ℝ) ≤ Real.log T := le_trans (le_trans (le_max_left _ _) hL₀8) hT
  have hTA : 2 * A ≤ Real.log T := le_trans (le_trans (le_max_right _ _) hL₀8) hT
  have hLL0 : (0 : ℝ) < Real.log (Real.log T) := by
    refine Real.log_pos ?_
    linarith
  have hR0 : (0 : ℝ) ≤ Cr * Real.log T ^ 2 / Real.log (Real.log T) := by positivity
  exact norm_tsum_vonMangoldt_sub_full_main_le_explicit hN hH
    (zero_lt_chebLeftLw hT8 hTA) (chebLeftLw_lt_one hA hT8) (one_lt_chebRightTwo hT8) hT1
    hR0 hR0 hzfrect hzfline hregline hregtop hregbot
    (fun s hs hsc => hdec N H hN hH (chebLeftLw A T) s hs hsc)
    (fun s hs hsd => hdec N H hN hH (chebRightTwo T) s hs hsd)


end RHTower.Sieve
