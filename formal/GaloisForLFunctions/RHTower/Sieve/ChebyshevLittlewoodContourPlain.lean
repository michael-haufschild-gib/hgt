import GaloisForLFunctions.RHTower.Sieve.ChebyshevLittlewoodContour

/-!
# The contour bound at width `A/log T` with the plain edge bound

The same five-term estimate as `exists_norm_tsum_vonMangoldt_littlewood_general`, with the edge
bound `Cr·log²T` in place of `Cr·log²T/log log T`.  Dropping the `log log` keeps the assembly's
shape identical to the exponent-one chain's, so the depth `A` is the only thing that changes; the
`log log` gain is retained separately in `exists_bound_zetaLogDerivReg_uniform_littlewood`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- **The contour bound at width `A/log T`, with the plain `log²T` edge bound.** -/
theorem exists_norm_tsum_vonMangoldt_littlewood_plain (A : ℝ) (hA : 0 < A) :
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
          + (Cr * Real.log T ^ 2
              * (2 * ((N + H) ^ chebLeftLw A T / chebLeftLw A T)
                + 2 * (Cm / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ chebLeftLw A T))
            + 2 * ((chebRightTwo T - chebLeftLw A T)
                * (Cr * Real.log T ^ 2
                    * ((Cm / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ chebRightTwo T)
                        / T ^ (1 + 1))))) := by
  obtain ⟨Cm, hCm, hdec⟩ := exists_bound_mellin_smoothWeight_uniform_upto 1
  obtain ⟨Cr, L₀, hCr0, hL₀8, hdata⟩ := exists_cheb_littlewood_data_plain A hA
  refine ⟨Cm, Cr, L₀, hCm, hCr0, hL₀8, fun N H hN hH T hT1 hT => ?_⟩
  obtain ⟨hzfrect, hzfline, hregline, hregtop, hregbot⟩ := hdata T hT1 hT
  have hT8 : (8 : ℝ) ≤ Real.log T := le_trans (le_trans (le_max_left _ _) hL₀8) hT
  have hTA : 2 * A ≤ Real.log T := le_trans (le_trans (le_max_right _ _) hL₀8) hT
  have hR0 : (0 : ℝ) ≤ Cr * Real.log T ^ 2 := by positivity
  exact norm_tsum_vonMangoldt_sub_full_main_le_explicit hN hH
    (zero_lt_chebLeftLw hT8 hTA) (chebLeftLw_lt_one hA hT8) (one_lt_chebRightTwo hT8) hT1
    hR0 hR0 hzfrect hzfline hregline hregtop hregbot
    (fun s hs hsc => hdec N H hN hH (chebLeftLw A T) s hs hsc)
    (fun s hs hsd => hdec N H hN hH (chebRightTwo T) s hs hsd)



end RHTower.Sieve
