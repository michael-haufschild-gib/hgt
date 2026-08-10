import GaloisForLFunctions.RHTower.Sieve.ChebyshevLittlewoodContourPlain
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLlData

/-!
# The contour bound at width `c·log log T/log T`

The five-term estimate of the Chebyshev contour, at the rectangle whose left edge sits at
`1 - c·log log T/log T`.  Unlike the fixed-depth version, the constants here do not depend on the
depth: there is one absolute `c`, so the rectangle may be used at every height simultaneously, which
is what allows the height to be optimised against a depth that grows.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- **The contour bound at width `c·log log T/log T`, with the plain `log²T` edge bound.** -/
theorem exists_norm_tsum_vonMangoldt_ll_plain :
    ∃ c Cm Cr L₀ : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ 0 ≤ Cm ∧ 0 < Cr ∧ 8 ≤ L₀ ∧
      ∀ N H : ℝ, 0 < N → 0 < H → ∀ T : ℝ, 1 ≤ T → L₀ ≤ Real.log T →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
            ((vonMangoldt n : ℝ) : ℂ)
              * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))
          - mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) 1
              * (((2 * Real.arctan (T / (chebRightTwo T - 1))
                    - 2 * Real.arctan (T / (chebLeftLl c T - 1)) : ℝ)) : ℂ)‖
        ≤ 2 * ((∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-(chebRightTwo T)))
              * (Cm / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ chebRightTwo T)) / T
          + ((1 - chebLeftLl c T)⁻¹
              * (2 * ((N + H) ^ chebLeftLl c T / chebLeftLl c T)
                + 2 * (Cm / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ chebLeftLl c T))
            + 2 * ((chebRightTwo T - chebLeftLl c T)
                * (((Cm / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ chebRightTwo T) / T ^ (1 + 1)
                    + ‖mellin (fun x : ℝ =>
                        ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) 1‖) / T)))
          + (Cr * Real.log T ^ 2
              * (2 * ((N + H) ^ chebLeftLl c T / chebLeftLl c T)
                + 2 * (Cm / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ chebLeftLl c T))
            + 2 * ((chebRightTwo T - chebLeftLl c T)
                * (Cr * Real.log T ^ 2
                    * ((Cm / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ chebRightTwo T)
                        / T ^ (1 + 1))))) := by
  obtain ⟨Cm, hCm, hdec⟩ := exists_bound_mellin_smoothWeight_uniform_upto 1
  obtain ⟨c, Cr, L₀, hc0, hchalf, hCr0, hL₀8, hdata⟩ := exists_cheb_ll_data_plain
  refine ⟨c, Cm, Cr, L₀, hc0, hchalf, hCm, hCr0, hL₀8, fun N H hN hH T hT1 hT => ?_⟩
  obtain ⟨hzfrect, hzfline, hregline, hregtop, hregbot⟩ := hdata T hT1 hT
  have hT8 : (8 : ℝ) ≤ Real.log T := le_trans hL₀8 hT
  have hR0 : (0 : ℝ) ≤ Cr * Real.log T ^ 2 := by positivity
  exact norm_tsum_vonMangoldt_sub_full_main_le_explicit hN hH
    (zero_lt_chebLeftLl hc0 hchalf hT8) (chebLeftLl_lt_one hc0 hT8) (one_lt_chebRightTwo hT8) hT1
    hR0 hR0 hzfrect hzfline hregline hregtop hregbot
    (fun s hs hsc => hdec N H hN hH (chebLeftLl c T) s hs hsc)
    (fun s hs hsd => hdec N H hN hH (chebRightTwo T) s hs hsd)

end RHTower.Sieve
