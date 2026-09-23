import GaloisForLFunctions.RHTower.Sieve.ChebyshevKappaOneData
import GaloisForLFunctions.RHTower.Sieve.ChebyshevExplicitBound
import GaloisForLFunctions.RHTower.Sieve.MellinDecayUniform

/-!
# The Chebyshev contour bound at the width-`1/log` rectangle

Substituting the width-`1/log` contour data into the five-term estimate gives a bound in which the
cutoff enters only through the trivial sizes `(N+H)^{c(T)}` and `(N+H+1)^{d(T)}` and the explicit
price `H^{-2}(N+H+1)^(2 : ℕ)` of the smoothing, and the height enters only through `T` and `log²T`.

Every edge bound is the same `C log²T`, so the left edge is of size `(N+H)^{c(T)}` throughout and
retains the saving `exp(-log(N+H)/(40000 log T))`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- **The Chebyshev contour bound at the width-`1/log` rectangle.** -/
theorem exists_norm_tsum_vonMangoldt_kappa_one_general :
    ∃ Cm Cr L₀ : ℝ, 0 ≤ Cm ∧ 0 < Cr ∧ 8 ≤ L₀ ∧
      ∀ N H : ℝ, 0 < N → 0 < H → ∀ T : ℝ, 1 ≤ T → L₀ ≤ Real.log T →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
            ((vonMangoldt n : ℝ) : ℂ) * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))
          - mellin (fun x : ℝ => ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) 1
              * (((2 * Real.arctan (T / (chebRightTwo T - 1))
                    - 2 * Real.arctan (T / (chebLeftTwo T - 1)) : ℝ)) : ℂ)‖
        ≤ 2 * ((∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-(chebRightTwo T)))
              * (Cm / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ chebRightTwo T)) / T
          + ((1 - chebLeftTwo T)⁻¹
              * (2 * ((N + H) ^ chebLeftTwo T / chebLeftTwo T)
                + 2 * (Cm / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ chebLeftTwo T))
            + 2 * ((chebRightTwo T - chebLeftTwo T)
                * (((Cm / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ chebRightTwo T) / T ^ (1 + 1)
                    + ‖mellin (fun x : ℝ => ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) 1‖) / T)))
          + (Cr * Real.log T ^ 2
              * (2 * ((N + H) ^ chebLeftTwo T / chebLeftTwo T)
                + 2 * (Cm / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ chebLeftTwo T))
            + 2 * ((chebRightTwo T - chebLeftTwo T)
                * (Cr * Real.log T ^ 2
                    * ((Cm / H ^ 2 * (N + H + 1) ^ 2 * (N + H + 1) ^ chebRightTwo T)
                        / T ^ (1 + 1))))) := by
  obtain ⟨Cm, hCm, hdec⟩ := exists_bound_mellin_smoothWeight_uniform_upto 1
  obtain ⟨Cr, L₀, hCr0, hL₀8, hdata⟩ := exists_cheb_kappa_one_data
  refine ⟨Cm, Cr, L₀, hCm, hCr0, hL₀8, fun N H hN hH T hT1 hT => ?_⟩
  obtain ⟨hzfrect, hzfline, hregline, hregtop, hregbot⟩ := hdata T hT1 hT
  have hT8 : (8 : ℝ) ≤ Real.log T := le_trans hL₀8 hT
  have hR0 : (0 : ℝ) ≤ Cr * Real.log T ^ 2 := by positivity
  exact norm_tsum_vonMangoldt_sub_full_main_le_explicit hN hH
    (zero_lt_chebLeftTwo hT8) (chebLeftTwo_lt_one hT8) (one_lt_chebRightTwo hT8) hT1
    hR0 hR0 hzfrect hzfline hregline hregtop hregbot
    (fun s hs hsc => hdec N H hN hH (chebLeftTwo T) s hs hsc)
    (fun s hs hsd => hdec N H hN hH (chebRightTwo T) s hs hsd)

end RHTower.Sieve
