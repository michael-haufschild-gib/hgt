import GaloisForLFunctions.HTGeometry.GammaShiftLadder
import GaloisForLFunctions.RHTower.LagExplicitFormula

/-!
# Summable archimedean tail for vertical HCF differences

The HCF cross-height source must take a vertical difference before it is
continued to the divisor.  `logDeriv Γℝ` itself grows like `log |t|`; this
module proves that the height-two difference has the summable `O(1/|t|)`
tail.  Height two is forced by the `s / 2` argument of `Γℝ`.

This resolves only the archimedean tail obligation.  It supplies neither the
required finite quadratic source trace nor its continuation estimate.
-/

open Complex

namespace RHTower

noncomputable section

/-- A height-two difference cancels the logarithmic archimedean growth. -/
theorem exists_norm_logDeriv_GammaR_vertical_two_shift_le :
    ∃ K R : ℝ, 0 ≤ K ∧ 2 ≤ R ∧ ∀ s : ℂ, 0 < s.re → R ≤ ‖s‖ →
      ‖logDeriv Gammaℝ (s + 2 * I) - logDeriv Gammaℝ s‖ ≤ K / ‖s‖ := by
  obtain ⟨K, R, hK, hR, htail⟩ :=
    GaloisForLFunctions.HTGeometry.exists_norm_digamma_vertical_unit_shift_le
  refine ⟨K, 2 * R, hK, ?_, ?_⟩
  · linarith
  · intro s hs hsize
    have hsHalf : 0 < (s / 2).re := by
      rw [Complex.div_re]
      norm_num
      linarith
    have hsizeHalf : R ≤ ‖s / 2‖ := by
      rw [Complex.norm_div]
      norm_num
      linarith
    have htail' := htail (s / 2) hsHalf hsizeHalf
    have hshift : (s + 2 * I) / 2 = s / 2 + I := by ring
    rw [logDeriv_Gammaℝ_digamma (by simpa using hs),
      logDeriv_Gammaℝ_digamma hs, hshift]
    have hrewrite :
        (Complex.digamma (s / 2 + I) / 2 - (Real.log Real.pi : ℂ) / 2) -
            (Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2) =
          (Complex.digamma (s / 2 + I) - Complex.digamma (s / 2)) / 2 := by
      ring
    rw [hrewrite, Complex.norm_div]
    norm_num
    rw [show ‖s / 2‖ = ‖s‖ / 2 by rw [Complex.norm_div]; norm_num] at htail'
    have hnorm : 0 < ‖s‖ := by
      have : 0 < 2 * R := by nlinarith
      exact this.trans_le hsize
    calc
      ‖(s / 2 + I).digamma - (s / 2).digamma‖ / 2 ≤
          (K / (‖s‖ / 2)) / 2 :=
        div_le_div_of_nonneg_right htail' (by norm_num)
      _ = K / ‖s‖ := by
        field_simp

end

end RHTower
