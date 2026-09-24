import GaloisForLFunctions.RHTower.ThetaCuspDegreeTwelveFluxShape
import GaloisForLFunctions.RHTower.ThetaCuspCenterCompensationFlux

/-!
# The lawful degree-twelve flux has one-sided tail debt

The source-selected flux is exactly the Schwartz polynomial correction. Its
zero-mass law makes negative derivative unavoidable beyond every cutoff;
strict log-rate descent makes the negative region terminal. This does not
compare that debt with the native odd-four Schur current.
-/

namespace RHTower
noncomputable section
open MeasureTheory Set

/-- The shape flux is the lawful degree-ten polynomial multiple of the center flux. -/
theorem thetaCuspDegreeTwelveFlux_eq_polynomialFlux (a : ℝ) :
    thetaCuspDegreeTwelveFlux a = thetaCuspPolynomialFlux 10 a := by
  funext r
  unfold thetaCuspDegreeTwelveFlux thetaCuspPolynomialFlux
    thetaCuspCenterCompensationFlux
  ring

/-- The degree-twelve correction changes no integrated source moment. -/
theorem integral_deriv_thetaCuspDegreeTwelveFlux {a : ℝ} (ha : |a| < 1) :
    ∫ r : ℝ in Ioi 0, deriv (thetaCuspDegreeTwelveFlux a) r = 0 := by
  rw [thetaCuspDegreeTwelveFlux_eq_polynomialFlux]
  exact integral_deriv_thetaCuspPolynomialFlux 10 ha

/-- Its signed tail integral is exactly the negative boundary flux. -/
theorem integral_Ioi_deriv_thetaCuspDegreeTwelveFlux_eq_neg {a : ℝ}
    (ha : |a| < 1) (R : ℝ) :
    (∫ r : ℝ in Ioi R, deriv (thetaCuspDegreeTwelveFlux a) r) =
      -thetaCuspDegreeTwelveFlux a R := by
  rw [thetaCuspDegreeTwelveFlux_eq_polynomialFlux]
  exact integral_Ioi_deriv_thetaCuspPolynomialFlux_eq_neg 10 ha R

/-- Beyond every positive cutoff, the correction exports negative mass. -/
theorem thetaCuspDegreeTwelveFlux_exists_negative_after {a R : ℝ}
    (ha : 0 < a) (habs : |a| < 1) (hR : 0 < R) :
    ∃ s : ℝ, R < s ∧ deriv (thetaCuspDegreeTwelveFlux a) s < 0 := by
  have hK : 0 < thetaCuspDegreeTwelveFlux a R :=
    thetaCuspDegreeTwelveFlux_pos ha hR
  have htail := integral_Ioi_deriv_thetaCuspDegreeTwelveFlux_eq_neg habs R
  by_contra h
  have hnn (s : ℝ) (hs : R < s) :
      0 ≤ deriv (thetaCuspDegreeTwelveFlux a) s :=
    le_of_not_gt (fun hneg => h ⟨s, hs, hneg⟩)
  have hint : 0 ≤ ∫ s : ℝ in Ioi R,
      deriv (thetaCuspDegreeTwelveFlux a) s := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hnn s hs
  linarith only [hint, htail, hK]

/-- Negative derivative forms a cofinal terminal ray, not alternating tails. -/
theorem thetaCuspDegreeTwelveFlux_eventually_deriv_neg {a : ℝ}
    (ha : 0 < a) (habs : |a| < 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ s : ℝ, R ≤ s →
      deriv (thetaCuspDegreeTwelveFlux a) s < 0 := by
  obtain ⟨R, hR, hder⟩ :=
    thetaCuspDegreeTwelveFlux_exists_negative_after ha habs (show (0 : ℝ) < 1 by norm_num)
  refine ⟨R, lt_trans (by norm_num : (0 : ℝ) < 1) hR, ?_⟩
  intro s hRs
  rcases eq_or_lt_of_le hRs with rfl | hlt
  · exact hder
  · exact thetaCuspDegreeTwelveFlux_deriv_no_recovery ha
      (lt_trans (by norm_num : (0 : ℝ) < 1) hR) hlt hder.le

end
end RHTower
