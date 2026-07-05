/-
The center-uniform four-phase small-ball law in iterated-integral form:
the four-fold angle integral of the sublevel indicator at any center is
bounded by the explicit four-phase constant.  This is the shape the
Steinhaus block marginal consumes after peeling and rescaling four prime
phases.
-/
import Mathlib
import GaloisForLFunctions.RHTower.RouteBProdFubini
import GaloisForLFunctions.RHTower.RouteBFourPhaseUniform

namespace RHTower
namespace Sublevel

open MeasureTheory

/-- The four-fold iterated angle integral of the sublevel indicator, at
any center `w`, is at most the explicit four-phase constant. -/
theorem four_phase_nested_uniform {A B C D w : ℂ} {r σ0 sstar : ℝ}
    {J : ℕ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hρB : ‖B‖ < ‖A‖) (hr0 : 0 < r) (hr2 : 2 * r ≤ ‖A‖ - ‖B‖)
    (hσ0 : 0 < σ0)
    (hσ0G : σ0 ≤ ((‖A‖ + ‖B‖) ^ 2 - (‖A‖ - ‖B‖) ^ 2) / 3)
    (hJ : ((‖A‖ + ‖B‖) ^ 2 - (‖A‖ - ‖B‖) ^ 2) / 3 < 2 ^ J * σ0)
    (hHσ0 : 2 * (r * (2 * ‖A‖ + r) / ((‖A‖ - ‖B‖) * ‖B‖))
        ≤ σ0 * causticKappa ‖A‖ ‖B‖)
    (hss : 0 < sstar) (hss2 : 2 * sstar ≤ ‖D‖) :
    ∫⁻ θD in Set.Icc (0 : ℝ) (2 * Real.pi),
        ∫⁻ θC in Set.Icc (0 : ℝ) (2 * Real.pi),
          ∫⁻ θB in Set.Icc (0 : ℝ) (2 * Real.pi),
            ∫⁻ θA in Set.Icc (0 : ℝ) (2 * Real.pi),
              {θ' : ℝ | ‖w + D * Complex.exp ((θD : ℂ) * Complex.I)
                  + C * Complex.exp ((θC : ℂ) * Complex.I)
                  + B * Complex.exp ((θB : ℂ) * Complex.I)
                  + A * Complex.exp ((θ' : ℂ) * Complex.I)‖ ≤ r}.indicator
                (fun _ => (1 : ENNReal)) θA
      ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3)
          * ENNReal.ofReal (8 * Real.pi * sstar / ‖D‖)
        + ENNReal.ofReal (2 * (Real.pi * r / ‖A‖)
            * ((J : ℝ) * (8 * Real.pi ^ 2
              * (r * (2 * ‖A‖ + r) / ((‖A‖ - ‖B‖) / 2 * ‖B‖))
              * Real.sqrt (2 / (causticKappa ‖A‖ ‖B‖ * ‖C‖)))
            + 2 * ((2 * Real.pi * Real.sqrt (2 * (r * (2 * ‖A‖ + r)
                / ((‖A‖ - ‖B‖) / 2 * ‖B‖))))
              * (2 * Real.pi * Real.sqrt ((σ0 + r * (2 * (‖A‖ + ‖B‖) + r))
                / ‖C‖))))
            / Real.sqrt sstar)
          * ENNReal.ofReal (2 * Real.pi)
        + ENNReal.ofReal (2 * (Real.pi * r / ‖A‖)
            * ((J : ℝ) * (8 * Real.pi ^ 2
              * (r * (2 * ‖A‖ + r) / ((‖A‖ - ‖B‖) / 2 * ‖B‖))
              * Real.sqrt 2)
            + 2 * Real.pi * (2 * Real.pi
              * (r * (2 * ‖A‖ + r) / ((‖A‖ - ‖B‖) / 2 * ‖B‖))
              / Real.sqrt (min (((‖A‖ + ‖B‖) ^ 2 - (‖A‖ - ‖B‖) ^ 2) / 3
                  * causticKappa ‖A‖ ‖B‖ / 2) (1 / 2)))))
          * ENNReal.ofReal (2 * Real.pi) := by
  exact le_trans (le_of_eq (four_phase_prod_eq_nested A B C D w r).symm)
    (four_phase_sublevel_uniform hA hB hC hD hρB hr0 hr2 hσ0 hσ0G hJ hHσ0
      hss hss2)

end Sublevel
end RHTower
