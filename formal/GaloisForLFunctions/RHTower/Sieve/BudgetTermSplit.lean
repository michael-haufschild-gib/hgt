import GaloisForLFunctions.RHTower.Sieve.OmegaBudgetLadderTail

/-!
# Splitting the normalised budget

The Route E gate divides the budget by `W²h²√x`.  The resulting quotient splits into four groups:
the Gallagher head, the two tail groups, and the non-spectral part.
-/

namespace RHTower.Sieve

noncomputable section

/-- **The normalised budget, split.** -/
theorem budget_div_eq {sx h W G T0 δ αL βL Ec B0 ns : ℝ}
    (hsx : 0 < sx) (hW : 0 < W) (hh : 0 < h) (hG : 0 < G) :
    (16 * sx * (2 * δ ^ 2 * (αL * G + βL)
        + (4 * (αL + 5 * Real.pi / 2 * Ec + 5 * Real.exp 1 / 2 * B0 * Ec / T0)
              / (Real.pi ^ 2 * G)
          + 4 * βL / (3 * Real.pi ^ 2 * G ^ 2))) + ns) / (W ^ 2 * h ^ 2 * sx)
      = 32 * δ ^ 2 * (αL * G + βL) / (W ^ 2 * h ^ 2)
        + 64 * (αL + 5 * Real.pi / 2 * Ec + 5 * Real.exp 1 / 2 * B0 * Ec / T0)
            / (Real.pi ^ 2 * G * (W ^ 2 * h ^ 2))
        + 64 * βL / (3 * Real.pi ^ 2 * G ^ 2 * (W ^ 2 * h ^ 2))
        + ns / (W ^ 2 * h ^ 2 * sx) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  field_simp
  ring

end

end RHTower.Sieve
