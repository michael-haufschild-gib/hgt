import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePVerticalConnectionCocycle

/-!
# Irreducibility of the Route-P terminal coordinate

The exact vertical cocycle is not a scalar reparametrization of the strict-cross
history.  At the literal zero atom `6`, strict-cross history is stationary,
while the canonical terminal connection has a strictly positive increment.
Consequently no function of the scalar strict-cross current—linear or
nonlinear—can recover the terminal connection at every cutoff.

This is a positive architectural constraint: a valid cofinal P graph must
retain a separate vertical terminal coordinate.  It does not construct its
unbounded completion or establish its required joint graph estimate.
-/

namespace RHTower

noncomputable section

/-- **Terminal irreducibility.** No scalar function of the complete
strict-cross current recovers the canonical terminal connection at all
cutoffs.  The zero atom `6` gives the explicit separating witness. -/
theorem not_exists_speQuantileRieszTerminalConnection_eq_function_of_strictCross :
    ¬ ∃ F : ℝ → ℝ, ∀ K : ℕ,
      speQuantileRieszCanonicalTerminalConnection K =
        F (ccmParabolicPairing
          (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
          (ccmActualHeadMatchedQuantileParabolicSourceBoundary K)) := by
  rintro ⟨F, hF⟩
  have hsource :
      ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal 4)
          (ccmActualHeadMatchedQuantileParabolicSourceBoundary 4) =
        ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal 3)
          (ccmActualHeadMatchedQuantileParabolicSourceBoundary 3) := by
    simpa using
      (ccmActualHeadMatchedQuantileParabolicStrictCross_succ_eq_of_not_isPrimePow 3
        speQuantileRieszSix_not_isPrimePow)
  have hterminal : 0 <
      speQuantileRieszCanonicalTerminalConnection 4 -
        speQuantileRieszCanonicalTerminalConnection 3 := by
    have hbound := speQuantileRieszCanonicalTerminalConnection_succ_sub_lower_of_not_isPrimePow
      3 speQuantileRieszSix_not_isPrimePow (by norm_num : 1 ≤ 3)
    have hpos : 0 < (2 / 9 : ℝ) * (3 + 3) := by positivity
    exact lt_of_lt_of_le hpos hbound
  have hterminal_eq : speQuantileRieszCanonicalTerminalConnection 4 =
      speQuantileRieszCanonicalTerminalConnection 3 := by
    calc
      speQuantileRieszCanonicalTerminalConnection 4 = F
          (ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal 4)
            (ccmActualHeadMatchedQuantileParabolicSourceBoundary 4)) := hF 4
      _ = F (ccmParabolicPairing
          (ccmActualHeadMatchedQuantileParabolicCodiagonal 3)
          (ccmActualHeadMatchedQuantileParabolicSourceBoundary 3)) := by rw [hsource]
      _ = speQuantileRieszCanonicalTerminalConnection 3 := (hF 3).symm
  linarith

end

end RHTower
