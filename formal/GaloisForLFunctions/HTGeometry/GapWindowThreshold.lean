import GaloisForLFunctions.HTGeometry.BalancedCoefficient

/-!
# The separation window opens past a threshold

For a divergent-ratio integer exponent sequence, past a threshold the gap between consecutive
terms exceeds any fixed bound and the next term dominates a fixed multiple of the current one
(`exists_threshold_gap_window`): `Omax < bnat M − bnat (M-1)` and `r·bnat M + Omax < bnat (M+1)`.
These are exactly the window hypotheses of the source-sum vanishing lemmas — so at a top-degree
balanced index every off-class differential monomial has vanishing coefficient once `M` is large.
-/

open Filter Finset

namespace GaloisForLFunctions

/-- **Separation window threshold.**  Past a threshold the consecutive gap exceeds `Omax` and the
successor dominates `r·bnat M + Omax`. -/
theorem exists_threshold_gap_window {bnat : ℕ → ℕ}
    (hpos : ∀ᶠ n in atTop, 0 < bnat n)
    (hratio : Tendsto (fun n => (bnat (n + 1) : ℝ) / (bnat n : ℝ)) atTop atTop) (r Omax : ℕ) :
    ∃ Nw : ℕ, ∀ M, Nw ≤ M →
      Omax < bnat M - bnat (M - 1) ∧ r * bnat M + Omax < bnat (M + 1) := by
  obtain ⟨N2, _, hjump, hmono, hstair⟩ := exists_gap_threshold hpos hratio (r + 1)
  refine ⟨N2 + Omax + 2, fun M hM => ?_⟩
  have hM1N2 : N2 ≤ M - 1 := by omega
  have hMN2 : N2 ≤ M := by omega
  have hbM1_ge : Omax + 1 ≤ bnat (M - 1) := by
    have hs := hstair (M - 1 - N2)
    rw [show N2 + (M - 1 - N2) = M - 1 by omega] at hs
    omega
  have hjM : (r + 1 + 2) * bnat (M - 1) ≤ bnat M := by
    have := hjump (M - 1) hM1N2
    rwa [show M - 1 + 1 = M by omega] at this
  have hjM1 : (r + 1 + 2) * bnat M ≤ bnat (M + 1) := hjump M hMN2
  have hbM_ge : Omax + 1 ≤ bnat M :=
    le_trans hbM1_ge (hmono (M - 1) hM1N2 M (by omega))
  refine ⟨?_, ?_⟩
  · have h2 : bnat (M - 1) + Omax < bnat M := by nlinarith [hjM, hbM1_ge]
    omega
  · nlinarith [hjM1, hbM_ge]

end GaloisForLFunctions
