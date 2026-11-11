import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailCombLimit

/-!
# Convergence of power comb tails characterizes RH

A convergent sequence is bounded and hence has subpolynomial growth.
Applied to every subcritical power tail, the exact growth criterion places
all zeros on the critical line. Conversely RH supplies cancellation for
the arithmetic Mellin integrals and hence convergence of every such tail.
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- Convergence of the actual normalized finite power comb. -/
def PowerCombTailConverges (a : ℝ) : Prop :=
  ∃ L : ℝ, Tendsto (powerCombTail a) atTop (𝓝 L)

private theorem strictGrowth_zero_of_tendsto {u : ℕ → ℝ} {L : ℝ}
    (hu : Tendsto u atTop (𝓝 L)) : HTGeometry.StrictNaturalPowerGrowth u 0 := by
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp hu) 1 one_pos
  let C := |L| + 1 + ∑ n ∈ range M, |u n|
  have hs : 0 ≤ ∑ n ∈ range M, |u n| := sum_nonneg fun n _ => abs_nonneg _
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hbound (N : ℕ) : |u N| ≤ C := by
    by_cases hMN : M ≤ N
    · have hh := hM N hMN
      rw [Real.dist_eq] at hh
      have ht : |u N| ≤ |u N - L| + |L| := by
        simpa only [sub_add_cancel] using abs_add_le (u N - L) L
      dsimp only [C]
      linarith only [hh, ht, hs]
    · have hh := single_le_sum (fun n _ => abs_nonneg (u n))
        (show N ∈ range M by simpa only [mem_range] using Nat.lt_of_not_ge hMN)
      dsimp only [C]
      linarith only [hh, abs_nonneg L]
  intro δ hδ
  refine ⟨C, hC, fun N hN => (hbound N).trans ?_⟩
  exact le_mul_of_one_le_right hC
    (Real.one_le_rpow (by exact_mod_cast hN) (by linarith only [hδ]))

/-- Every convergent power tail has zero strict growth exponent. -/
theorem powerCombTailGrowth_zero_of_converges {a : ℝ} (h : PowerCombTailConverges a) :
    PowerCombTailGrowth a 0 := by
  obtain ⟨L, hL⟩ := h
  exact strictGrowth_zero_of_tendsto hL

/-- Convergence of every positive subcritical power tail forces RH. -/
theorem riemannHypothesis_of_all_powerCombTails_converge
    (h : ∀ a : ℝ, 0 < a → a < 1 / 2 → PowerCombTailConverges a) : RiemannHypothesis := by
  apply riemannHypothesis_iff_all_powerCombTails_subpolynomial.mpr
  intro a ha ha2
  exact powerCombTailGrowth_zero_of_converges (h a ha ha2)

/-- RH is equivalent to convergence of all literal subcritical power combs. -/
theorem riemannHypothesis_iff_all_powerCombTails_converge :
    RiemannHypothesis ↔ ∀ a : ℝ, 0 < a → a < 1 / 2 → PowerCombTailConverges a := by
  constructor
  · intro hRH a ha ha2
    exact ⟨powerTailCombMellinIntegral a, tendsto_powerCombTail_of_rh hRH ha ha2⟩
  · exact riemannHypothesis_of_all_powerCombTails_converge

/-- The same criterion specifies the limit of every power comb. -/
theorem riemannHypothesis_iff_powerCombTails_tendsto_mellin_integrals :
    RiemannHypothesis ↔ ∀ a : ℝ, 0 < a → a < 1 / 2 →
      Tendsto (powerCombTail a) atTop (𝓝 (powerTailCombMellinIntegral a)) := by
  constructor
  · exact fun hRH a ha ha2 => tendsto_powerCombTail_of_rh hRH ha ha2
  · intro h
    exact riemannHypothesis_of_all_powerCombTails_converge
      (fun a ha ha2 => ⟨powerTailCombMellinIntegral a, h a ha ha2⟩)

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
