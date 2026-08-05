import GaloisForLFunctions.HTGeometry.KleinGordonTwoSidedRate

/-!
# The card's inequality, at the sharp rate, in both directions

The card opens with

`E(t) ≤ E(0)·e^{(‖V‖_∞+1)|t|}`

for a classical solution with uniformly compact spatial support. Squaring the two-sided state bound of
statement 424 gives the same inequality for an arbitrary `L²` datum in a periodic background even in
time, with the exponent replaced by twice the Floquet exponent — the rate the clock actually has:

`E(t) ≤ e^{2μ|t|}·E(0)·e^{2bT}`,   `μ = log(r+ε)/T`,   for all `|t|` large.

The rate is bounded by the estimate's own `b` (statement 397) and is generally smaller; for the free
field it is zero, and the inequality becomes exact conservation.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section EnergyTwoSided

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The card's inequality at the sharp rate, in both directions of time.** -/
theorem exists_bound_kgFieldEnergyT_abs (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hsym : ∀ r : ℝ, W (-r) = W r) (hT : 0 < T)
    {ε : ℝ} (hε : 0 < ε)
    (hq : 1 ≤ (spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T)).toReal + ε)
    (g h : Lp ℂ 2 (volume : Measure E)) :
    ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ |t| →
      ‖kgFieldGradT W g h t‖ ^ 2 + ‖kgFieldVelT W g h t‖ ^ 2
        ≤ Real.exp (2 * (Real.log ((spectralRadius ℂ
            (kgMonodromy W b hb0 hWb hWs T)).toReal + ε) / T * |t|))
          * (‖g‖ ^ 2 + ‖h‖ ^ 2) * Real.exp (2 * (b * T)) := by
  set μ : ℝ :=
    Real.log ((spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T)).toReal + ε) / T with hμ
  obtain ⟨t₀, ht₀⟩ := exists_bound_norm_kgFieldStateT_abs hb0 hWb hWs hper hsym hT hε hq g h
  refine ⟨t₀, fun t ht => ?_⟩
  have hstate := ht₀ t ht
  have hnn : (0 : ℝ) ≤ ‖kgFieldStateT W g h t‖ := norm_nonneg _
  have hsq := mul_self_le_mul_self hnn hstate
  have hpair : ‖kgPair E (g, h)‖ ^ 2 = ‖g‖ ^ 2 + ‖h‖ ^ 2 := norm_kgPair_sq g h
  have hexpand : (Real.exp (μ * |t|) * ‖kgPair E (g, h)‖ * Real.exp (b * T))
        * (Real.exp (μ * |t|) * ‖kgPair E (g, h)‖ * Real.exp (b * T))
      = Real.exp (2 * (μ * |t|)) * (‖kgPair E (g, h)‖ ^ 2) * Real.exp (2 * (b * T)) := by
    rw [← exp_mul_self (μ * |t|), ← exp_mul_self (b * T)]
    ring
  rw [kgFieldEnergyT_eq_norm_sq W g h t]
  have hL : ‖kgFieldStateT W g h t‖ ^ 2
      = ‖kgFieldStateT W g h t‖ * ‖kgFieldStateT W g h t‖ := by ring
  rw [hL]
  refine hsq.trans ?_
  rw [hexpand, hpair]

end EnergyTwoSided

end GaloisForLFunctions.HTGeometry
