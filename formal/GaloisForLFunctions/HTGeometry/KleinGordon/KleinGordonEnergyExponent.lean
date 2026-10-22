import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonEnergyRate

/-!
# The card's estimate at the true rate

The card opens with `E(t) ≤ E(0)·e^{(‖V‖+1)|t|}` for a compactly supported classical solution. The
spectral theory replaces the exponent by the truth: the state grows at `log(r+ε)/T` in continuous time
(statement 414), and the energy is the square of the state's norm, so

`E(t) ≤ e^{2(log(r+ε)/T)·t}·E(0)·e^{2bT}`   for all large `t`.

That is the card's opening estimate with the rate the clock actually has — twice the Floquet exponent —
and a constant that costs one period.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section EnergyExponent

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

theorem exp_mul_self (x : ℝ) : Real.exp x * Real.exp x = Real.exp (2 * x) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- **The energy obeys the card's estimate at the true rate.** -/
theorem eventually_kgFieldEnergyT_le_exp_rate (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hT : 0 < T) {ε : ℝ} (hε : 0 < ε)
    (hq : 1 ≤ (spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T)).toReal + ε)
    (g h : Lp ℂ 2 (volume : Measure E)) :
    ∀ᶠ t : ℝ in atTop,
      ‖kgFieldGradT W g h t‖ ^ 2 + ‖kgFieldVelT W g h t‖ ^ 2
        ≤ Real.exp (2 * (Real.log ((spectralRadius ℂ
            (kgMonodromy W b hb0 hWb hWs T)).toReal + ε) / T * t))
          * (‖g‖ ^ 2 + ‖h‖ ^ 2) * Real.exp (2 * (b * T)) := by
  set μ : ℝ :=
    Real.log ((spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T)).toReal + ε) / T with hμ
  have hstate := eventually_norm_kgFieldStateT_le_exp_rate hb0 hWb hWs hper hT hε hq g h
  filter_upwards [hstate] with t ht
  have hnn : (0 : ℝ) ≤ ‖kgFieldStateT W g h t‖ := norm_nonneg _
  have hsq := mul_self_le_mul_self hnn ht
  have hpair : ‖kgPair E (g, h)‖ ^ 2 = ‖g‖ ^ 2 + ‖h‖ ^ 2 := norm_kgPair_sq g h
  have hexpand : (Real.exp (μ * t) * ‖kgPair E (g, h)‖ * Real.exp (b * T))
        * (Real.exp (μ * t) * ‖kgPair E (g, h)‖ * Real.exp (b * T))
      = Real.exp (2 * (μ * t)) * (‖kgPair E (g, h)‖ ^ 2) * Real.exp (2 * (b * T)) := by
    rw [← exp_mul_self (μ * t), ← exp_mul_self (b * T)]
    ring
  rw [kgFieldEnergyT_eq_norm_sq W g h t]
  have hL : ‖kgFieldStateT W g h t‖ ^ 2
      = ‖kgFieldStateT W g h t‖ * ‖kgFieldStateT W g h t‖ := by ring
  rw [hL]
  refine hsq.trans ?_
  rw [hexpand, hpair]

end EnergyExponent

end GaloisForLFunctions.HTGeometry
