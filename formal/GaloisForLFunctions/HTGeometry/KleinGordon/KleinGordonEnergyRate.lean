import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonBandRate

/-!
# The energy grows at twice the Floquet exponent

The card's subject is the energy `E(t) = ‖⟨D⟩u(t)‖² + ‖∂ₜu(t)‖²`, and the Floquet theory has been
carried on the state, whose norm is its square root. So everything said about the rate of the state
says the same about the energy with the exponent doubled:

`E(nT) ≤ ‖Mⁿ‖²·E(0)`,   hence eventually   `E(nT) ≤ (r+ε)^{2n}·E(0)`.

The band transfer of statement 417 then reads: **if the band models decay at a uniform geometric rate
below one, the true clock's energy decays** — the property the card set out to estimate, decided on the
models where the Cauchy problem is a genuine strong problem.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section EnergyRate

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

/-- **The energy after `n` periods is bounded by the square of the operator norm.** -/
theorem kgFieldEnergyT_pow_le (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (g h : Lp ℂ 2 (volume : Measure E)) (n : ℕ) :
    ‖kgFieldGradT W g h ((n : ℝ) * T)‖ ^ 2 + ‖kgFieldVelT W g h ((n : ℝ) * T)‖ ^ 2
      ≤ ‖kgMonodromy W b hb0 hWb hWs T ^ n‖ ^ 2 * (‖g‖ ^ 2 + ‖h‖ ^ 2) := by
  have hstate : ‖kgFieldStateT W g h ((n : ℝ) * T)‖
      ≤ ‖kgMonodromy W b hb0 hWb hWs T ^ n‖ * ‖kgPair E (g, h)‖ := by
    rw [kgFieldStateT_monodromy_pow hb0 hWb hWs hper g h n]
    exact (kgMonodromy W b hb0 hWb hWs T ^ n).le_opNorm _
  have hnn : (0 : ℝ) ≤ ‖kgFieldStateT W g h ((n : ℝ) * T)‖ := norm_nonneg _
  have hR : (0 : ℝ) ≤ ‖kgMonodromy W b hb0 hWb hWs T ^ n‖ * ‖kgPair E (g, h)‖ := by positivity
  have hsq := mul_self_le_mul_self hnn hstate
  rw [kgFieldEnergyT_eq_norm_sq W g h ((n : ℝ) * T)]
  have hL : ‖kgFieldStateT W g h ((n : ℝ) * T)‖ ^ 2
      = ‖kgFieldStateT W g h ((n : ℝ) * T)‖ * ‖kgFieldStateT W g h ((n : ℝ) * T)‖ := by ring
  have hpair : ‖kgPair E (g, h)‖ ^ 2 = ‖g‖ ^ 2 + ‖h‖ ^ 2 := norm_kgPair_sq g h
  rw [hL]
  calc ‖kgFieldStateT W g h ((n : ℝ) * T)‖ * ‖kgFieldStateT W g h ((n : ℝ) * T)‖
      ≤ (‖kgMonodromy W b hb0 hWb hWs T ^ n‖ * ‖kgPair E (g, h)‖)
        * (‖kgMonodromy W b hb0 hWb hWs T ^ n‖ * ‖kgPair E (g, h)‖) := hsq
    _ = ‖kgMonodromy W b hb0 hWb hWs T ^ n‖ ^ 2 * ‖kgPair E (g, h)‖ ^ 2 := by ring
    _ = ‖kgMonodromy W b hb0 hWb hWs T ^ n‖ ^ 2 * (‖g‖ ^ 2 + ‖h‖ ^ 2) := by rw [hpair]

/-- **The energy grows at twice the Floquet exponent.** -/
theorem eventually_kgFieldEnergyT_le_rate (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) {ε : ℝ} (hε : 0 < ε)
    (g h : Lp ℂ 2 (volume : Measure E)) :
    ∀ᶠ n : ℕ in atTop,
      ‖kgFieldGradT W g h ((n : ℝ) * T)‖ ^ 2 + ‖kgFieldVelT W g h ((n : ℝ) * T)‖ ^ 2
        ≤ (((spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T)).toReal + ε) ^ n) ^ 2
          * (‖g‖ ^ 2 + ‖h‖ ^ 2) := by
  have hpow := eventually_norm_pow_le_of_spectralRadius
    (spectralRadius_kgMonodromy_ne_top hb0 hWb hWs hper) hε
  filter_upwards [hpow] with n hn
  refine (kgFieldEnergyT_pow_le hb0 hWb hWs hper g h n).trans ?_
  have hsq : ‖kgMonodromy W b hb0 hWb hWs T ^ n‖ ^ 2
      ≤ (((spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T)).toReal + ε) ^ n) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖kgMonodromy W b hb0 hWb hWs T ^ n‖ := norm_nonneg _
    nlinarith [hn, h0]
  have hdata : (0 : ℝ) ≤ ‖g‖ ^ 2 + ‖h‖ ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_right hsq hdata

/-- **A band model decaying at a uniform geometric rate below one makes the true clock decay.** -/
theorem tendsto_kgFieldStateT_zero_of_band_rate (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hT : 0 < T) {C q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hC : ∀ R : ℝ, ∀ n : ℕ, ‖kgBandMonodromy W b hb0 hWb hWs R T ^ n‖ ≤ C * q ^ n)
    (g h : Lp ℂ 2 (volume : Measure E)) :
    Tendsto (fun t : ℝ => kgFieldStateT W g h t) atTop (𝓝 0) := by
  have hrad := spectralRadius_le_of_band_rate hb0 hWb hWs hT.le hq0 hC
  have hlt : spectralRadius ℂ (kgMonodromy W b hb0 hWb hWs T) < 1 :=
    lt_of_le_of_lt hrad (ENNReal.ofReal_lt_one.mpr hq1)
  exact tendsto_kgFieldStateT_zero_of_spectralRadius hb0 hWb hWs hper hT hlt g h

end EnergyRate

end GaloisForLFunctions.HTGeometry
