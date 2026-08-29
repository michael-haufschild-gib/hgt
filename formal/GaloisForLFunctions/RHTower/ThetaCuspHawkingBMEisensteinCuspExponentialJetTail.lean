import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinCuspAnalyticFinitePart
import GaloisForLFunctions.HTGeometry.AbeDerivativeDampingNoGo
import GaloisForLFunctions.HTGeometry.ExpRayL2
import GaloisForLFunctions.RHTower.PerronPolyExpAbsorb

/-!
# Infinite differentiated Eisenstein cusp tails vanish

After the diagonal Eisenstein constant terms are removed by analytic-family finite part, the two
Stokes currents contain nonconstant Whittaker packets.  Differentiation introduces fixed powers
of cusp height, so termwise exponential decay or a finite-mode argument is insufficient.

This module packages an infinite cusp jet tail with degree `m`, coefficients `a_n`, and the exact
summable majorant supplied by

`Y^m exp(-(n+1)Y) <= m! (2/(n+1))^m exp(-(n+1)Y/2)`.

The summability certificate is carried by the packet subtype, not assumed by the theorem.  A
Tannery argument then proves unconditionally that the complete infinite complex packet tends to
zero at the cusp.  This closes the limit theorem required after an actual Eisenstein Fourier
coefficient packet is admitted; constructing that coefficient packet from the Whittaker expansion
is kept as the remaining source-specific step.

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [HC94] [INFINITE CUSP JET TAIL]`
-/

open Complex Real Filter Topology

namespace RHTower

noncomputable section

/-- Infinite differentiated cusp packet with its one-scale summability certificate. -/
structure D4BMCuspExponentialJetTailPacket where
  degree : ℕ
  coefficient : ℕ → ℂ
  weightedNormSummable :
    Summable (fun n =>
      ‖coefficient n‖ * (degree.factorial : ℝ) *
        (2 / ((n : ℝ) + 1)) ^ degree *
        Real.exp (-(((n : ℝ) + 1) / 2)))

/-- Complete infinite cusp tail at height `Y`. -/
def d4BMCuspExponentialJetTail
    (packet : D4BMCuspExponentialJetTailPacket) (Y : ℝ) : ℂ :=
  ∑' n : ℕ, packet.coefficient n * (Y : ℂ) ^ packet.degree *
    (Real.exp (-(((n : ℝ) + 1) * Y)) : ℂ)

/-- Every admitted infinite differentiated cusp packet vanishes at infinite height. -/
theorem tendsto_d4BMCuspExponentialJetTail_atTop_zero
    (packet : D4BMCuspExponentialJetTailPacket) :
    Tendsto (d4BMCuspExponentialJetTail packet) atTop (𝓝 0) := by
  apply GaloisForLFunctions.HTGeometry.tendsto_tsum_zero_of_pointwise_damping_of_summable_majorant
    packet.weightedNormSummable
  · intro n
    let a : ℝ := (n : ℝ) + 1
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have hscale : Tendsto (fun Y : ℝ => a * Y) atTop atTop := by
      simpa using tendsto_id.const_mul_atTop ha
    have hbase := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero packet.degree
    have hscaled := hbase.comp hscale
    have haNe : a ^ packet.degree ≠ 0 := pow_ne_zero _ ha.ne'
    have hreal : Tendsto
        (fun Y : ℝ => Y ^ packet.degree * Real.exp (-(a * Y)))
        atTop (𝓝 0) := by
      have hmul := hscaled.const_mul (a ^ packet.degree)⁻¹
      convert hmul using 1
      · funext Y
        dsimp [Function.comp_def]
        rw [mul_pow]
        field_simp
      · simp
    have hc : Tendsto
        (fun Y : ℝ => ((Y ^ packet.degree * Real.exp (-(a * Y)) : ℝ) : ℂ))
        atTop (𝓝 0) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
    simpa [d4BMCuspExponentialJetTail, a, mul_assoc, ofReal_mul, ofReal_pow] using
      hc.const_mul (packet.coefficient n)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
    intro n
    have hY0 : 0 ≤ Y := zero_le_one.trans hY
    have ha : 0 < (n : ℝ) + 1 := by positivity
    have habsorb := pow_mul_exp_neg_le_absorb_half ha hY0 packet.degree
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hY0,
      abs_of_pos (Real.exp_pos _)]
    calc
      ‖packet.coefficient n‖ * Y ^ packet.degree *
          Real.exp (-(((n : ℝ) + 1) * Y)) =
          ‖packet.coefficient n‖ *
            (Y ^ packet.degree * Real.exp (-(((n : ℝ) + 1) * Y))) := by ring
      _ ≤ ‖packet.coefficient n‖ *
          ((packet.degree.factorial : ℝ) * (2 / ((n : ℝ) + 1)) ^ packet.degree *
            Real.exp (-(((n : ℝ) + 1) * Y / 2))) :=
        mul_le_mul_of_nonneg_left habsorb (norm_nonneg _)
      _ ≤ ‖packet.coefficient n‖ * (packet.degree.factorial : ℝ) *
          (2 / ((n : ℝ) + 1)) ^ packet.degree *
          Real.exp (-(((n : ℝ) + 1) / 2)) := by
        have hexp : Real.exp (-(((n : ℝ) + 1) * Y / 2)) ≤
            Real.exp (-(((n : ℝ) + 1) / 2)) := by
          apply Real.exp_le_exp.mpr
          nlinarith
        have hnonneg : 0 ≤ ‖packet.coefficient n‖ *
            (packet.degree.factorial : ℝ) *
            (2 / ((n : ℝ) + 1)) ^ packet.degree := by positivity
        calc
          _ = (‖packet.coefficient n‖ * (packet.degree.factorial : ℝ) *
              (2 / ((n : ℝ) + 1)) ^ packet.degree) *
              Real.exp (-(((n : ℝ) + 1) * Y / 2)) := by ring
          _ ≤ (‖packet.coefficient n‖ * (packet.degree.factorial : ℝ) *
              (2 / ((n : ℝ) + 1)) ^ packet.degree) *
              Real.exp (-(((n : ℝ) + 1) / 2)) :=
            mul_le_mul_of_nonneg_left hexp hnonneg
          _ = _ := by ring

end

end RHTower
