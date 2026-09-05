/-
Thermodynamic phase normalization and arithmetic recovery.

At each fixed point of the open critical strip, the normalized alternating
Dirichlet signal tends to zero while remaining eventually nonzero. Multiplication
by its thermal partition recovers arithmetic information but has divergent error
gain. The logarithmic decay-rate limit, unlike the raw signal limit, detects the
zeta divisor; it does not force the divisor onto the critical line.
-/

import GaloisForLFunctions.RHTower.DQPTObservables
import GaloisForLFunctions.RHTower.DQPTFreeEnergy
import GaloisForLFunctions.RHTower.FractionalPartZeta

open Complex Filter Topology

namespace RHTower.DQPT

noncomputable section

/-- The literal thermal normalization diverges throughout the open critical strip. -/
theorem dqptPartition_tendsto_atTop {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) :
    Tendsto (dqptPartition β) atTop atTop := by
  apply tendsto_atTop_mono' atTop
    (show (fun N : ℕ => (N : ℝ) ^ (1 - β)) ≤ᶠ[atTop] dqptPartition β from ?_)
  · exact (tendsto_rpow_atTop (sub_pos.mpr hβ1)).comp tendsto_natCast_atTop_atTop
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact dqptPartition_rpow_le hβ.le hN

/-- Raw normalized phase tends to zero at every fixed strip point, not only at zeros. -/
theorem dqptPhaseFactor_tendsto_zero {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (t : ℝ) :
    Tendsto (dqptPhaseFactor β t) atTop (𝓝 0) := by
  let s : ℂ := (β : ℂ) + (t : ℂ) * I
  have hs : s.re = β := by simp [s]
  have hsne : s ≠ 1 := by
    intro heq
    have := congrArg Complex.re heq
    rw [hs] at this
    simp only [Complex.one_re] at this
    linarith
  have hnum := (dqpt_altPartialSum_tendsto (s := s) (by simpa [hs] using hβ) hsne).neg
  have hinv : Tendsto (fun N : ℕ => ((dqptPartition β N)⁻¹ : ℂ)) atTop (𝓝 0) := by
    exact_mod_cast (Complex.continuous_ofReal.tendsto 0).comp
      (tendsto_inv_atTop_zero.comp (dqptPartition_tendsto_atTop hβ hβ1))
  have hlim := hnum.mul hinv
  change Tendsto (fun N : ℕ => dqptPhaseFactor β t N) atTop (𝓝 0)
  simpa only [dqptPhaseFactor_eq, div_eq_mul_inv, Complex.ofReal_inv, mul_zero, s] using hlim

/-- A concrete nonzero zeta value has the same vanishing raw thermodynamic readout. -/
theorem dqptPhaseFactor_half_zero_blind :
    Tendsto (dqptPhaseFactor (1 / 2) 0) atTop (𝓝 0) ∧
      riemannZeta (1 / 2 : ℂ) ≠ 0 := by
  constructor
  · exact dqptPhaseFactor_tendsto_zero (by norm_num) (by norm_num) 0
  · simpa using (riemannZeta_ne_zero_of_ofReal_mem_Ioo
      (σ := (1 / 2 : ℝ)) (by norm_num) (by norm_num))

/-- At every fixed strip point, all sufficiently late finite readouts are nonzero. -/
theorem dqptPhaseFactor_eventually_ne_zero {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (t : ℝ) :
    ∀ᶠ N : ℕ in atTop, dqptPhaseFactor β t N ≠ 0 := by
  let s : ℂ := (β : ℂ) + (t : ℂ) * I
  have hs : s.re = β := by simp [s]
  have hs0 : 0 < s.re := by simpa [hs] using hβ
  have hsne : s ≠ 1 := by
    intro heq
    have := congrArg Complex.re heq
    rw [hs] at this
    simp only [Complex.one_re] at this
    linarith
  have hnum : ∀ᶠ N : ℕ in atTop, dqptAltPartialSum s N ≠ 0 := by
    by_cases hz : (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s = 0
    · exact dqpt_eventually_altPartialSum_ne_zero_of_eta_zero hs0 hsne hz
    · exact dqpt_eventually_altPartialSum_ne_zero_of_eta_ne_zero hs0 hsne hz
  filter_upwards [hnum, eventually_ge_atTop 1] with N hN hpos
  rw [dqptPhaseFactor_eq]
  exact div_ne_zero (neg_ne_zero.mpr hN)
    (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_dqptPartition β hpos))))

/-- Undoing thermal normalization has exact, not merely upper-bounded, error gain. -/
theorem dqptPhaseFactor_recovery_error (β t : ℝ) (N : ℕ) (e : ℂ) :
    ‖(dqptPartition β N : ℂ) * (dqptPhaseFactor β t N + e) -
        (dqptPartition β N : ℂ) * dqptPhaseFactor β t N‖ =
      dqptPartition β N * ‖e‖ := by
  rw [mul_add, add_sub_cancel_left, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (dqptPartition_nonneg β N)]

/-- Every fixed nonzero readout error acquires unbounded recovered arithmetic magnitude. -/
theorem dqptPhaseFactor_recovery_error_tendsto_atTop
    {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (t : ℝ) {e : ℂ} (he : e ≠ 0) :
    Tendsto (fun N : ℕ =>
      ‖(dqptPartition β N : ℂ) * (dqptPhaseFactor β t N + e) -
          (dqptPartition β N : ℂ) * dqptPhaseFactor β t N‖) atTop atTop := by
  simp_rw [dqptPhaseFactor_recovery_error]
  exact (dqptPartition_tendsto_atTop hβ hβ1).atTop_mul_const (norm_pos_iff.mpr he)

/-- The positive survivor is the decay-rate readout: its exceptional value detects exactly
the zeta divisor in the strip. It does not locate that divisor horizontally. -/
theorem dqpt_freeEnergy_limit_eq_log_two_iff {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1) :
    Tendsto (dqptFreeEnergyFinite s) atTop (𝓝 (Real.log 2)) ↔ riemannZeta s = 0 := by
  constructor
  · intro hlim
    by_contra hz
    have hfac := dqpt_eta_factor_ne_zero (ne_of_lt hs1)
    have hother := dqpt_freeEnergy_strip hs hs1 (mul_ne_zero hfac hz)
    have heq := tendsto_nhds_unique hlim hother
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith [mul_pos hs hlog]
  · intro hz
    exact dqpt_freeEnergy_at_eta_zero hs hs1 (by rw [hz, mul_zero])

end

end RHTower.DQPT


