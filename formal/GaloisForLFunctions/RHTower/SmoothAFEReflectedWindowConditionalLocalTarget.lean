import GaloisForLFunctions.RHTower.SteinhausFrozenWindowLocalTarget
import GaloisForLFunctions.RHTower.SmoothAFEReflectedWindowChannelUpper
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics


open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace RHTower
open SteinhausModel

/-- A fixed logarithmic covariance floor gives a polynomial target cost for the actual reflected carrier at any compatible independent cutoff. -/
theorem eventually_frozenReflectedWindowCarrier_localTarget_ge
    {J : ℕ} (hJ : 0 < J) (d b : Fin J → ℝ)
    (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2) {D : ℕ} (hD : 0 < D)
    {H B ρ : ℝ} (hH : 0 < H) (hρ : 0 < ρ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ tau ∈ Set.Icc ((5 / 4 : ℝ) * N) ((7 / 4 : ℝ) * N),
      ∀ L : ℕ, N ≤ L → ∀ ω : Omega, ∀ t : EuclideanSpace ℂ (Fin J),
      L < (N / D) * (N / D) →
      ‖t - steinhausHilbertRetainedCarrier
        (fun j => smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) 1 N)
        L (steinhausWindowRetainedPrimes L N (N / D)) ω‖ ≤ B →
      (∀ u : Fin J → ℂ, H / Real.log N * ‖u‖ ^ 2 ≤ ∑ p ∈ largePrimes N (N / D),
        ‖∑ j, steinhausLargePrimeChannel
          (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) 1 N)
          L p ω * u j‖ ^ 2) →
      (1 / 4 : ℝ) * (N : ℝ) ^ (-(2 * J * B ^ 2 / H)) ≤
        steinhausMeasure.real {η |
          ‖steinhausHilbertCarrier
            (fun j => smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) 1 N)
            L (freezeSteinhausPrefix (steinhausWindowRetainedPrimes L N (N / D)) ω η) - t‖ < ρ} := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  obtain ⟨C, hC, hdot⟩ := exists_eventually_reflectedPrimalWindowChannel_dot_upper d b hd hdhalf hD
  have hbase : Tendsto (fun N : ℕ => Real.log N / (N : ℝ) ^ (1 / 2 : ℝ))
      atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hsmalllim : Tendsto (fun N : ℕ =>
      C * (N : ℝ) ^ (-(1 / 2 : ℝ)) * B / ((H / Real.log N) / J)) atTop (𝓝 0) := by
    convert hbase.mul_const (C * B * J / H) using 1
    · ext N
      rw [Real.rpow_neg (Nat.cast_nonneg N)]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring
    · ring
  obtain ⟨C₁, _, henergy⟩ :=
    exists_eventually_reflectedPrimalWindowConditional_energy_upper d b hd hdhalf hD
  have hloglim : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdecay : Tendsto (fun N : ℕ => C₁ / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hloglim
  have henergySmall := hdecay.eventually
    (gt_mem_nhds (show (0 : ℝ) < ρ ^ 2 / (2 * J) by positivity))
  filter_upwards [hdot, henergy, henergySmall, hsmalllim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_ge_atTop 2] with N hdotN henergyN henergySmallN hsmallN hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos hN1
  have hden : 0 < (H / Real.log N) / J := by positivity
  intro tau htau L hNL ω t hLY ht hlower
  let a := fun j => smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) 1 N
  have hlocal := measureReal_frozenSteinhausWindowCarrier_localTarget_ge hJ a L N (N / D)
    (Nat.div_le_self _ _) hNL hLY ω
    (div_pos hH hlog) (show 0 ≤ C * (N : ℝ) ^ (-(1 / 2 : ℝ)) by positivity) hρ hlower
    (fun p hp u => hdotN tau htau L ω u p hp)
    (fun u => (henergyN tau htau L ω u).trans
      (mul_le_mul_of_nonneg_right henergySmallN.le (sq_nonneg _))) t
    (le_trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left ht (by positivity)) hden.le) hsmallN.le)
    (show (J : ℝ) * (ρ ^ 2 / (2 * J)) ≤ ρ ^ 2 / 2 by
      apply le_of_eq
      field_simp)
  have hsq : ‖t - steinhausHilbertRetainedCarrier a L (steinhausWindowRetainedPrimes L N (N / D)) ω‖ ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) ht 2
  have hcost : -2 * B ^ 2 / ((H / Real.log N) / J) ≤
      -2 * ‖t - steinhausHilbertRetainedCarrier a L (steinhausWindowRetainedPrimes L N (N / D)) ω‖ ^ 2 / ((H / Real.log N) / J) :=
    div_le_div_of_nonneg_right (by linarith) hden.le
  calc
    _ = (1 / 4 : ℝ) * Real.exp (-2 * B ^ 2 / ((H / Real.log N) / J)) := by
      rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hN1)]
      congr 2
      field_simp
    _ ≤ _ := (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcost) (by norm_num)).trans hlocal

end RHTower
