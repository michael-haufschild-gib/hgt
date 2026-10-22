import GaloisForLFunctions.BezoutValuationIncidence.PowerDampedResidualHasLinearCusp
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Positive residual work escapes every fixed horizon

The literal residual has a linear cusp, although its work tends to zero at each fixed
horizon. The mean value theorem therefore detects positive work at arbitrarily small
damping and arbitrarily large horizons. All differentiation stays at positive damping.
-/

open Finset Set Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
noncomputable section
set_option autoImplicit false

/-- The signed pairing of the residual with its actual arithmetic damping tangent. -/
def residualDampingWork (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 T, (pmPowerDampedCenteredDivisorPrefix ε n - 1) *
    dampedChebyshevError ε n / ((n : ℝ) * ((n : ℝ) + 1))

theorem hasDerivAt_pmPowerDampedDualResidual {ε : ℝ} (hε : 0 < ε) (T : ℕ) :
    HasDerivAt (fun x => pmPowerDampedDualResidual x T)
      (2 * residualDampingWork ε T) ε := by
  have h := HasDerivAt.fun_sum (u := Icc 1 T)
    (A := fun n x => (pmPowerDampedCenteredDivisorPrefix x n - 1) ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1)))
    (A' := fun n => 2 * (pmPowerDampedCenteredDivisorPrefix ε n - 1) *
      dampedChebyshevError ε n / ((n : ℝ) * ((n : ℝ) + 1)))
    (fun n _ => by
      have hp := (((hasDerivAt_pmPowerDampedCenteredDivisorPrefix hε n).sub_const 1).pow 2).
        div_const ((n : ℝ) * ((n : ℝ) + 1))
      refine hp.congr_deriv ?_
      push_cast
      ring)
  refine h.congr_deriv ?_
  rw [residualDampingWork, mul_sum]
  exact sum_congr rfl fun n _ => by ring

theorem tendsto_pmPowerDampedDualResidual_zero (T : ℕ) :
    Tendsto (fun ε => pmPowerDampedDualResidual ε T) (𝓝[>] 0) (𝓝 0) := by
  unfold pmPowerDampedDualResidual
  simpa only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, sum_const_zero]
    using tendsto_finsetSum (Icc 1 T) (fun n hn =>
      (((tendsto_pmPowerDampedCenteredDivisorPrefix_zero (mem_Icc.mp hn).1).
        sub_const 1).pow 2).div_const ((n : ℝ) * ((n : ℝ) + 1)))

/-- Each fixed horizon has vanishing work, despite the escaping positive lower bound. -/
theorem tendsto_residualDampingWork_zero (T : ℕ) :
    Tendsto (fun ε => residualDampingWork ε T) (𝓝[>] 0) (𝓝 0) := by
  unfold residualDampingWork
  simpa only [sub_self, zero_mul, zero_div, sum_const_zero] using
    tendsto_finsetSum (Icc 1 T) (fun n hn =>
      (((tendsto_pmPowerDampedCenteredDivisorPrefix_zero (mem_Icc.mp hn).1).
        sub_const 1).mul (tendsto_dampedChebyshevError_zero n)).div_const
          ((n : ℝ) * ((n : ℝ) + 1)))

private theorem exists_residualDampingWork_gt_of_cusp {c t : ℝ} (ht : 0 < t) (T : ℕ)
    (hcusp : c * t < pmPowerDampedDualResidual t T) :
    ∃ ε : ℝ, 0 < ε ∧ ε < t ∧ c / 2 < residualDampingWork ε T := by
  let g : ℝ → ℝ := fun u => pmPowerDampedDualResidual u T - c * u
  have hgt : 0 < g t := sub_pos.mpr hcusp
  have hgzero : Tendsto g (𝓝[>] 0) (𝓝 0) := by
    have hid : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [g, mul_zero, sub_zero] using
      (tendsto_pmPowerDampedDualResidual_zero T).sub (hid.const_mul c)
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a ∧ a < t ∧ g a < g t := by
    filter_upwards [Ioo_mem_nhdsGT ht, hgzero.eventually (gt_mem_nhds hgt)] with a ha hga
    exact ⟨ha.1, ha.2, hga⟩
  obtain ⟨a, ha, hat, hga⟩ := hsmall.exists
  have hder (u : ℝ) (hu : 0 < u) :
      HasDerivAt g (2 * residualDampingWork u T - c) u := by
    simpa only [mul_one] using
      (hasDerivAt_pmPowerDampedDualResidual hu T).sub ((hasDerivAt_id u).const_mul c)
  have hcont : ContinuousOn g (Icc a t) := by
    intro u hu
    exact (hder u (ha.trans_le hu.1)).continuousAt.continuousWithinAt
  obtain ⟨ε, hε, hslope⟩ := exists_hasDerivAt_eq_slope g
    (fun u => 2 * residualDampingWork u T - c) hat hcont
    (fun u hu => hder u (ha.trans hu.1))
  have hpos : 0 < 2 * residualDampingWork ε T - c := by
    rw [hslope]
    exact div_pos (sub_pos.mpr hga) (sub_pos.mpr hat)
  exact ⟨ε, ha.trans hε.1, hε.2, by linarith⟩

/-- The cusp forces a positive amount of actual residual work arbitrarily near zero damping. -/
theorem exists_positive_residualDampingWork_near_zero :
    ∃ κ : ℝ, 0 < κ ∧ ∀ δ : ℝ, 0 < δ →
      ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∃ T : ℕ, κ < residualDampingWork ε T := by
  obtain ⟨c, hc, δ₀, hδ₀, hfloor⟩ := exists_positive_linear_dualResidual_floor
  refine ⟨c / 2, by positivity, ?_⟩
  intro δ hδ
  let t : ℝ := min δ δ₀ / 2
  have hmin : 0 < min δ δ₀ := lt_min hδ hδ₀
  have ht : 0 < t := div_pos hmin (by norm_num)
  have htm : t < min δ δ₀ := div_lt_self hmin (by norm_num)
  obtain ⟨T, hT⟩ := hfloor t ht (htm.trans_le (min_le_right _ _))
  obtain ⟨ε, hε, hεt, hw⟩ := exists_residualDampingWork_gt_of_cusp ht T hT
  exact ⟨ε, hε, hεt.trans (htm.trans_le (min_le_left _ _)), T, hw⟩

/-- Positive residual work persists near zero only at horizons escaping every finite cutoff.
No admission or infinite-horizon differentiation is used. -/
theorem exists_positive_residualDampingWork_escaping_horizons :
    ∃ κ : ℝ, 0 < κ ∧ ∀ N : ℕ, ∀ δ : ℝ, 0 < δ →
      ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∃ T : ℕ, N < T ∧ κ < residualDampingWork ε T := by
  obtain ⟨κ, hκ, hwork⟩ := exists_positive_residualDampingWork_near_zero
  refine ⟨κ, hκ, ?_⟩
  intro N δ hδ
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ∀ T ∈ range (N + 1), residualDampingWork ε T < κ := by
    rw [Filter.eventually_all_finset]
    intro T hT
    exact (tendsto_residualDampingWork_zero T).eventually (gt_mem_nhds hκ)
  obtain ⟨η, hη, hsmallη⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hsmall
  obtain ⟨ε, hε, hεsmall, T, hw⟩ := hwork (min δ η) (lt_min hδ hη)
  have hεδ : ε < δ := hεsmall.trans_le (min_le_left _ _)
  have hεη : ε < η := hεsmall.trans_le (min_le_right _ _)
  refine ⟨ε, hε, hεδ, T, ?_, hw⟩
  by_contra hNT
  have hTN : T ∈ range (N + 1) := mem_range.mpr (by omega)
  exact (not_lt_of_ge (hsmallη ⟨hε, hεη⟩ T hTN).le) hw

end
end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
