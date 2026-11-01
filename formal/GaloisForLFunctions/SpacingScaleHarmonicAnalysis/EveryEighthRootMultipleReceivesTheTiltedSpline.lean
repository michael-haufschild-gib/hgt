import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheTiltedSplineReceivesAtTheEighthRoot
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheLowCompleteWeilSpectrumLivesOnTheLowConductors

/-!
# Every multiple of the eighth-root overlap receives the tilted spline

Diagonal selection makes the overlap multiple diverge sufficiently slowly.
The eighth-power synthesis error then tends to zero, so positivity at every
fixed multiple is equivalent to RH, also on the pole hyperplane.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology RHTower
open scoped Real ContDiff

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticElectrostatics RenormalizedArithmeticPotentialTheory

private theorem exists_eighthRoot_receiver_schedule (P : ℕ → ℝ → Prop)
    (hP : ∀ K : ℝ, 0 < K → ∀ᶠ N : ℕ in atTop,
      P N ((N : ℝ) / (K * Real.log N ^ (1 / 8 : ℝ)))) :
    ∃ κ : ℕ → ℝ, OverlapGrowthPow 8 κ ∧ ∀ᶠ N : ℕ in atTop, P N (κ N) := by
  let d : ℝ → ℕ → ℝ := fun K N => (N : ℝ) / (K * Real.log N ^ (1 / 8 : ℝ))
  have hbase : Tendsto (fun N : ℕ => (N : ℝ) / Real.log N ^ (1 / 8 : ℝ)) atTop atTop :=
    (overlapGrowthPow_log (q := 16) (by norm_num) (by norm_num)).1
  have hd : ∀ K : ℝ, 0 < K → Tendsto (d K) atTop atTop := by
    intro K hK
    have h := Filter.Tendsto.const_mul_atTop (inv_pos.mpr hK) hbase
    convert h using 1
    funext N
    simp only [d, div_eq_mul_inv, mul_inv_rev]
    ring
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨s, hs, hdiag⟩ := exists_schedule_of_forall_eventually
    (fun j N => P N (d ((j : ℝ) + 1) N) ∧ (j : ℝ) + 1 ≤ d ((j : ℝ) + 1) N ∧
      1 ≤ Real.log N ∧ 1 ≤ N) (fun j =>
        (hP ((j : ℝ) + 1) (by positivity)).and
          (((hd ((j : ℝ) + 1) (by positivity)).eventually_ge_atTop _).and
            ((hlog.eventually_ge_atTop 1).and (eventually_ge_atTop 1))))
  let κ : ℕ → ℝ := fun N => d ((s N : ℝ) + 1) N
  have hsreal : Tendsto (fun N => (s N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hs
  have hκ : Tendsto κ atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [hsreal.eventually_ge_atTop b, hdiag] with N hb hN
    exact hb.trans ((le_add_of_nonneg_right zero_le_one).trans hN.2.1)
  refine ⟨κ, ⟨hκ, ?_⟩, hdiag.mono fun N hN => hN.1⟩
  have hs1 : Tendsto (fun N => (s N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun N => le_add_of_nonneg_right zero_le_one) hsreal
  have hu : Tendsto (fun N => (1 / ((s N : ℝ) + 1)) ^ 8) atTop (𝓝 0) := by
    simpa only [one_div, Pi.inv_apply, zero_pow (by omega : (8 : ℕ) ≠ 0)] using
      hs1.inv_tendsto_atTop.pow 8
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
  · filter_upwards [hκ.eventually_ge_atTop 1] with N hN
    exact mul_nonneg (by positivity) (Real.log_nonneg hN)
  · filter_upwards [hdiag] with N hN
    let K : ℝ := (s N : ℝ) + 1
    have hK : 1 ≤ K := le_add_of_nonneg_left (Nat.cast_nonneg _)
    have hK0 : 0 < K := by linarith
    have hL : 1 ≤ Real.log N := hN.2.2.1
    have hL0 : 0 < Real.log N := by linarith
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN.2.2.2
    have hp : 1 ≤ Real.log N ^ (1 / 8 : ℝ) := Real.one_le_rpow hL (by norm_num)
    have hk1 : 1 ≤ κ N := hK.trans hN.2.1
    have hkN : κ N ≤ N := div_le_self hN0.le (one_le_mul_of_one_le_of_one_le hK hp)
    have hlogle : Real.log (κ N) ≤ Real.log N := Real.log_le_log (by linarith) hkN
    have hpow : (Real.log N ^ (1 / 8 : ℝ)) ^ (8 : ℕ) = Real.log N := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      norm_num
    have hratio : (κ N / N) ^ 8 = 1 / (K ^ 8 * Real.log N) := by
      change ((N : ℝ) / (K * Real.log N ^ (1 / 8 : ℝ)) / N) ^ 8 = _
      rw [div_div_cancel_left' hN0.ne', inv_pow, mul_pow, hpow, one_div]
    calc
      (κ N / N) ^ 8 * Real.log (κ N) ≤ (κ N / N) ^ 8 * Real.log N :=
        mul_le_mul_of_nonneg_left hlogle (by positivity)
      _ = (1 / K) ^ 8 := by rw [hratio]; field_simp

/-- Every fixed multiple of the eighth-root overlap detects Weil positivity.
The threshold horizon may depend on the multiple. -/
theorem riemannHypothesis_iff_tiltedSpline_nonneg_every_eighthRoot_multiple :
    RiemannHypothesis ↔ ∀ K : ℝ, 0 < K → ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x
        (dilate ((N : ℝ) / (K * Real.log N ^ (1 / 8 : ℝ)))
          (recentredProfile tiltedUnitSpline))) := by
  constructor
  · intro hRH K hK
    filter_upwards [eventually_ge_atTop 2] with N hN x
    have hN0 : (0 : ℝ) < N := by
      have h : (2 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    have hk : 0 < (N : ℝ) / (K * Real.log N ^ (1 / 8 : ℝ)) := by positivity
    obtain ⟨h2, hc⟩ := atomicTest_dilate_mem
      (contDiff_recentredProfile contDiff_tiltedUnitSpline)
      (vanishesOff_recentredProfile tiltedUnitSpline_eq_zero) hk N x
    exact WeilSpectral.riemannHypothesis_iff_real_weilPositive.mp hRH _ h2 hc
  · intro H
    obtain ⟨κ, hκ, hpos⟩ := exists_eighthRoot_receiver_schedule
      (fun N k => ∀ x : ℕ → ℝ,
        0 ≤ weilQuad (atomicTest N x (dilate k (recentredProfile tiltedUnitSpline)))) H
    exact (riemannHypothesis_iff_tiltedSpline_atomicFamilies_nonneg_of_growthEight hκ).mpr hpos

/-- The same endpoint completeness holds after removing the pole moment. -/
theorem riemannHypothesis_iff_tiltedSpline_pole_nonneg_every_eighthRoot_multiple :
    RiemannHypothesis ↔ ∀ K : ℝ, 0 < K → ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      poleMomentNeg (atomicTest N x
        (dilate ((N : ℝ) / (K * Real.log N ^ (1 / 8 : ℝ)))
          (recentredProfile tiltedUnitSpline))) = 0 →
      0 ≤ markovQuad (atomicTest N x
        (dilate ((N : ℝ) / (K * Real.log N ^ (1 / 8 : ℝ)))
          (recentredProfile tiltedUnitSpline))) := by
  constructor
  · intro hRH K hK
    filter_upwards [eventually_ge_atTop 2] with N hN x h0
    have hN0 : (0 : ℝ) < N := by
      have h : (2 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    have hk : 0 < (N : ℝ) / (K * Real.log N ^ (1 / 8 : ℝ)) := by positivity
    obtain ⟨h2, hc⟩ := atomicTest_dilate_mem
      (contDiff_recentredProfile contDiff_tiltedUnitSpline)
      (vanishesOff_recentredProfile tiltedUnitSpline_eq_zero) hk N x
    exact riemannHypothesis_iff_forall_exp_neg_half_moment_zero_markovEnergy_nonneg.mp
      hRH _ h2 hc h0
  · intro H
    obtain ⟨κ, hκ, hpos⟩ := exists_eighthRoot_receiver_schedule
      (fun N k => ∀ x : ℕ → ℝ,
        poleMomentNeg (atomicTest N x (dilate k (recentredProfile tiltedUnitSpline))) = 0 →
          0 ≤ markovQuad (atomicTest N x (dilate k (recentredProfile tiltedUnitSpline)))) H
    exact (riemannHypothesis_iff_tiltedSpline_poleHyperplane_nonneg_of_growthEight hκ).mpr hpos

/-- Complete Weil matrices at every overlap `2K(log N)^(1/8)` are eventually
positive semidefinite exactly when RH holds. -/
theorem riemannHypothesis_iff_tiltedSpline_completeWeil_nonneg_every_eighthRoot_multiple :
    RiemannHypothesis ↔ ∀ K : ℝ, 0 < K → ∀ᶠ N : ℕ in atTop,
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        0 ≤ completeWeilEnergy tiltedUnitSpline (2 * K * Real.log N ^ (1 / 8 : ℝ)) N x := by
  rw [riemannHypothesis_iff_tiltedSpline_nonneg_every_eighthRoot_multiple]
  have hc : ∀ K : ℝ, 0 < K → ∀ᶠ N : ℕ in atTop,
      0 < 2 * K * Real.log N ^ (1 / 8 : ℝ) := by
    intro K hK
    filter_upwards [eventually_ge_atTop 2] with N hN
    have : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    positivity
  have heq : ∀ K : ℝ, ∀ N : ℕ,
      2 / (2 * K * Real.log N ^ (1 / 8 : ℝ) / N) =
        (N : ℝ) / (K * Real.log N ^ (1 / 8 : ℝ)) := by
    intro K N
    rw [mul_assoc, div_div_eq_mul_div, mul_div_mul_left _ _ two_ne_zero]
  constructor
  · intro H K hK
    filter_upwards [H K hK, hc K hK, eventually_ge_atTop 1] with N hN hcN h1
    apply (forall_completeWeilEnergy_nonneg_iff contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
      integral_tiltedUnitSpline_ne_zero hcN h1).mpr
    rwa [heq]
  · intro H K hK
    filter_upwards [H K hK, hc K hK, eventually_ge_atTop 1] with N hN hcN h1
    have h := (forall_completeWeilEnergy_nonneg_iff contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
      integral_tiltedUnitSpline_ne_zero hcN h1).mp hN
    rwa [heq] at h

#print axioms riemannHypothesis_iff_tiltedSpline_nonneg_every_eighthRoot_multiple
#print axioms riemannHypothesis_iff_tiltedSpline_pole_nonneg_every_eighthRoot_multiple
#print axioms riemannHypothesis_iff_tiltedSpline_completeWeil_nonneg_every_eighthRoot_multiple

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
