/-
Repurposing the anti-concentration engine to its honest target: a proportion statement.

The Steinhaus small-ball does not produce a pointwise floor for the interfering carrier `gN` (its
on-line zeros are genuine — doc 89). Its correct output is a DENSITY statement about the single
Dirichlet polynomial `|D|`: the floor-failure set `{τ : |D τ| ≤ t₀}` has Cesàro upper density `< 1`
under the caustic geometry, so the complement — `|D|` LARGE — holds at a positive proportion of
heights. This is the legitimate payoff of the small-ball machinery; combined with the sign-change
count of the finite Hardy function it feeds zero-density control (classical strength, not the moonshot).
-/
import GaloisForLFunctions.RHTower.FloorFailureDensity
import GaloisForLFunctions.RHTower.RouteBFullSupportDensity

open Filter Topology MeasureTheory intervalIntegral

namespace RHTower.Weyl

/-- The Cesàro lower time density `liminf_T (1/T)∫₀ᵀ f`. -/
noncomputable def cesaroLowerDensity (f : ℝ → ℝ) : ℝ :=
  Filter.liminf (fun T : ℝ => T⁻¹ * ∫ τ in (0:ℝ)..T, f τ) atTop

/-- **Proportion statement.** For a `[0,1]`-valued observable `fail` with Cesàro upper density `≤ B`,
the complementary success observable `1 − fail` has Cesàro lower density `≥ 1 − B`. When `B < 1` this
is positive: the complement (`|D|` large) holds at a positive proportion of heights. -/
theorem good_proportion_ge (fail : ℝ → ℝ) (hf0 : ∀ τ, 0 ≤ fail τ) (hf1 : ∀ τ, fail τ ≤ 1)
    (hint : ∀ T : ℝ, IntervalIntegrable fail volume 0 T) {B : ℝ}
    (hB : cesaroUpperDensity fail ≤ B) :
    1 - B ≤ cesaroLowerDensity (fun τ => 1 - fail τ) := by
  set g : ℝ → ℝ := fun T : ℝ => T⁻¹ * ∫ τ in (0:ℝ)..T, fail τ with hgdef
  have hgle : ∀ᶠ T in atTop, g T ≤ 1 := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    have hle : (∫ τ in (0:ℝ)..T, fail τ) ≤ ∫ _τ in (0:ℝ)..T, (1:ℝ) := by
      apply intervalIntegral.integral_mono_on hT.le (hint T) intervalIntegral.intervalIntegrable_const
      intro x _; exact hf1 x
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero] at hle
    rw [hgdef]
    calc T⁻¹ * ∫ τ in (0:ℝ)..T, fail τ ≤ T⁻¹ * T := by
            apply mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hT)
  have hgge : ∀ᶠ T in atTop, 0 ≤ g T := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    rw [hgdef]
    apply mul_nonneg (by positivity)
    apply intervalIntegral.integral_nonneg hT.le
    intro x _; exact hf0 x
  have hbdd : IsBoundedUnder (· ≤ ·) atTop g := ⟨1, hgle⟩
  have hcobdd : IsCoboundedUnder (· ≤ ·) atTop g :=
    (show IsBoundedUnder (· ≥ ·) atTop g from ⟨0, hgge⟩).isCoboundedUnder_le
  have heq : ∀ᶠ T in atTop, T⁻¹ * ∫ τ in (0:ℝ)..T, (1 - fail τ)
      = 1 - g T := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_const (hint T),
      intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero, mul_sub,
      inv_mul_cancel₀ (ne_of_gt hT), hgdef]
  rw [cesaroLowerDensity, liminf_congr heq, liminf_const_sub _ g 1 hbdd hcobdd]
  have : cesaroUpperDensity fail = limsup g atTop := by rw [cesaroUpperDensity]
  rw [← this]
  linarith [hB]

open RHTower

/-- **Positive proportion of large-`|D|` heights, from the caustic geometry.** If the explicit
four-phase constant is `< 1`, the complement of the floor-failure set (the heights where the
full-support carrier `dpoly a (Icc 1 N)` exceeds `t₀`) has strictly positive Cesàro lower density.
The anti-concentration engine's honest deliverable. -/
theorem dpoly_large_lower_density_pos {N : ℕ} (a : ℕ → ℝ)
    {t₀ σ0 sstar : ℝ} {J : ℕ} {p1 p2 p3 p4 : ℕ}
    (hp1P : p1.Prime) (hp2P : p2.Prime) (hp3P : p3.Prime) (hp4P : p4.Prime)
    (hp1I : p1 ∈ Finset.Icc 1 N) (hp2I : p2 ∈ Finset.Icc 1 N)
    (hp3I : p3 ∈ Finset.Icc 1 N) (hp4I : p4 ∈ Finset.Icc 1 N)
    (hN1 : N < 2 * p1) (hN2 : N < 2 * p2) (hN3 : N < 2 * p3) (hN4 : N < 2 * p4)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (hA : (a p4 : ℂ) ≠ 0) (hB : (a p3 : ℂ) ≠ 0) (hC : (a p2 : ℂ) ≠ 0) (hD : (a p1 : ℂ) ≠ 0)
    (hρB : ‖(a p3 : ℂ)‖ < ‖(a p4 : ℂ)‖) (hr0 : 0 < t₀)
    (hr2 : 2 * t₀ ≤ ‖(a p4 : ℂ)‖ - ‖(a p3 : ℂ)‖) (hσ0 : 0 < σ0)
    (hσ0G : σ0 ≤ ((‖(a p4 : ℂ)‖ + ‖(a p3 : ℂ)‖) ^ 2 - (‖(a p4 : ℂ)‖ - ‖(a p3 : ℂ)‖) ^ 2) / 3)
    (hJ : ((‖(a p4 : ℂ)‖ + ‖(a p3 : ℂ)‖) ^ 2 - (‖(a p4 : ℂ)‖ - ‖(a p3 : ℂ)‖) ^ 2) / 3 < 2 ^ J * σ0)
    (hHσ0 : 2 * (t₀ * (2 * ‖(a p4 : ℂ)‖ + t₀) / ((‖(a p4 : ℂ)‖ - ‖(a p3 : ℂ)‖) * ‖(a p3 : ℂ)‖))
        ≤ σ0 * Sublevel.causticKappa ‖(a p4 : ℂ)‖ ‖(a p3 : ℂ)‖)
    (hss : 0 < sstar) (hss2 : 2 * sstar ≤ ‖(a p1 : ℂ)‖)
    (fail : ℝ → ℝ) (hfail0 : ∀ τ, 0 ≤ fail τ) (hfle1 : ∀ τ, fail τ ≤ 1)
    (hfsupp : ∀ τ, t₀ < ‖dpoly a (Finset.Icc 1 N) τ‖ → fail τ = 0)
    (hfail_int : ∀ T : ℝ, IntervalIntegrable fail volume 0 T)
    (hnum : (ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4
        * Sublevel.fourPhaseConst (a p4 : ℂ) (a p3 : ℂ) (a p2 : ℂ) (a p1 : ℂ)
            t₀ σ0 sstar J).toReal < 1) :
    0 < cesaroLowerDensity (fun τ => 1 - fail τ) := by
  have hdens := floorFailure_timeDensity_le_caustic_fullSupport a hp1P hp2P hp3P hp4P
    hp1I hp2I hp3I hp4I hN1 hN2 hN3 hN4 h12 h13 h14 h23 h24 h34 hA hB hC hD hρB hr0 hr2 hσ0 hσ0G hJ
    hHσ0 hss hss2 fail hfail0 hfle1 hfsupp hfail_int
  have hprop := good_proportion_ge fail hfail0 hfle1 hfail_int hdens
  linarith [hnum, hprop]


end RHTower.Weyl
