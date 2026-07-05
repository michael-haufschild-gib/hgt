/-
From the floor-failure density to a cofinal a.e.-height floor.

The Cesàro upper time density of the floor-failure indicator being strictly below `1` forces the
floor-holding heights `{τ : ‖F τ‖ > t₀}` to be cofinal: if they were bounded, the indicator would
eventually equal `1` and the density would be `1`. Composed with the concrete caustic small-ball
bound, this turns the explicit four-phase constant `< 1` into the deterministic statement that the
carrier exceeds `t₀` at arbitrarily large heights — the input a window-placement argument consumes.
A carrier zero on the line is itself a failure height (`carrier_line_zero_le`), so the failure set
also bounds the on-line carrier zeros.
-/
import GaloisForLFunctions.RHTower.FloorFailureCaustic

open MeasureTheory intervalIntegral Filter Topology Complex

namespace RHTower

open Weyl SteinhausModel Sublevel

/-- A carrier zero on the critical line is a floor-failure height. -/
theorem carrier_line_zero_le (a : ℕ → ℝ) (s : Finset ℕ) {t₀ τ : ℝ} (ht0 : 0 ≤ t₀)
    (hz : dpoly a s τ = 0) : ‖dpoly a s τ‖ ≤ t₀ := by
  rw [hz, norm_zero]; exact ht0

/-- **A.e.-height floor from the density bound.** If the floor-failure indicator has Cesàro
upper time density strictly below `1`, the floor-holding heights `{τ : ‖F τ‖ > t₀}` are cofinal:
above every bound there is a height where the carrier exceeds `t₀`. If they were bounded, the
failure indicator would eventually equal `1`, forcing density `1`. -/
theorem good_height_cofinal_of_density_lt_one
    (a : ℕ → ℝ) (s : Finset ℕ) (t₀ : ℝ)
    (fail : ℝ → ℝ) (hfail_int : ∀ T : ℝ, IntervalIntegrable fail volume 0 T)
    (hfailfull : ∀ τ, ‖dpoly a s τ‖ ≤ t₀ → fail τ = 1)
    (hdens : cesaroUpperDensity fail < 1) :
    ∀ M : ℝ, ∃ τ, M < τ ∧ t₀ < ‖dpoly a s τ‖ := by
  by_contra hcon
  simp only [not_forall, not_exists, not_and, not_lt] at hcon
  obtain ⟨M, hM⟩ := hcon
  have hfe : ∀ τ, M < τ → fail τ = 1 := fun τ hτ => hfailfull τ (hM τ hτ)
  set M₀ : ℝ := max M 0 + 1 with hM₀def
  have hM₀M : M < M₀ := lt_of_le_of_lt (le_max_left M 0) (lt_add_one _)
  have hM₀0 : (0 : ℝ) < M₀ := lt_of_le_of_lt (le_max_right M 0) (lt_add_one _)
  have htend : Tendsto (fun T : ℝ => T⁻¹ * ∫ τ in (0:ℝ)..T, fail τ) atTop (𝓝 1) := by
    have heq : ∀ᶠ T in atTop, T⁻¹ * ∫ τ in (0:ℝ)..T, fail τ
        = (∫ τ in (0:ℝ)..M₀, fail τ) * T⁻¹ + (1 - M₀ * T⁻¹) := by
      filter_upwards [eventually_gt_atTop M₀] with T hTM
      have hII : IntervalIntegrable fail volume M₀ T :=
        ((hfail_int M₀).symm).trans (hfail_int T)
      have hsplit : (∫ τ in (0:ℝ)..M₀, fail τ) + (∫ τ in M₀..T, fail τ)
          = ∫ τ in (0:ℝ)..T, fail τ :=
        intervalIntegral.integral_add_adjacent_intervals (hfail_int M₀) hII
      have htail : ∫ τ in M₀..T, fail τ = T - M₀ := by
        rw [intervalIntegral.integral_congr (g := fun _ => (1:ℝ)) ?_]
        · rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]
        · intro u hu
          rw [Set.uIcc_of_le (le_of_lt hTM)] at hu
          exact hfe u (lt_of_lt_of_le hM₀M hu.1)
      have hTne : (T : ℝ) ≠ 0 := ne_of_gt (lt_trans hM₀0 hTM)
      rw [← hsplit, htail, mul_add]
      field_simp
    have h1 : Tendsto (fun T : ℝ => (∫ τ in (0:ℝ)..M₀, fail τ) * T⁻¹) atTop (𝓝 0) := by
      have := tendsto_inv_atTop_zero.const_mul (∫ τ in (0:ℝ)..M₀, fail τ)
      simpa using this
    have h2 : Tendsto (fun T : ℝ => 1 - M₀ * T⁻¹) atTop (𝓝 1) := by
      have := (tendsto_inv_atTop_zero.const_mul M₀).const_sub (1 : ℝ)
      simpa using this
    have hsum : Tendsto (fun T : ℝ => (∫ τ in (0:ℝ)..M₀, fail τ) * T⁻¹ + (1 - M₀ * T⁻¹))
        atTop (𝓝 1) := by simpa using h1.add h2
    refine hsum.congr' ?_
    filter_upwards [heq] with T hT
    exact hT.symm
  have hcd : cesaroUpperDensity fail = 1 := htend.limsup_eq
  linarith

/-- **Caustic a.e.-height floor.** Under the caustic geometry, if the explicit four-phase
constant satisfies `((2π)⁻⁴·fourPhaseConst).toReal < 1`, then the carrier's floor holds at
cofinally many heights: above every bound there is a height `τ` with `‖F τ‖ > t₀`. Composes the
concrete caustic density bound with the cofinality bridge — the deterministic input the
movable-shell window placement consumes. -/
theorem good_height_cofinal_of_caustic
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (a : ℕ → ℝ)
    {t₀ σ0 sstar : ℝ} {J : ℕ}
    (p1 p2 p3 p4 : ℕ) (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) (hp3 : p3 ∈ s) (hp4 : p4 ∈ s)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (hA : (a p4 : ℂ) ≠ 0) (hB : (a p3 : ℂ) ≠ 0) (hC : (a p2 : ℂ) ≠ 0) (hD : (a p1 : ℂ) ≠ 0)
    (hρB : ‖(a p3 : ℂ)‖ < ‖(a p4 : ℂ)‖) (hr0 : 0 < t₀)
    (hr2 : 2 * t₀ ≤ ‖(a p4 : ℂ)‖ - ‖(a p3 : ℂ)‖) (hσ0 : 0 < σ0)
    (hσ0G : σ0 ≤ ((‖(a p4 : ℂ)‖ + ‖(a p3 : ℂ)‖) ^ 2 - (‖(a p4 : ℂ)‖ - ‖(a p3 : ℂ)‖) ^ 2) / 3)
    (hJ : ((‖(a p4 : ℂ)‖ + ‖(a p3 : ℂ)‖) ^ 2 - (‖(a p4 : ℂ)‖ - ‖(a p3 : ℂ)‖) ^ 2) / 3
        < 2 ^ J * σ0)
    (hHσ0 : 2 * (t₀ * (2 * ‖(a p4 : ℂ)‖ + t₀)
        / ((‖(a p4 : ℂ)‖ - ‖(a p3 : ℂ)‖) * ‖(a p3 : ℂ)‖))
        ≤ σ0 * causticKappa ‖(a p4 : ℂ)‖ ‖(a p3 : ℂ)‖)
    (hss : 0 < sstar) (hss2 : 2 * sstar ≤ ‖(a p1 : ℂ)‖)
    (fail : ℝ → ℝ) (hfail0 : ∀ τ, 0 ≤ fail τ) (hfle1 : ∀ τ, fail τ ≤ 1)
    (hfsupp : ∀ τ, t₀ < ‖dpoly a s τ‖ → fail τ = 0)
    (hfailfull : ∀ τ, ‖dpoly a s τ‖ ≤ t₀ → fail τ = 1)
    (hfail_int : ∀ T : ℝ, IntervalIntegrable fail volume 0 T)
    (hnum : (ENNReal.ofReal (2 * Real.pi)⁻¹ ^ 4
        * Sublevel.fourPhaseConst (a p4 : ℂ) (a p3 : ℂ) (a p2 : ℂ) (a p1 : ℂ)
            t₀ σ0 sstar J).toReal < 1) :
    ∀ M : ℝ, ∃ τ, M < τ ∧ t₀ < ‖dpoly a s τ‖ :=
  good_height_cofinal_of_density_lt_one a s t₀ fail hfail_int hfailfull
    (lt_of_le_of_lt
      (floorFailure_timeDensity_le_caustic s hs a p1 p2 p3 p4 hp1 hp2 hp3 hp4
        h12 h13 h14 h23 h24 h34 hA hB hC hD hρB hr0 hr2 hσ0 hσ0G hJ hHσ0 hss hss2
        fail hfail0 hfle1 hfsupp hfail_int)
      hnum)

end RHTower
