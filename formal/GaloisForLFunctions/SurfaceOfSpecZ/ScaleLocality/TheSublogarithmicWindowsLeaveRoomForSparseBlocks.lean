import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.TheReflectedCalibratedBlocksHavePositiveWindows

/-!
# Arbitrarily late sparse calibrated blocks

A sublogarithmic window has left endpoint tending to infinity. The
normalized node mass and local density vanish, while every fixed positive
depth gap supplies unbounded exponential gain. These limits allow each
new calibrated block to satisfy the preceding blocks' tail constraints.
-/

open Complex Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- The left endpoints of sublogarithmic windows tend to infinity. -/
theorem tendsto_sublogarithmic_window_left {R : ℝ → ℝ}
    (hR : Tendsto (fun T => R T / Real.log T) atTop (𝓝 0)) :
    Tendsto (fun T => T - R T) atTop atTop := by
  have hlog := RHTower.eventually_const_mul_rpow_neg_mul_log_pow_le
    1 1 (by norm_num) 1 (by norm_num : (0 : ℝ) < 1 / 2)
  apply Filter.tendsto_atTop.2
  intro A
  filter_upwards [eventually_sublogarithmic_grid_parameters hR (by norm_num : (0 : ℝ) < 1),
    hlog, eventually_ge_atTop (2 * A)] with T hT hLT hTA
  have hh : Real.log T / T ≤ 1 / 2 := by
    simpa only [one_mul, pow_one, Real.rpow_neg_one, div_eq_mul_inv, mul_comm] using hLT
  have hlogT := (div_le_iff₀ hT.1).mp hh
  linarith only [hT.2.2.2.2.2.2.1, hlogT, hTA]

/-- Both normalized mass and the allowed fraction of local density become arbitrarily small. -/
theorem eventually_calibrated_grid_mass_and_count {R : ℝ → ℝ}
    (hR0 : ∀ T, 0 ≤ R T)
    (hR : Tendsto (fun T => R T / Real.log T) atTop (𝓝 0))
    {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop,
      let Γ := calibratedGridFrequency T
      let k := calibratedGridDegree Γ (R T)
      4 ≤ Γ ∧ 0 < k ∧
        4 * (1 + (k : ℝ) / Γ) ≤ C * Real.log Γ ∧
        16 * (k : ℝ) / Γ ^ 2 ≤ ε ∧
        524288 * Real.exp 4 * (k : ℝ) / Γ ^ 2 ≤ ε := by
  have hΓtop : Tendsto calibratedGridFrequency atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  have hLtop : Tendsto (fun T => Real.log (calibratedGridFrequency T)) atTop atTop :=
    Real.tendsto_log_atTop.comp hΓtop
  have hinv : Tendsto (fun T => (Real.log (calibratedGridFrequency T))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hLtop
  have hden := tendsto_sublogarithmic_grid_logarithmic_density hR0 hR
  have hd : Tendsto (fun T => 4 * ((Real.log (calibratedGridFrequency T))⁻¹ +
      (calibratedGridDegree (calibratedGridFrequency T) (R T) : ℝ) /
        (calibratedGridFrequency T * Real.log (calibratedGridFrequency T)))) atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero] using (hinv.add hden).const_mul 4
  have hm := tendsto_sublogarithmic_grid_quadratic_mass hR0 hR
  have hm16 : Tendsto (fun T => 16 *
      ((calibratedGridDegree (calibratedGridFrequency T) (R T) : ℝ) /
        calibratedGridFrequency T ^ 2)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hm.const_mul 16
  have hmw : Tendsto (fun T => (524288 * Real.exp 4) *
      ((calibratedGridDegree (calibratedGridFrequency T) (R T) : ℝ) /
        calibratedGridFrequency T ^ 2)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hm.const_mul (524288 * Real.exp 4)
  filter_upwards [hΓtop.eventually_ge_atTop 4, hLtop.eventually_ge_atTop 1,
    hd.eventually_le_const hC, hm16.eventually_le_const hε, hmw.eventually_le_const hε,
    eventually_sublogarithmic_grid_parameters hR (by norm_num : (0 : ℝ) < 1)]
    with T hΓ4 hL1 hdi hmi hwi hT
  let Γ := calibratedGridFrequency T
  let k := calibratedGridDegree Γ (R T)
  have hΓ : 0 < Γ := by linarith only [hΓ4]
  have hL : 0 < Real.log Γ := zero_lt_one.trans_le hL1
  have hbounds := growing_calibrated_grid_bounds hT.2.1 hT.2.2.1 hT.2.2.2.1
    hT.2.2.2.2.1 hT.2.2.2.2.2.1 (hR0 T) hT.2.2.2.2.2.2.1 hT.2.2.2.2.2.2.2
  refine ⟨hΓ4, hbounds.1, ?_, ?_, ?_⟩
  · have he : 4 * (1 + (k : ℝ) / Γ) / Real.log Γ =
        4 * ((Real.log Γ)⁻¹ + (k : ℝ) / (Γ * Real.log Γ)) := by
      field_simp [hΓ.ne', hL.ne'] <;> ring
    apply (div_le_iff₀ hL).mp
    rwa [he]
  · simpa only [mul_div_assoc] using hmi
  · simpa only [mul_div_assoc] using hwi

/-- A calibrated block can be chosen beyond arbitrary ordinate and window bounds, with any small mass
and any prescribed gain from a fixed positive depth gap. -/
theorem exists_sparse_calibrated_block {R : ℝ → ℝ} (hR0 : ∀ T, 0 ≤ R T)
    (hR : Tendsto (fun T => R T / Real.log T) atTop (𝓝 0))
    {C ε η d : ℝ} (hC : 0 < C) (hε : 0 < ε) (hη : 0 < η) (hd : 0 < d)
    (H P M x : ℝ) :
    ∃ T : ℝ,
      let Γ := calibratedGridFrequency T
      let k := calibratedGridDegree Γ (R T)
      H ≤ Γ ∧ P ≤ T - R T ∧ 4 ≤ Γ ∧ 0 < k ∧
      4 * (1 + (k : ℝ) / Γ) ≤ C * Real.log Γ ∧
      16 * (k : ℝ) / Γ ^ 2 ≤ ε ∧
      524288 * Real.exp 4 * (k : ℝ) / Γ ^ 2 ≤ ε ∧
      M ≤ (3 / 2 : ℝ) * Real.exp (d * (T - R T) - 8 * x) ∧
      ∃ z : Fin (k + 1) → ℂ,
        (∀ i, |(z i).re| ≤ η ∧ Γ / 2 ≤ (z i).im ∧ (z i).im ≤ 4 * Γ ∧ ‖z i‖ ≤ 4 * Γ) ∧
        (∀ i j, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * (Γ / k) ≤ |(z i).im - (z j).im|) ∧
        ∀ v : ℝ, |v| ≤ R T + 8 →
          (3 / 4 : ℝ) ≤ (∑ i, Complex.exp (((T + v : ℝ) : ℂ) * z i)).re := by
  have hΓtop : Tendsto calibratedGridFrequency atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  have hleft := tendsto_sublogarithmic_window_left hR
  have hexp : Tendsto (fun T => (3 / 2 : ℝ) * Real.exp (d * (T - R T) - 8 * x))
      atTop atTop :=
    (Real.tendsto_exp_atTop.comp ((hleft.const_mul_atTop hd).sub_const (8 * x))).const_mul_atTop
      (by norm_num)
  have hevent : ∀ᶠ T : ℝ in atTop,
      H ≤ calibratedGridFrequency T ∧ P ≤ T - R T ∧
      M ≤ (3 / 2 : ℝ) * Real.exp (d * (T - R T) - 8 * x) ∧
      (let Γ := calibratedGridFrequency T
       let k := calibratedGridDegree Γ (R T)
       4 ≤ Γ ∧ 0 < k ∧ 4 * (1 + (k : ℝ) / Γ) ≤ C * Real.log Γ ∧
        16 * (k : ℝ) / Γ ^ 2 ≤ ε ∧ 524288 * Real.exp 4 * (k : ℝ) / Γ ^ 2 ≤ ε) ∧
      (let Γ := calibratedGridFrequency T
       let k := calibratedGridDegree Γ (R T)
       ∃ z : Fin (k + 1) → ℂ,
        Function.Injective z ∧
        (∀ i, |(z i).re| ≤ η ∧ Γ / 2 ≤ (z i).im ∧ (z i).im ≤ 4 * Γ ∧ ‖z i‖ ≤ 4 * Γ) ∧
        (∀ i j, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * (Γ / k) ≤ |(z i).im - (z j).im|) ∧
        ∀ v : ℝ, |v| ≤ R T + 8 →
          (3 / 4 : ℝ) ≤ (∑ i, Complex.exp (((T + v : ℝ) : ℂ) * z i)).re) := by
    filter_upwards [hΓtop.eventually_ge_atTop H, hleft.eventually_ge_atTop P,
      hexp.eventually_ge_atTop M, eventually_calibrated_grid_mass_and_count hR0 hR hC hε,
      eventually_exists_sublogarithmic_calibrated_grid hR0 hR hη]
      with T hH hP hM hm hz
    exact ⟨hH, hP, hM, hm, hz⟩
  obtain ⟨T, hH, hP, hM, hm, z, _, hz, hsep, hpos⟩ := hevent.exists
  exact ⟨T, hH, hP, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2,
    hM, z, hz, hsep, hpos⟩

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
