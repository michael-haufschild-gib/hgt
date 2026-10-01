import GaloisForLFunctions.RHTower.PMPowerDampedMobiusGramDiagonal

/-! The literal power-damped sources force a unit limiting canonical norm budget.
The Fermi seed has smaller norm, excluding any local seed-norm ceiling.
These lower bounds do not establish source admission for small positive damping. -/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace RHTower


/-- The physical Haar target has exactly unit canonical norm on its carrier. -/
theorem pm_eLpNorm_dyadicHaar :
    eLpNorm dyadicHaar 2 (volume.restrict (Ioc (0 : ℝ) 1)) = 1 := by
  have heq : eLpNorm dyadicHaar 2 (volume.restrict (Ioc (0 : ℝ) 1)) =
      eLpNorm (fun _ : ℝ => (1 : ℂ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
    apply eLpNorm_congr_norm_ae
    exact Eventually.of_forall fun t => by rw [norm_dyadicHaar]; simp
  rw [heq, eLpNorm_const' (1 : ℂ) (by norm_num : (2 : ENNReal) ≠ 0)
    (by norm_num : (2 : ENNReal) ≠ ⊤)]
  simp

/-- Fatou supplies a sharp unit lower floor along every parameter sequence approaching zero. -/
theorem pmPowerDampedFermiSource_liminf_norm_floor {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) :
    1 ≤ atTop.liminf (fun n => eLpNorm (pmPowerDampedFermiSource (ε n)) 2
      (volume.restrict (Ioc (0 : ℝ) 1))) := by
  rw [← pm_eLpNorm_dyadicHaar]
  apply Lp.eLpNorm_lim_le_liminf_eLpNorm
    (fun n => (measurable_pmPowerDampedFermiSource (ε n)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [← pmPowerDampedFermiSource_zero_eq_haar ht]
  exact ((continuous_pmPowerDampedFermiSource_parameter t).tendsto 0).comp hε

/-- Any eventual uniform full canonical norm budget near zero is at least one. -/
theorem pmPowerDampedFermiSource_norm_budget_floor
    {ι : Type*} {u : Filter ι} [NeBot u] [IsCountablyGenerated u]
    {ε : ι → ℝ} (hε : Tendsto ε u (𝓝 0)) {C : ENNReal}
    (hbound : ∀ᶠ n in u, eLpNorm (pmPowerDampedFermiSource (ε n)) 2
      (volume.restrict (Ioi (0 : ℝ))) ≤ C) : 1 ≤ C := by
  have hsmall : ∀ᶠ n in u, eLpNorm (pmPowerDampedFermiSource (ε n)) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) ≤ C := by
    filter_upwards [hbound] with n hn
    exact (eLpNorm_mono_measure _ (Measure.restrict_mono
      (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from fun _ ht => ht.1) le_rfl)).trans hn
  have hlim : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1),
      Tendsto (fun n => pmPowerDampedFermiSource (ε n) t) u (𝓝 (dyadicHaar t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [← pmPowerDampedFermiSource_zero_eq_haar ht]
    exact ((continuous_pmPowerDampedFermiSource_parameter t).tendsto 0).comp hε
  have h := Lp.eLpNorm_le_of_ae_tendsto hsmall
    (fun n => (measurable_pmPowerDampedFermiSource (ε n)).aestronglyMeasurable) hlim
  rwa [pm_eLpNorm_dyadicHaar] at h

/-- No subunit canonical norm budget can hold throughout any positive parameter neighborhood. -/
theorem pmPowerDampedFermiSource_no_subunit_neighborhood {C : ENNReal} (hC : C < 1) :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      eLpNorm (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) ≤ C := by
  rintro ⟨δ, hδ, hb⟩
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      eLpNorm (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) ≤ C := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    exact hb ε hε.1 hε.2
  have h := pmPowerDampedFermiSource_norm_budget_floor
    (ε := fun ε : ℝ => ε) (u := 𝓝[>] (0 : ℝ)) nhdsWithin_le_nhds hbound
  exact not_le_of_gt hC h

/-- The seed generator's norm lies strictly below the forced limiting budget. -/
theorem pm_fermi_seed_norm_lt_one :
    eLpNorm (fermiNymanGen 1) 2 (volume.restrict (Ioi (0 : ℝ))) < 1 := by
  have hf := memLp_pm_fermiNymanGen (by norm_num : (0 : ℝ) < 1)
  have hn : ‖hf.toLp (fermiNymanGen 1)‖ ^ 2 = Real.log 2 := by
    rw [← pm_integral_norm_sq_toLp hf, pm_integral_normSq_fermiNymanGen_one]
  have hlog : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
    norm_num at h
    exact h
  have hnorm : ‖hf.toLp (fermiNymanGen 1)‖ < 1 := by nlinarith [norm_nonneg (hf.toLp (fermiNymanGen 1))]
  rw [← ofReal_lpNorm hf, ← toReal_eLpNorm hf.aestronglyMeasurable, ← Lp.norm_toLp]
  simpa only [ENNReal.ofReal_one] using (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr hnorm

/-- Even a local source ceiling at the undamped seed norm is impossible. -/
theorem pmPowerDampedFermiSource_no_seed_norm_neighborhood :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      eLpNorm (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi (0 : ℝ))) ≤
        eLpNorm (fermiNymanGen 1) 2 (volume.restrict (Ioi (0 : ℝ))) :=
  pmPowerDampedFermiSource_no_subunit_neighborhood pm_fermi_seed_norm_lt_one

end RHTower
