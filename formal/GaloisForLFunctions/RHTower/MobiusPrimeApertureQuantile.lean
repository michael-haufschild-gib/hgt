import GaloisForLFunctions.RHTower.MobiusPrimeApertureCriticalProfile
import GaloisForLFunctions.RHTower.ExponentialIntegralE1Quantile

/-!
# The retained-fraction quantile and the full-mass criterion

The critical retained mass is monotone in the scaled prime aperture and bounded by one.  Combined
with the exponential-integral profile this gives the quantile cutoff and the exact criterion for
transporting the whole critical Möbius channel: the retained fraction tends to one exactly when
the scaled aperture diverges.
-/

open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace RHTower

noncomputable section

theorem apertureLogSum_nonneg {ω : ℝ} (_hω : 0 < ω) (c : ℝ) : 0 ≤ apertureLogSum c ω := by
  rw [apertureLogSum]
  exact tsum_nonneg (fun n => apertureLogTerm_nonneg c ω n)

theorem criticalRetainedMass_le_one {ω : ℝ} (hω : 0 < ω) (c : ℝ) :
    criticalRetainedMass c ω ≤ 1 := by
  rw [criticalRetainedMass, Real.exp_le_one_iff]
  have := apertureLogSum_nonneg hω c
  linarith

theorem criticalRetainedMass_pos (c ω : ℝ) : 0 < criticalRetainedMass c ω := Real.exp_pos _

theorem criticalCutoff_mono {ω : ℝ} (hω : 0 < ω) {c₁ c₂ : ℝ} (h : c₁ ≤ c₂) :
    criticalCutoff c₁ ω ≤ criticalCutoff c₂ ω := by
  have hωpos : (0 : ℝ) < 2 * ω := by linarith
  rw [criticalCutoff, criticalCutoff]
  refine Real.exp_le_exp.mpr ?_
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h (inv_pos.mpr hωpos).le

theorem apertureLogSum_antitone {ω : ℝ} (hω : 0 < ω) {c₁ c₂ : ℝ} (h : c₁ ≤ c₂) :
    apertureLogSum c₂ ω ≤ apertureLogSum c₁ ω := by
  have hfloor : ⌊criticalCutoff c₁ ω⌋₊ ≤ ⌊criticalCutoff c₂ ω⌋₊ :=
    Nat.floor_mono (criticalCutoff_mono hω h)
  refine (summable_apertureLogTerm hω c₂).tsum_le_tsum (fun n => ?_)
    (summable_apertureLogTerm hω c₁)
  simp only [apertureLogTerm]
  by_cases hcase : ⌊criticalCutoff c₂ ω⌋₊ < n ∧ n.Prime
  · rw [if_pos hcase, if_pos ⟨lt_of_le_of_lt hfloor hcase.1, hcase.2⟩]
  · rw [if_neg hcase]
    split_ifs with h2
    · exact log_one_add_nonneg' (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    · exact le_rfl

theorem criticalRetainedMass_mono {ω : ℝ} (hω : 0 < ω) {c₁ c₂ : ℝ} (h : c₁ ≤ c₂) :
    criticalRetainedMass c₁ ω ≤ criticalRetainedMass c₂ ω := by
  rw [criticalRetainedMass, criticalRetainedMass, Real.exp_le_exp]
  have := apertureLogSum_antitone hω h
  linarith

/-- **Equations (15)--(17): the quantile cutoff.**  For every retained fraction `q ∈ (0,1)` there
is a unique scaled prime aperture `c_q` whose critical cutoff retains asymptotic fraction `q`. -/
theorem exists_criticalCutoff_retaining {q : ℝ} (h0 : 0 < q) (h1 : q < 1) :
    ∃! c : ℝ, 0 < c ∧
      Tendsto (fun ω : ℝ => criticalRetainedMass c ω) (𝓝[>] (0 : ℝ)) (nhds q) := by
  obtain ⟨c, ⟨hc0, hcq⟩, huniq⟩ := existsUnique_retentionQuantile h0 h1
  refine ⟨c, ⟨hc0, ?_⟩, ?_⟩
  · have h := tendsto_criticalRetainedMass hc0
    rwa [show Real.exp (-expIntegralOne c) = q from hcq] at h
  · rintro d ⟨hd0, hdq⟩
    refine huniq d ⟨hd0, ?_⟩
    have h := tendsto_criticalRetainedMass hd0
    exact tendsto_nhds_unique h hdq

/-! ## The full-mass criterion -/

/-- **Equation (18), sufficiency.**  A diverging scaled aperture transports the whole channel. -/
theorem tendsto_criticalRetainedMass_one_of_atTop {C : ℝ → ℝ}
    (hC : Tendsto C (𝓝[>] (0 : ℝ)) atTop) :
    Tendsto (fun ω : ℝ => criticalRetainedMass (C ω) ω) (𝓝[>] (0 : ℝ)) (nhds 1) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨C₀, hC₀q, hC₀pos⟩ : ∃ C₀ : ℝ, a < retentionQuantile C₀ ∧ C₀ ∈ Ioi (0 : ℝ) := by
      have hev : ∀ᶠ x in atTop, a < retentionQuantile x :=
        tendsto_retentionQuantile_atTop (Ioi_mem_nhds ha)
      exact (hev.and (eventually_gt_atTop (0 : ℝ))).exists
    have hlim := tendsto_criticalRetainedMass (mem_Ioi.mp hC₀pos)
    have hev2 : ∀ᶠ ω in 𝓝[>] (0 : ℝ), a < criticalRetainedMass C₀ ω := by
      refine hlim.eventually (Ioi_mem_nhds ?_)
      exact hC₀q
    filter_upwards [hev2, hC.eventually_ge_atTop C₀, self_mem_nhdsWithin] with ω h1 h2 h3
    exact lt_of_lt_of_le h1 (criticalRetainedMass_mono (mem_Ioi.mp h3) h2)
  · filter_upwards [self_mem_nhdsWithin] with ω hω
    exact lt_of_le_of_lt (criticalRetainedMass_le_one (mem_Ioi.mp hω) _) ha

/-- **Equation (18), necessity.**  Full mass transport forces a diverging scaled aperture. -/
theorem tendsto_atTop_of_criticalRetainedMass_one {C : ℝ → ℝ}
    (hmass : Tendsto (fun ω : ℝ => criticalRetainedMass (C ω) ω) (𝓝[>] (0 : ℝ)) (nhds 1)) :
    Tendsto C (𝓝[>] (0 : ℝ)) atTop := by
  refine tendsto_atTop.2 fun b => ?_
  by_contra hcon
  have hfreq : ∃ᶠ ω in 𝓝[>] (0 : ℝ), ¬ (max b 1 ≤ C ω) := by
    intro hev
    refine hcon ?_
    filter_upwards [hev] with ω hω
    exact le_trans (le_max_left b 1) (not_not.mp hω)
  set b' : ℝ := max b 1 with hb'
  have hb'pos : 0 < b' := lt_of_lt_of_le zero_lt_one (le_max_right b 1)
  have hq : retentionQuantile b' < 1 := retentionQuantile_lt_one hb'pos
  obtain ⟨a, haq, ha1⟩ : ∃ a : ℝ, retentionQuantile b' < a ∧ a < 1 :=
    ⟨(retentionQuantile b' + 1) / 2, by linarith, by linarith⟩
  have hlimb := tendsto_criticalRetainedMass hb'pos
  have hevb : ∀ᶠ ω in 𝓝[>] (0 : ℝ), criticalRetainedMass b' ω < a := by
    refine hlimb.eventually (Iio_mem_nhds ?_)
    exact haq
  have heva : ∀ᶠ ω in 𝓝[>] (0 : ℝ), a < criticalRetainedMass (C ω) ω :=
    hmass.eventually (Ioi_mem_nhds ha1)
  have hcontra := (hfreq.and_eventually (hevb.and (heva.and self_mem_nhdsWithin))).exists
  obtain ⟨ω, hnot, hb, ha, hωmem⟩ := hcontra
  have hCle : C ω ≤ b' := (not_le.mp hnot).le
  have := criticalRetainedMass_mono (mem_Ioi.mp hωmem) hCle
  linarith

end

end RHTower
