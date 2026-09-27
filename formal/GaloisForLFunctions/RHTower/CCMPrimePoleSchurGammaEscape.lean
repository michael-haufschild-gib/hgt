import GaloisForLFunctions.RHTower.CCMPrimePoleSchurConstrainedEscape

/-!
# Gamma energy detects the constrained prime-edge escape

The exact constrained sequence defeating a prime-edge gap has unbounded form
energy. Compactness of the actual Gamma embedding forces this conclusion from
its nonzero limiting physical norm and weak escape. The complete signed source
then tends to positive infinity, with its entire bounded remainder retained.
-/

open Complex MeasureTheory Set Filter
open scoped InnerProduct Topology
noncomputable section
namespace RHTower

private theorem form_norm_escape (a : SuzukiPositiveAperture)
    (u : ℕ → CCMArchimedeanFormDomain a) (c : ℝ) (hc : 0 < c)
    (hnorm : Tendsto (fun n => ‖ccmArchimedeanFormToAperture a (u n)‖) atTop (𝓝 c))
    (hweak : ∀ g : suzukiApertureHilbert a,
      Tendsto (fun n => inner ℂ g (ccmArchimedeanFormToAperture a (u n))) atTop (𝓝 0)) :
    Tendsto (fun n => ‖u n‖) atTop atTop := by
  let J := ccmArchimedeanFormToAperture a
  refine tendsto_atTop.2 fun b => ?_
  by_contra hb
  rw [Filter.not_eventually] at hb
  have hK := (isCompactOperator_ccmArchimedeanFormToAperture a).isCompact_closure_image_closedBall b
  have hfreq : ∃ᶠ n in atTop,
      J (u n) ∈ closure (J '' Metric.closedBall (0 : CCMArchimedeanFormDomain a) b) := by
    apply hb.mono
    intro n hn
    apply subset_closure
    refine ⟨u n, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (lt_of_not_ge hn).le
  obtain ⟨g, _, φ, hφ, hconv⟩ := hK.isSeqCompact.subseq_of_frequently_in hfreq
  have hg : inner ℂ g g = 0 := by
    have h1 := ((innerSL ℂ g).continuous.tendsto g).comp hconv
    have h2 := (hweak g).comp hφ.tendsto_atTop
    exact tendsto_nhds_unique h1 h2
  have hgzero : g = 0 := inner_self_eq_zero.mp hg
  have hzero : Tendsto (fun n => ‖J (u (φ n))‖) atTop (𝓝 0) := by
    have hn : Tendsto (fun n => ‖J (u (φ n))‖) atTop (𝓝 ‖g‖) :=
      ((show Continuous (fun f : suzukiApertureHilbert a => ‖f‖) from
        continuous_norm).tendsto g).comp hconv
    simpa only [hgzero, norm_zero] using hn
  have heq : c = 0 := tendsto_nhds_unique (hnorm.comp hφ.tendsto_atTop) hzero
  linarith

private theorem source_escape (a : SuzukiPositiveAperture)
    (u : ℕ → CCMArchimedeanFormDomain a) (c : ℝ) (hc : 0 < c)
    (hnorm : Tendsto (fun n => ‖ccmArchimedeanFormToAperture a (u n)‖) atTop (𝓝 c))
    (hform : Tendsto (fun n => ‖u n‖) atTop atTop) :
    Tendsto (fun n => ccmRestrictedWeilSourceQuadratic a (u n)) atTop atTop := by
  let B := ‖ccmRestrictedWeilBoundedRemainder a‖ * (c+1)^2
  have hmass : ∀ᶠ n in atTop, ‖ccmArchimedeanFormToAperture a (u n)‖ ≤ c+1 :=
    hnorm.eventually_le_const (by linarith)
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [hmass, hform.eventually_ge_atTop (max 1 (b+B))] with n hn hu
  have hu1 : 1 ≤ ‖u n‖ := (le_max_left _ _).trans hu
  have hub : b+B ≤ ‖u n‖ := (le_max_right _ _).trans hu
  have hsq : ‖ccmArchimedeanFormToAperture a (u n)‖ ^ 2 ≤ (c+1)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (by linarith)).mpr hn
  have hB := mul_le_mul_of_nonneg_left hsq (norm_nonneg (ccmRestrictedWeilBoundedRemainder a))
  have hsource := ccmArchimedeanFormNorm_sq_le_source_add_remainder_norm_mass a (u n)
  change ‖u n‖ ^ 2 ≤ _ at hsource
  change _ ≤ B at hB
  nlinarith

/-- The actual graph-gap countersequence is paid for by Gamma: its complete
signed source tends to positive infinity, rather than producing a negative witness. -/
theorem exists_ccmPolarConstrained_schurEdge_zero_source_positive_escape
    (a : SuzukiPositiveAperture) :
    ∃ u : ℕ → CCMArchimedeanFormDomain a,
      (∀ n, IsPolarConstrained a (u n)) ∧
      Tendsto (fun n => ‖ccmArchimedeanFormToAperture a (u n)‖)
        atTop (𝓝 ‖ccmSchurPoleVector a‖) ∧
      Tendsto (fun n => ccmPrimePoleSchurEnergy a
        (ccmArchimedeanFormToAperture a (u n)).1) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖u n‖) atTop atTop ∧
      Tendsto (fun n => ccmRestrictedWeilSourceQuadratic a (u n)) atTop atTop := by
  obtain ⟨u,hu,hnorm,hweak,he⟩ := exists_ccmPolarConstrained_schurEdge_nullSequence a
  have hc : 0 < ‖ccmSchurPoleVector a‖ := norm_pos_iff.mpr (ccmSchurPoleVector_ne_zero a)
  have hf := form_norm_escape a u _ hc hnorm hweak
  exact ⟨u,hu,hnorm,he,hf,source_escape a u _ hc hnorm hf⟩

end RHTower
