import GaloisForLFunctions.BiScaleUncertainty.ShortSupportEnergyInjection
import GaloisForLFunctions.BiScaleUncertainty.InfiniteGridOriginConcentration

/-!
# Strict energy loss for smooth signed sources, with infinite-grid witnesses

All sources lie in one interval shorter than the first logarithmic grid gap.
Their normalized correlations converge uniformly to an actual smooth source, while
their energies retain a fixed positive excess. A subsequence realizes a strictly
positive limiting defect, concentrated at zero as classified by the preceding package.
The unrestricted signed-source conclusion forgets the constructed grid zeros;
blindness is a verified sharpness property, not a premise for a general coercivity claim.
-/

open MeasureTheory Set Filter Topology
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-- Uniform correlation convergence can lose energy even with a common short source support. -/
theorem exists_smooth_infiniteGrid_strict_energy_loss :
    ∃ (K d B : ℝ) (f : InfiniteGridEnergySource K) (g : ℕ → InfiniteGridEnergySource K),
      0 ≤ K ∧ 0 < d ∧ 0 < B ∧ 2 * B < Real.log 2 ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) (f.source : ℝ → ℝ) ∧
      (∀ n, ContDiff ℝ (↑(⊤ : ℕ∞)) ((g n).source : ℝ → ℝ)) ∧
      (∀ u, B < |u| → f.source u = 0) ∧
      (∀ n u, B < |u| → (g n).source u = 0) ∧
      Tendsto (fun n => ∫ u, ((g n).source u - f.source u) ^ 2) atTop (𝓝 0) ∧
      TendstoUniformly (fun n => (g n).correlation) f.correlation atTop ∧
      ∀ n, normalizedArchEnergy f.source + d ≤ normalizedArchEnergy (g n).source := by
  classical
  let b : ℝ := Real.log 2 / 16
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hb : 0 < b := div_pos hlog (by norm_num)
  have hB : 2 * (5 * b) < Real.log 2 := by dsimp [b]; linarith
  obtain ⟨f, hf, hfc, hR, hs⟩ := exists_smooth_source_in_radius hb
  have hA := biScaleLevyEnergy_nonneg hfc hf.continuous
  let K := 2 * (biScaleLevyEnergy f + 1) / autocorr f 0
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have htwo : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) :=
    WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  have hnode : ∀ n : ℕ, 2 ≤ n → 2 * (5 * b) < |Real.log (n : ℝ)| := by
    intro n hn
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ n by exact_mod_cast hn)
    exact (hB.trans_le hl).trans_le (le_abs_self _)
  let F : InfiniteGridEnergySource K :=
    { source := ⟨⟨f, hf.continuous⟩, hfc⟩
      smooth := hf.of_le htwo
      mass_pos := hR
      energy_le := by
        change biScaleLevyEnergy f / autocorr f 0 ≤ K
        exact div_le_div_of_nonneg_right (by linarith) hR.le
      grid_zero := by
        intro n hn
        apply autocorr_eq_zero_of_source_radius hs
        linarith [hnode n hn] }
  have htpos (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have htle (n : ℕ) : 1 / ((n : ℝ) + 1) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
    have hn : 0 ≤ (n : ℝ) := by positivity
    linarith
  have hex (n : ℕ) := exists_short_support_energy_injection hf hfc hR hb hs (htpos n) (htle n)
  choose g hg hgc hgR hgs hgE hgap hL2 hnear using hex
  let G : ℕ → InfiniteGridEnergySource K := fun n =>
    { source := ⟨⟨g n, (hg n).continuous⟩, hgc n⟩
      smooth := (hg n).of_le htwo
      mass_pos := hgR n
      energy_le := hgE n
      grid_zero := fun k hk => autocorr_eq_zero_of_source_radius (hgs n) (hnode k hk) }
  refine ⟨K, 1 / (2 * autocorr f 0), 5 * b, F, G, hK, by positivity,
    by positivity, hB, hf, hg, ?_, hgs, ?_, ?_, hgap⟩
  · intro u hu
    exact hs u (by linarith)
  · apply squeeze_zero (fun n => integral_nonneg (fun u => sq_nonneg _)) hL2
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
  · have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) *
        (autocorr f 0 + 3) / autocorr f 0) atTop (𝓝 0) := by
      simpa only [mul_div_assoc, zero_mul, zero_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const
          ((autocorr f 0 + 3) / autocorr f 0)
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [(tendsto_order.mp ht).2 ε hε] with n hn x
    change dist (autocorr f x / autocorr f 0) (autocorr (g n) x / autocorr (g n) 0) < ε
    rw [Real.dist_eq, abs_sub_comm]
    exact (hnear n x).trans_lt hn

/-- General signed smooth sources need origin-energy control even under strong source
convergence, uniform correlation convergence, bounded energy and common support. -/
theorem exists_smooth_source_strict_energy_loss :
    ∃ (K d B : ℝ) (f : C_c(ℝ, ℝ)) (g : ℕ → C_c(ℝ, ℝ)),
      0 ≤ K ∧ 0 < d ∧ 0 < B ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) (f : ℝ → ℝ) ∧
      (∀ n, ContDiff ℝ (↑(⊤ : ℕ∞)) (g n : ℝ → ℝ)) ∧
      0 < autocorr f 0 ∧ (∀ n, 0 < autocorr (g n) 0) ∧
      normalizedArchEnergy f ≤ K ∧ (∀ n, normalizedArchEnergy (g n) ≤ K) ∧
      (∀ u, B < |u| → f u = 0) ∧ (∀ n u, B < |u| → g n u = 0) ∧
      Tendsto (fun n => ∫ u, (g n u - f u) ^ 2) atTop (𝓝 0) ∧
      TendstoUniformly (fun n x => autocorr (g n) x / autocorr (g n) 0)
        (fun x => autocorr f x / autocorr f 0) atTop ∧
      ∀ n, normalizedArchEnergy f + d ≤ normalizedArchEnergy (g n) := by
  obtain ⟨K, d, B, f, g, hK, hd, hB, _, hf, hg, hs, hgs, hL2, hu, hgap⟩ :=
    exists_smooth_infiniteGrid_strict_energy_loss
  exact ⟨K, d, B, f.source, fun n => (g n).source, hK, hd, hB, hf, hg,
    f.mass_pos, fun n => (g n).mass_pos, f.energy_le, fun n => (g n).energy_le,
    hs, hgs, hL2, hu, hgap⟩

/-- An actual smooth limit has a strictly positive defect in every fixed origin interval. -/
theorem exists_smooth_infiniteGrid_positive_origin_defect :
    ∃ (K D : ℝ) (f : InfiniteGridEnergySource K) (g : ℕ → InfiniteGridEnergySource K),
      0 ≤ K ∧ 0 < D ∧
      ContDiff ℝ (↑(⊤ : ℕ∞)) (f.source : ℝ → ℝ) ∧
      (∀ n, ContDiff ℝ (↑(⊤ : ℕ∞)) ((g n).source : ℝ → ℝ)) ∧
      TendstoUniformly (fun n => (g n).correlation) f.correlation atTop ∧
      Tendsto (fun n => normalizedArchEnergy (g n).source) atTop
        (𝓝 (normalizedArchEnergy f.source + D)) ∧
      ∀ a : ℝ, 0 < a → Tendsto (fun n => correlationOriginEnergy (g n).correlation a)
        atTop (𝓝 (D + correlationOriginEnergy f.correlation a)) := by
  obtain ⟨K, d, B, f, g, hK, hd, _, _, hf, hg, _, _, _, hu, hgap⟩ :=
    exists_smooth_infiniteGrid_strict_energy_loss
  have hb : ∀ n : ℕ, normalizedArchEnergy (g n).source ∈ Icc 0 K := by
    intro n
    refine ⟨?_, (g n).energy_le⟩
    exact div_nonneg (biScaleLevyEnergy_nonneg (g n).source.hasCompactSupport (g n).source.continuous)
      (g n).mass_pos.le
  obtain ⟨L, _, φ, hφ, he⟩ := isCompact_Icc.tendsto_subseq hb
  have hu' : TendstoUniformly (fun n => (g (φ n)).correlation) f.correlation atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    exact hφ.tendsto_atTop.eventually (Metric.tendstoUniformly_iff.mp hu ε hε)
  have hlow : normalizedArchEnergy f.source + d ≤ L := by
    have hn := le_of_tendsto' he.neg (fun n => neg_le_neg (hgap (φ n)))
    linarith
  have hc := (infiniteGrid_origin_energy_defect hK (fun n => g (φ n)) hu' he).2
  rw [f.integral_correlationLevyIntegrand] at hc
  refine ⟨K, L - normalizedArchEnergy f.source, f, fun n => g (φ n), hK,
    by linarith, hf, fun n => hg (φ n), hu', ?_, hc⟩
  simpa only [Function.comp_def,
    show normalizedArchEnergy f.source + (L - normalizedArchEnergy f.source) = L by ring]
    using he

end

end GaloisForLFunctions.BiScaleUncertainty
