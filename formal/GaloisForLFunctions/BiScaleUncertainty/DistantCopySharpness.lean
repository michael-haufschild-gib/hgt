import GaloisForLFunctions.BiScaleUncertainty.DistantCopyCompactness
import GaloisForLFunctions.BiScaleUncertainty.DistantCopyPolarTopology

/-!
# Smooth witnesses separating grid, energy and polar topologies

Unit-amplitude copies have eventually zero samples at each fixed logarithmic node
and convergent energy, but no compact correlation closure. Polar-attenuated copies
have compact correlation closure and convergent energy while their polar limit
has a strictly positive moment.
-/

open MeasureTheory Set Filter Topology
open scoped CompactlySupported BoundedContinuousFunction
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def escapingCopyCenter (D : ℝ) (n : ℕ) : ℝ := D + 2 + n

theorem escapingCopyCenter_separated (D : ℝ) (n : ℕ) : D + 1 ≤ escapingCopyCenter D n := by
  have hn : 0 ≤ (n : ℝ) := by positivity
  unfold escapingCopyCenter
  linarith

theorem tendsto_escapingCopyCenter (D : ℝ) : Tendsto (escapingCopyCenter D) atTop atTop := by
  change Tendsto (fun n : ℕ => D + 2 + (n : ℝ)) atTop atTop
  convert
    tendsto_atTop_add_const_right atTop (D + 2) (tendsto_natCast_atTop_atTop (R := ℝ))
    using 1
  funext n
  exact add_comm _ _

theorem tendsto_polarCopy_mixing_zero (T : ℕ → ℝ) (hT : Tendsto T atTop atTop) :
    Tendsto (fun n => copyMixingCoefficient (Real.exp (-T n / 2))) atTop (𝓝 0) := by
  have hz : Tendsto (fun n => -T n / 2) atTop atBot := by
    apply tendsto_atBot.mpr
    intro b
    filter_upwards [hT.eventually (eventually_ge_atTop (-2 * b))] with n hn
    linarith
  have he : Tendsto (fun n => Real.exp (-T n / 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using Real.tendsto_exp_atBot.comp hz
  have hd : Tendsto (fun n => 1 + Real.exp (-T n / 2) ^ 2) atTop (𝓝 1) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using
      tendsto_const_nhds.add (he.pow 2)
  have hq := he.div hd one_ne_zero
  change Tendsto (fun n => Real.exp (-T n / 2) / (1 + Real.exp (-T n / 2) ^ 2))
    atTop (𝓝 ((0 : ℝ) / 1)) at hq
  simpa only [copyMixingCoefficient, zero_div] using hq

private theorem exists_short_positive_polar_seed :
    ∃ (f : C_c(ℝ, ℝ)) (D : ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) (f : ℝ → ℝ) ∧
      0 < autocorr f 0 ∧ 0 < normalizedPolarMoment f ∧ 0 < D ∧ D < Real.log 2 ∧
      ∀ x, D < |x| → autocorr f x = 0 := by
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  obtain ⟨p, hp, hpc, hR, hP, hs⟩ :=
    exists_smooth_source_positive_polar_moment (show 0 < Real.log (2 : ℝ) / 4 by positivity)
  refine ⟨⟨⟨p, hp.continuous⟩, hpc⟩, 2 * (Real.log 2 / 4), hp, hR, hP,
    by positivity, by linarith, ?_⟩
  intro x hx
  exact autocorr_eq_zero_of_source_radius hs hx

/-- Eventual blindness at each fixed node and convergent energy do not imply compactness. -/
theorem exists_smooth_pointwise_grid_blind_noncompact :
    ∃ (K : ℝ) (f : LevyEnergySource K) (g : ℕ → LevyEnergySource K),
      0 ≤ K ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) (f.source : ℝ → ℝ) ∧
      (∀ n, ContDiff ℝ (↑(⊤ : ℕ∞)) ((g n).source : ℝ → ℝ)) ∧
      (∀ m : ℕ, 2 ≤ m → f.correlation (Real.log (m : ℝ)) = 0) ∧
      (∀ m : ℕ, 2 ≤ m → ∀ᶠ n in atTop, (g n).correlation (Real.log (m : ℝ)) = 0) ∧
      Tendsto (fun n => normalizedArchEnergy (g n).source) atTop
        (𝓝 (normalizedArchEnergy f.source)) ∧
      ¬ IsCompact (closure (LevyEnergySource.complexCorrelation '' range g)) := by
  obtain ⟨f, D, hf, hR, _, hD, hDlog, hs⟩ := exists_short_positive_polar_seed
  have htwo : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) :=
    WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  have hf2 := hf.of_le htwo
  let F := levyCopySeed f hf2 hR D
  let G := fun n => levyDistantCopy f hf2 hR hs (escapingCopyCenter_separated D n) 1
  have hgrid (m : ℕ) (hm : 2 ≤ m) : normalizedSourceCorrelation f (Real.log (m : ℝ)) = 0 := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ m by exact_mod_cast hm)
    have hz := hs (Real.log (m : ℝ)) ((hDlog.trans_le hl).trans_le (le_abs_self _))
    simp only [normalizedSourceCorrelation, hz, zero_div]
  refine ⟨copyEnergyCeiling f D, F, G, copyEnergyCeiling_nonneg f.continuous f.hasCompactSupport hR D,
    hf, fun n => contDiff_subtractCopy hf 1 (escapingCopyCenter D n), hgrid, ?_, ?_, ?_⟩
  · intro m hm
    have he := eventually_subtractCopy_correlation_eq_on_window (f := (f : ℝ → ℝ))
      f.continuous f.hasCompactSupport hs
      (fun _ => 1) (escapingCopyCenter D) (tendsto_escapingCopyCenter D) (abs_nonneg (Real.log (m : ℝ)))
    filter_upwards [he] with n hn
    change normalizedSourceCorrelation (subtractCopy f 1 (escapingCopyCenter D n)) (Real.log (m : ℝ)) = 0
    rw [hn _ le_rfl, hgrid m hm]
  · exact tendsto_normalizedArchEnergy_subtractCopy hf2 f.hasCompactSupport hR hs
      (fun _ => 1) (escapingCopyCenter D) (escapingCopyCenter_separated D) (tendsto_escapingCopyCenter D)
  · intro hc
    have hb := (isCompact_closure_distantCopies_iff f hf2 hR hD hs (fun _ => 1)
      (escapingCopyCenter D) (escapingCopyCenter_separated D) (tendsto_escapingCopyCenter D)).mp hc
    have hval : copyMixingCoefficient 1 = (1 / 2 : ℝ) := by norm_num [copyMixingCoefficient]
    simp only [hval] at hb
    have he := tendsto_nhds_unique hb (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2)))
    norm_num at he

/-- Polar balance is not closed under global correlation and energy convergence, even
for a compact correlation family with uniform signed-grid trace decay. -/
theorem exists_smooth_polar_balanced_nonpolar_uniform_limit :
    ∃ (K : ℝ) (f : LevyEnergySource K) (g : ℕ → LevyEnergySource K),
      0 ≤ K ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) (f.source : ℝ → ℝ) ∧
      (∀ n, ContDiff ℝ (↑(⊤ : ℕ∞)) ((g n).source : ℝ → ℝ)) ∧
      0 < normalizedPolarMoment f.source ∧
      (∀ n, normalizedPolarMoment (g n).source = 0) ∧
      TendstoUniformly (fun n => (g n).correlation) f.correlation atTop ∧
      Tendsto (fun n => normalizedArchEnergy (g n).source) atTop
        (𝓝 (normalizedArchEnergy f.source)) ∧
      IsCompact (closure (LevyEnergySource.complexCorrelation '' range g)) ∧
      UniformSignedGridTail (range g) := by
  obtain ⟨f, D, hf, hR, hP, hD, _, hs⟩ := exists_short_positive_polar_seed
  have htwo : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) :=
    WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  have hf2 := hf.of_le htwo
  let T := escapingCopyCenter D
  let a := fun n => Real.exp (-T n / 2)
  let F := levyCopySeed f hf2 hR D
  let G := fun n => levyDistantCopy f hf2 hR hs (escapingCopyCenter_separated D n) (a n)
  have hT := tendsto_escapingCopyCenter D
  have hb := tendsto_polarCopy_mixing_zero T hT
  have hc := (isCompact_closure_distantCopies_iff f hf2 hR hD hs a T
    (escapingCopyCenter_separated D) hT).mpr hb
  refine ⟨copyEnergyCeiling f D, F, G, copyEnergyCeiling_nonneg f.continuous f.hasCompactSupport hR D,
    hf, fun n => contDiff_subtractCopy hf (a n) (T n), hP, ?_, ?_, ?_, hc, ?_⟩
  · intro n
    exact normalizedPolarMoment_polarCopy hf2 f.hasCompactSupport (T n)
  · exact (tendstoUniformly_subtractCopy_iff_mixing f.continuous f.hasCompactSupport hR hD hs a T
      (fun n => by have hh := escapingCopyCenter_separated D n; dsimp [T]; linarith)).mpr hb
  · exact tendsto_normalizedArchEnergy_subtractCopy hf2 f.hasCompactSupport hR hs a T
      (escapingCopyCenter_separated D) hT
  · exact (isCompact_closure_signed_correlations_iff_gridTail _).mp hc

end

end GaloisForLFunctions.BiScaleUncertainty
