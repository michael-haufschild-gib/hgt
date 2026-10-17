import GaloisForLFunctions.BiScaleUncertainty.FiniteIntegerTrainCompactness
import GaloisForLFunctions.BiScaleUncertainty.TernaryPacketPolarGrowth
import GaloisForLFunctions.BiScaleUncertainty.DistantCopySharpness

/-!
# Concrete finite-train producers and diffuse polar escape

Consecutive sites recover the earlier copyTrain exactly. Equal ternary packets
produce an unconditional smooth family with correlation error `1/(n+2)`, convergent
energy and diverging normalized polar moment under one energy ceiling.
-/

open MeasureTheory Set Filter Topology
open scoped CompactlySupported BoundedContinuousFunction
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def consecutivePacketTrain {m : ℕ} (c : Fin (m + 1) → ℝ) (hc : ∃ i, c i ≠ 0) : IntegerPacketTrain where
  last := m
  coefficient := c
  site := fun i => i.val
  site_injective := by
    intro i j hij
    apply Fin.ext
    change (i.val : ℤ) = (j.val : ℤ) at hij
    exact_mod_cast hij
  coefficient_nonzero := hc

theorem source_consecutivePacketTrain {m : ℕ} (c : Fin (m + 1) → ℝ) (hc : ∃ i, c i ≠ 0)
    (f : ℝ → ℝ) (S : ℝ) : (consecutivePacketTrain c hc).source f S = copyTrain f c S := by
  funext u
  change finiteTranslateSource f Finset.univ c (fun i : Fin (m + 1) => ((i.val : ℤ) : ℝ) * S) u =
    finiteTranslateSource f Finset.univ c (fun i : Fin (m + 1) => (i.val : ℝ) * S) u
  simp only [Int.cast_natCast]

theorem lagCoefficient_consecutivePacketTrain {m : ℕ} (c : Fin (m + 1) → ℝ) (hc : ∃ i, c i ≠ 0)
    (k : ℤ) : (consecutivePacketTrain c hc).lagCoefficient k = copyTrainLagCoefficient c k := rfl

def diffuseTrainSpacing (n : ℕ) : ℝ := escapingCopyCenter 6 n

theorem diffuseTrainSpacing_separated (n : ℕ) : 2 * (2 : ℝ) + 2 ≤ diffuseTrainSpacing n := by
  have hn : 0 ≤ (n : ℝ) := by positivity
  dsimp [diffuseTrainSpacing, escapingCopyCenter]
  linarith only [hn]

theorem diffuseTrainSpacing_ge_count (n : ℕ) : (n : ℝ) + 2 ≤ diffuseTrainSpacing n := by
  dsimp [diffuseTrainSpacing, escapingCopyCenter]
  linarith

theorem tendsto_diffuseTrainSpacing : Tendsto diffuseTrainSpacing atTop atTop :=
  tendsto_escapingCopyCenter 6

theorem tendsto_ternaryPacketTrain_peak : Tendsto (fun n => (ternaryPacketTrain n).peak) atTop (𝓝 0) := by
  have hq : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 (tendsto_natCast_atTop_atTop (R := ℝ))
  have hi := (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)).comp hq
  simpa only [ternaryPacketTrain_peak, Function.comp_def, one_div] using hi

/-- An actual diffuse smooth source producer: compact normalized correlations and
convergent energies coexist with unbounded polar moments and no dominant packet. -/
theorem exists_smooth_diffuse_train_polar_escape :
    ∃ (K : ℝ) (f : LevyEnergySource K) (g : ℕ → LevyEnergySource K),
      0 ≤ K ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) (f.source : ℝ → ℝ) ∧
      (∀ n, ContDiff ℝ (↑(⊤ : ℕ∞)) ((g n).source : ℝ → ℝ)) ∧
      0 < normalizedPolarMoment f.source ∧
      (∀ n, autocorr (g n).source 0 = ((n : ℝ) + 2) * autocorr f.source 0) ∧
      (∀ n, dist (g n).complexCorrelation f.complexCorrelation = 1 / ((n : ℝ) + 2)) ∧
      (∀ n : ℕ, (((n : ℝ) + 2) / 4) * normalizedPolarMoment f.source ≤ normalizedPolarMoment (g n).source) ∧
      Tendsto (fun n => normalizedPolarMoment (g n).source) atTop atTop ∧
      TendstoUniformly (fun n => (g n).correlation) f.correlation atTop ∧
      Tendsto (fun n => normalizedArchEnergy (g n).source) atTop (𝓝 (normalizedArchEnergy f.source)) ∧
      IsCompact (closure (LevyEnergySource.complexCorrelation '' range g)) ∧
      UniformSignedGridTail (range g) := by
  obtain ⟨p, hp, hpc, hR, hP, hsp⟩ :=
    exists_smooth_source_positive_polar_moment (by norm_num : (0 : ℝ) < 1)
  let f : C_c(ℝ, ℝ) := ⟨⟨p, hp.continuous⟩, hpc⟩
  have htwo : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) :=
    WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  have hf2 : ContDiff ℝ 2 (f : ℝ → ℝ) := hp.of_le htwo
  have hs : ∀ x, (2 : ℝ) < |x| → autocorr f x = 0 := by
    intro x hx
    exact autocorr_eq_zero_of_source_radius hsp (by simpa only [mul_one] using hx)
  have hD : (0 : ℝ) ≤ 2 := by norm_num
  let F := levyIntegerTrainSeed f hf2 hR
  let G := fun n => levyIntegerTrain (ternaryPacketTrain n) f hf2 hR hD hs (diffuseTrainSpacing_separated n)
  have hsep (n : ℕ) : 2 * (2 : ℝ) < diffuseTrainSpacing n := by
    have hh := diffuseTrainSpacing_separated n
    linarith only [hh]
  have hformula (n : ℕ) : normalizedPolarMoment (G n).source =
      (ternaryPacketTrain n).polarMultiplier (diffuseTrainSpacing n) * normalizedPolarMoment f :=
    (ternaryPacketTrain n).normalizedPolarMoment_source hf2 f.hasCompactSupport hR hD hs (hsep n)
  have hbound (n : ℕ) : (((n : ℝ) + 2) / 4) * normalizedPolarMoment f ≤
      normalizedPolarMoment (G n).source := by
    rw [hformula]
    exact mul_le_mul_of_nonneg_right
      (ternaryPacketTrain_polarMultiplier_ge (diffuseTrainSpacing_ge_count n)) hP.le
  have hgrowth : Tendsto (fun n => normalizedPolarMoment (G n).source) atTop atTop := by
    have hq : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 (tendsto_natCast_atTop_atTop (R := ℝ))
    have hl : Tendsto (fun n : ℕ => (((n : ℝ) + 2) / 4) * normalizedPolarMoment f) atTop atTop := by
      convert Filter.Tendsto.const_mul_atTop
        (show 0 < normalizedPolarMoment f / 4 by positivity) hq using 1
      funext n
      ring
    exact tendsto_atTop_mono hbound hl
  have hc := (isCompact_closure_integerTrains_iff_peak f hf2 hR hD hs ternaryPacketTrain
    diffuseTrainSpacing diffuseTrainSpacing_separated tendsto_diffuseTrainSpacing).mpr tendsto_ternaryPacketTrain_peak
  refine ⟨integerTrainEnergyCeiling f, F, G, integerTrainEnergyCeiling_nonneg f.continuous f.hasCompactSupport hR,
    hp, fun n => (ternaryPacketTrain n).contDiff_source hp (diffuseTrainSpacing n), hP,
    ?_, ?_, hbound, hgrowth, ?_, ?_, hc, ?_⟩
  · intro n
    change autocorr ((ternaryPacketTrain n).source f (diffuseTrainSpacing n)) 0 =
      ((n : ℝ) + 2) * autocorr f 0
    rw [(ternaryPacketTrain n).autocorr_source_zero (f := (f : ℝ → ℝ)) f.continuous
      f.hasCompactSupport hD hs (hsep n), ternaryPacketTrain_mass]
  · intro n
    exact (levyIntegerTrain_dist_seed (ternaryPacketTrain n) f hf2 hR hD hs
      (diffuseTrainSpacing_separated n)).trans (ternaryPacketTrain_peak n)
  · exact (tendstoUniformly_integerTrains_iff_peak f.continuous f.hasCompactSupport hR hD hs
      ternaryPacketTrain diffuseTrainSpacing hsep).mpr tendsto_ternaryPacketTrain_peak
  · exact tendsto_integerTrain_energy hf2 f.hasCompactSupport hR hD hs ternaryPacketTrain
      diffuseTrainSpacing hsep tendsto_diffuseTrainSpacing
  · exact (isCompact_closure_signed_correlations_iff_gridTail _).mp hc

end
end GaloisForLFunctions.BiScaleUncertainty
