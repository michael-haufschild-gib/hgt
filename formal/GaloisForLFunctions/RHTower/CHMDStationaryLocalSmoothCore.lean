import GaloisForLFunctions.RHTower.CHMDStationaryLocalOperatorDomain

/-!
# Local smoothing of the actual stationary operator domain

After a cutoff fixes the source, transfer to the ordinary stationary generator,
mollify, and apply the fixed local inverse. The exact cutoff commutator and
the bounded theta adjoint give convergence of the actual generator images.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDClosedJump CHMDPolar

def localizedVolumeVector (k : ℕ) (u : stationaryGenerator.domain) (hu : massCutoff k u = u) :
    volumeGenerator.domain := ⟨thetaToVolume u, localized_theta_mem_volume_domain k u hu⟩

def localStationarySmooth (k : ℕ) (u : stationaryGenerator.domain) (hu : massCutoff k u = u)
    (n : ℕ) : stationaryGenerator.domain :=
  ⟨localThetaInverse k (volumeSmooth n (thetaToVolume u)),
    stationary_of_volume_mem_domain _
      (volumeGeneratorCutoff k (volumeGeneratorSmooth n (localizedVolumeVector k u hu)))
      (thetaToVolume_localInverse k (volumeSmooth n (thetaToVolume u))).symm⟩

theorem localStationarySmooth_apply (k : ℕ) (u : stationaryGenerator.domain)
    (hu : massCutoff k u = u) (n : ℕ) :
    stationaryGenerator (localStationarySmooth k u hu n) =
      thetaToVolume.adjoint
        (volumeCutoff k (volumeSmooth n (volumeGenerator (localizedVolumeVector k u hu))) +
          volumeCutoffCommutator k (volumeSmooth n (thetaToVolume u))) := by
  have h := stationary_of_volume_apply (localStationarySmooth k u hu n)
    (volumeGeneratorCutoff k (volumeGeneratorSmooth n (localizedVolumeVector k u hu)))
    (thetaToVolume_localInverse k (volumeSmooth n (thetaToVolume u))).symm
  rw [volumeGeneratorCutoff_apply, volumeGeneratorSmooth_apply] at h
  exact h

theorem localStationarySmooth_tendsto (k : ℕ) (u : stationaryGenerator.domain)
    (hu : massCutoff k u = u) :
    Tendsto (fun n => (localStationarySmooth k u hu n : MassSpace)) atTop (𝓝 (u : MassSpace)) ∧
    Tendsto (fun n => stationaryGenerator (localStationarySmooth k u hu n)) atTop
      (𝓝 (stationaryGenerator u)) := by
  constructor
  · have h := ((localThetaInverse k).continuous.tendsto (thetaToVolume u)).comp
      (volumeSmooth_tendsto (thetaToVolume u))
    rw [localInverse_thetaToVolume, hu] at h
    exact h
  · let f := localizedVolumeVector k u hu
    have hc : volumeGeneratorCutoff k f = f := by
      apply Subtype.ext
      change volumeCutoff k (thetaToVolume u) = thetaToVolume u
      rw [← thetaToVolume_cutoff, hu]
    have he := volumeGeneratorCutoff_apply k f
    rw [hc] at he
    have h := (thetaToVolume.adjoint.continuous.tendsto
      (volumeCutoff k (volumeGenerator f) + volumeCutoffCommutator k (f : StationaryVolumeSpace))).comp
        ((((volumeCutoff k).continuous.tendsto (volumeGenerator f)).comp
          (volumeSmooth_tendsto (volumeGenerator f))).add
          (((volumeCutoffCommutator k).continuous.tendsto (f : StationaryVolumeSpace)).comp
            (volumeSmooth_tendsto (f : StationaryVolumeSpace))))
    rw [← he, ← stationary_of_volume_apply u f rfl] at h
    simpa only [localStationarySmooth_apply, Function.comp_def, f, localizedVolumeVector] using h

theorem localStationarySmooth_compact_contDiff (k : ℕ) (u : stationaryGenerator.domain)
    (hu : massCutoff k u = u) (n : ℕ) :
    ∃ v : ℝ → ℝ, ContDiff ℝ 2 v ∧ HasCompactSupport v ∧
      (localStationarySmooth k u hu n : MassSpace) =ᵐ[massMeasure] v := by
  refine ⟨fun x => localThetaInverseFactor k x * smooth (thetaToVolume u) n x,
    (localThetaInverseFactor_contDiff k).mul (smooth_contDiff (Lp.memLp _) n),
    (localThetaInverseFactor_compact k).mul_right, ?_⟩
  filter_upwards [localThetaInverse_ae k (volumeSmooth n (thetaToVolume u)),
    (withDensity_absolutelyContinuous volume _).ae_le (volumeSmooth_ae n (thetaToVolume u))]
    with x hi hs
  change localThetaInverse k (volumeSmooth n (thetaToVolume u)) x = _
  rw [hi, hs]

theorem exists_cutoff_fix_compact {v : ℝ → ℝ} (hc : HasCompactSupport v) :
    ∃ k : ℕ, ∀ x : ℝ, cutoff k x * v x = v x := by
  obtain ⟨L, hL⟩ := hc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨k, hk⟩ := exists_nat_ge |L|
  refine ⟨k, fun x => ?_⟩
  by_cases hx : v x = 0
  · simp [hx]
  · have hxl : |x| ≤ L := by
      have h := hL (subset_tsupport v hx)
      simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using h
    have hb : |cutoffScale k * x| ≤ 1 := by
      rw [abs_mul, abs_of_pos (cutoffScale_pos k)]
      change ((k : ℝ) + 1)⁻¹ * |x| ≤ 1
      rw [mul_comm, ← div_eq_mul_inv]
      apply (div_le_one (by positivity : (0 : ℝ) < (k : ℝ) + 1)).mpr
      linarith [le_abs_self L]
    have he : cutoff k x = 1 := by
      apply baseCutoff.one_of_mem_closedBall
      change dist (cutoffScale k * x) 0 ≤ 1
      simpa only [dist_zero_right, Real.norm_eq_abs] using hb
    rw [he, one_mul]

theorem exists_massCutoff_fixed (u : MassSpace)
    (hc : ∃ v : ℝ → ℝ, HasCompactSupport v ∧ u =ᵐ[massMeasure] v) :
    ∃ k : ℕ, massCutoff k u = u := by
  obtain ⟨v, hv, huv⟩ := hc
  obtain ⟨k, hk⟩ := exists_cutoff_fix_compact hv
  refine ⟨k, Lp.ext ?_⟩
  filter_upwards [massCutoff_ae k u, huv] with x hx hvx
  rw [hx, hvx, hk]

end RHTower.CHMDDoobGraph
