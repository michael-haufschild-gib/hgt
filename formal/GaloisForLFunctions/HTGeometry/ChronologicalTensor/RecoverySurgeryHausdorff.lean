import GaloisForLFunctions.HTGeometry.ChronologicalTensor.RecoverySurgeryCurvature
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Quantitative Hausdorff convergence of the surgery domains

A point in the wedge is close to its copy in the inscribed homothetic core.
This proves a quadratic-rate Hausdorff bound and convergence to the original
wedge, using the actual planar sets and their ordinary product metric.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Filter Topology

theorem recoverySurgeryCorePower_le_scale (n : ℕ) :
    recoverySurgeryCorePower n ≤ recoverySurgeryCoreScale n := by
  rw [← recoverySurgeryCoreScale_power, show n+2=(n+1)+1 by omega, pow_succ]
  have h : (recoverySurgeryCoreScale n)^(n+1) ≤ 1 := pow_le_one₀ (le_of_lt (recoverySurgeryCoreScale_positive n))
    (le_of_lt (recoverySurgeryCoreScale_lt_one n))
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h
    (le_of_lt (recoverySurgeryCoreScale_positive n))

theorem recoveryWedge_radial_distance (p : ℝ × ℝ) (hp : p ∈ recoveryWedge)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    dist p (q*p.1,q*p.2) ≤ 3*(1-q) := by
  have h0 : 0 ≤ p.1 := hp.1.trans hp.2.2.1
  have h3 : p.1 ≤ 3 := by linarith [hp.2.2.2,hp.2.1]
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq]
  have hu : 0 ≤ p.1-q*p.1 := by nlinarith [hq.2]
  have hc : 0 ≤ p.2-q*p.2 := by nlinarith [hq.2,hp.1]
  rw [abs_of_nonneg hu, abs_of_nonneg hc]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr h3) (sub_nonneg.mpr hq.2)]
  · nlinarith [mul_nonneg (show 0 ≤ 3-p.2 by linarith [hp.2.1]) (sub_nonneg.mpr hq.2)]

theorem recoverySurgeryDomain_hausdorff_bound (n : ℕ) :
    Metric.hausdorffDist (recoverySurgeryDomain n) recoveryWedge ≤ 33/(32*(n+2 : ℝ)^2) := by
  have ha := recoverySurgeryCorePower_le_scale n
  have hb := recoverySurgeryCorePower_deficit_bound n
  have hq : recoverySurgeryCoreScale n ∈ Icc (0 : ℝ) 1 :=
    ⟨le_of_lt (recoverySurgeryCoreScale_positive n),le_of_lt (recoverySurgeryCoreScale_lt_one n)⟩
  apply Metric.hausdorffDist_le_of_mem_dist (by positivity)
  · intro p hp
    exact ⟨p,hp.1,by rw [dist_self]; positivity⟩
  · intro p hp
    refine ⟨(recoverySurgeryCoreScale n*p.1,recoverySurgeryCoreScale n*p.2),
      recoverySurgeryDomain_core n p hp,?_⟩
    apply (recoveryWedge_radial_distance p hp _ hq).trans
    have he : 33/(32*(n+2 : ℝ)^2)=3*(11/(32*(n+2 : ℝ)^2)) := by ring
    rw [he]
    linarith

theorem recoverySurgeryDomain_hausdorff_tendsto :
    Tendsto (fun n : ℕ => Metric.hausdorffDist (recoverySurgeryDomain n) recoveryWedge)
      atTop (𝓝 0) := by
  have hb : ∀ n : ℕ, Metric.hausdorffDist (recoverySurgeryDomain n) recoveryWedge ≤
      (33/32 : ℝ)*(1/(n+1 : ℝ)) := by
    intro n
    apply (recoverySurgeryDomain_hausdorff_bound n).trans
    rw [mul_one_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [sq_nonneg (n : ℝ)]
  apply squeeze_zero (fun n => Metric.hausdorffDist_nonneg) hb
  simpa only [mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (33/32 : ℝ)

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
