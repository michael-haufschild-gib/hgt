import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSlopeConvexityObstruction
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open scoped Topology

theorem thirdInitialQuotient_zero_clock (r : ℝ) :
    thirdInitialQuotient 0 r=615974148349919265846014022600622080 := by
  norm_num [thirdInitialQuotient,thirdInitialRow5,Nat.rawCast]

theorem thirdInitialQuotient_clock_continuous (r : ℝ) :
    Continuous (fun h : ℝ => thirdInitialQuotient h r) := by
  unfold thirdInitialQuotient
  fun_prop

theorem reducedKineticThirdValue_initial_small_clock_pos (r : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      0 < 9-r*h^2 ∧ 0 < reducedKineticThirdValue h (9-r*h^2) 0 := by
  have hq : ∀ᶠ h : ℝ in 𝓝 0, 0 < thirdInitialQuotient h r :=
    (thirdInitialQuotient_clock_continuous r).continuousAt.eventually
      (lt_mem_nhds (by
        change 0 < thirdInitialQuotient 0 r
        rw [thirdInitialQuotient_zero_clock]
        norm_num))
  have hv : ∀ᶠ h : ℝ in 𝓝 0, 0 < 9-r*h^2 := by
    have hc : Continuous (fun h : ℝ => 9-r*h^2) := by fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds (by norm_num))
  obtain ⟨δ,hδ,hnear⟩ := Metric.eventually_nhds_iff.mp (hq.and hv)
  refine ⟨δ,hδ,?_⟩
  intro h hh0 hhδ
  have hs := hnear (show dist h 0 < δ by simpa [Real.dist_eq,abs_of_pos hh0] using hhδ)
  refine ⟨hs.2,?_⟩
  rw [thirdValue_initial_defect_factor]
  exact mul_pos (mul_pos hs.2 (pow_pos hh0 5)) hs.1

theorem thirdInitialQuotient_clock_root (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 361/25) :
    ∃ h : ℝ, 0 < h ∧ h < 4/5 ∧ thirdInitialQuotient h r=0 := by
  have hpos : 0 < thirdInitialQuotient 0 r := by
    rw [thirdInitialQuotient_zero_clock]
    norm_num
  have hneg := thirdInitialQuotient_high_clock_neg r hr0 hr1
  obtain ⟨h,hh,hzero⟩ := intermediate_value_Icc' (f := fun h => thirdInitialQuotient h r)
    (show (0:ℝ) ≤ 4/5 by norm_num)
    (thirdInitialQuotient_clock_continuous r).continuousOn ⟨hneg.le,hpos.le⟩
  have hh0 : 0 < h := by
    by_contra hn
    have he : h=0 := le_antisymm (not_lt.mp hn) hh.1
    rw [he] at hzero
    linarith
  have hh1 : h < 4/5 := by
    by_contra hn
    have he : h=4/5 := le_antisymm hh.2 (not_lt.mp hn)
    rw [he] at hzero
    linarith
  exact ⟨h,hh0,hh1,hzero⟩

theorem reducedKineticThirdValue_initial_clock_root (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 361/25) :
    ∃ h : ℝ, 0 < h ∧ h < 4/5 ∧ thirdInitialQuotient h r=0 ∧
      reducedKineticThirdValue h (9-r*h^2) 0=0 := by
  obtain ⟨h,hh0,hh1,hq⟩ := thirdInitialQuotient_clock_root r hr0 hr1
  refine ⟨h,hh0,hh1,hq,?_⟩
  rw [thirdValue_initial_defect_factor,hq,mul_zero]

end
end HTGeometry.ThetaRatioKineticContraction
