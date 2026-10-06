import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticThirdInitialReconstruction
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticThirdInitialHighClock
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open HTGeometry.EvenCompactBernstein
open scoped Topology

theorem thirdInitialTensor_row34_neg (B : Fin 9) :
    thirdInitialTensorCoefficient 34 B < 0 := by
  fin_cases B
  · exact thirdInitialTensorCoefficient_34_0_neg
  · exact thirdInitialTensorCoefficient_34_1_neg
  · exact thirdInitialTensorCoefficient_34_2_neg
  · exact thirdInitialTensorCoefficient_34_3_neg
  · exact thirdInitialTensorCoefficient_34_4_neg
  · exact thirdInitialTensorCoefficient_34_5_neg
  · exact thirdInitialTensorCoefficient_34_6_neg
  · exact thirdInitialTensorCoefficient_34_7_neg
  · exact thirdInitialTensorCoefficient_34_8_neg

theorem thirdInitialRow34_reconstruction (v : ℝ) :
    kineticBernstein 8 (thirdInitialTensorCoefficient 34) v=
      thirdInitialQuotient (4/5) ((361/25)*v) := by
  have he := thirdInitialTensorValue_reconstruction 1 v
  norm_num [thirdInitialTensorValue,kineticBernstein,unscaledBernstein,
    Finset.sum_range_succ] at he ⊢
  exact he

theorem thirdInitialQuotient_high_clock_unit_neg (v : ℝ)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    thirdInitialQuotient (4/5) ((361/25)*v) < 0 := by
  have hp : 0 < kineticBernstein 8 (fun B => -thirdInitialTensorCoefficient 34 B) v := by
    apply kineticBernstein_pos 8 _ v _ hv0 hv1
    intro B hB
    exact neg_pos.mpr (thirdInitialTensor_row34_neg ⟨B,hB⟩)
  have he : kineticBernstein 8 (fun B => -thirdInitialTensorCoefficient 34 B) v=
      -kineticBernstein 8 (thirdInitialTensorCoefficient 34) v := by
    simp [kineticBernstein,Finset.sum_neg_distrib]
  rw [he,thirdInitialRow34_reconstruction] at hp
  exact neg_pos.mp hp

theorem thirdInitialQuotient_high_clock_neg (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 361/25) :
    thirdInitialQuotient (4/5) r < 0 := by
  have hv0 : 0 ≤ r/(361/25:ℝ) := div_nonneg hr0 (by norm_num)
  have hv1 : r/(361/25:ℝ) ≤ 1 := (div_le_iff₀ (by norm_num)).mpr (by simpa using hr1)
  have hp := thirdInitialQuotient_high_clock_unit_neg (r/(361/25)) hv0 hv1
  have he : (361/25:ℝ)*(r/(361/25))=r := by ring
  simpa only [he] using hp

theorem thirdValue_initial_defect_factor (h r : ℝ) :
    reducedKineticThirdValue h (9-r*h^2) 0=
      (9-r*h^2)*h^5*thirdInitialQuotient h r := by
  rw [reducedKineticThirdValue_drift_factor]
  have hc : reducedKineticThirdCore h (9-r*h^2) 0=
      6*higherKineticCoefficient h (9-r*h^2) 1 := by
    norm_num [reducedKineticThirdCore,Finset.sum_range_succ]
  have he := thirdInitial_factor h r
  rw [kineticThirdControl_initial] at he
  rw [hc,he]
  ring

theorem reducedKineticThirdValue_high_clock_initial_neg (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 361/25) (hv : 0 < 9-r*(4/5)^2) :
    reducedKineticThirdValue (4/5) (9-r*(4/5)^2) 0 < 0 := by
  rw [thirdValue_initial_defect_factor]
  exact mul_neg_of_pos_of_neg (mul_pos hv (by norm_num))
    (thirdInitialQuotient_high_clock_neg r hr0 hr1)

theorem kineticSlope_nonconvex_high_clock (r Z : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 361/25) (hv : 0 < 9-r*(4/5)^2) (hZ : 0 < Z) :
    ¬ ConvexOn ℝ (Set.Icc 0 Z) (reducedKineticSlopeValue (4/5) (9-r*(4/5)^2)) := by
  intro hconv
  have hf : Continuous (reducedKineticThirdValue (4/5) (9-r*(4/5)^2)) := by
    unfold reducedKineticThirdValue
    fun_prop
  have he : ∀ᶠ z : ℝ in 𝓝 0, reducedKineticThirdValue (4/5) (9-r*(4/5)^2) z < 0 :=
    hf.continuousAt.eventually (gt_mem_nhds
      (reducedKineticThirdValue_high_clock_initial_neg r hr0 hr1 hv))
  obtain ⟨δ,hδ,hnear⟩ := Metric.eventually_nhds_iff.mp he
  let z := min (δ/2) (Z/2)
  have hz0 : 0 < z := lt_min (by linarith) (by linarith)
  have hzδ : z < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hzZ : z < Z := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hn := hnear (show dist z 0 < δ by simpa [Real.dist_eq,abs_of_pos hz0] using hzδ)
  have hm := hconv.monotoneOn_deriv (fun x _ =>
    (reducedKineticSlopeValue_hasDerivAt (4/5) (9-r*(4/5)^2) x).differentiableAt)
  have hp := hm.derivWithin_nonneg (x := z)
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hz0 hzZ)] at hp
  have hd : deriv (reducedKineticSlopeValue (4/5) (9-r*(4/5)^2))=
      reducedKineticCurvatureValue (4/5) (9-r*(4/5)^2) := by
    funext x
    exact (reducedKineticSlopeValue_hasDerivAt (4/5) (9-r*(4/5)^2) x).deriv
  rw [hd,(reducedKineticCurvatureValue_hasDerivAt (4/5) (9-r*(4/5)^2) z).deriv] at hp
  exact (not_le_of_gt hn) hp

end
end HTGeometry.ThetaRatioKineticContraction
