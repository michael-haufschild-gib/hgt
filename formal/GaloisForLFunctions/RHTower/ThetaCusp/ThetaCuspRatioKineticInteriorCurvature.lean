import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioKineticAxisCurvature
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open ThetaRatioInfinity
open scoped Topology

def curvaturePerturbationR (h s : ℝ) : ℝ :=
  s*(1-h^2*(1/12-7*h/72)*s)

def curvatureBoundaryZ (h s : ℝ) : ℝ :=
  (1-h*(1/12-7*h/72)*s)/3

def curvaturePerturbationZ (h s : ℝ) : ℝ :=
  (1-s)*curvatureBoundaryZ h s

theorem curvaturePerturbationR_incidence (h s : ℝ) :
    nonlinearBoundaryR (h:ℂ) (s:ℂ) = (curvaturePerturbationR h s:ℂ) := by
  unfold nonlinearBoundaryR nonlinearBoundarySeed curvaturePerturbationR
  push_cast
  rfl

theorem curvatureBoundaryZ_incidence (h s : ℝ) :
    nonlinearBoundaryZ (h:ℂ) (s:ℂ) = (curvatureBoundaryZ h s:ℂ) := by
  unfold nonlinearBoundaryZ nonlinearBoundaryT nonlinearBoundarySeed curvatureBoundaryZ
  push_cast
  ring

theorem curvaturePerturbation_core_continuous (h : ℝ) :
    Continuous (fun s : ℝ => reducedKineticCurvatureCore h
      (9-curvaturePerturbationR h s*h^2) (curvaturePerturbationZ h s)) := by
  simp_rw [reducedKineticCurvatureCore_drift_tensor]
  unfold curvaturePerturbationR curvaturePerturbationZ curvatureBoundaryZ
  fun_prop

theorem positive_curvature_inside_nonlinear_cone (h : ℝ)
    (hh0 : 0 < h) (hh1 : h ≤ 4/5) (hh : 1 ≤ 14*h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      s < (6/5)*(361/25) ∧
      0 < curvaturePerturbationR h s ∧
      curvaturePerturbationR h s < 361/25 ∧
      0 < 9-curvaturePerturbationR h s*h^2 ∧
      0 < curvaturePerturbationZ h s ∧
      curvaturePerturbationZ h s < curvatureBoundaryZ h s ∧
      curvatureBoundaryZ h s < 1/3 ∧
      0 < deriv (deriv (reducedKineticValue h
        (9-curvaturePerturbationR h s*h^2))) (curvaturePerturbationZ h s) := by
  have hb : 0 < (1/12-7*h/72:ℝ) := by linarith only [hh1]
  have heF : ∀ᶠ s : ℝ in 𝓝 0, 0 < 1-h^2*(1/12-7*h/72)*s := by
    have hc : Continuous (fun s : ℝ => 1-h^2*(1/12-7*h/72)*s) := by fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds (by norm_num))
  have heR : ∀ᶠ s : ℝ in 𝓝 0, curvaturePerturbationR h s < 361/25 := by
    have hc : Continuous (curvaturePerturbationR h) := by unfold curvaturePerturbationR; fun_prop
    exact hc.continuousAt.eventually (gt_mem_nhds (by norm_num [curvaturePerturbationR]))
  have heV : ∀ᶠ s : ℝ in 𝓝 0, 0 < 9-curvaturePerturbationR h s*h^2 := by
    have hc : Continuous (fun s : ℝ => 9-curvaturePerturbationR h s*h^2) := by
      unfold curvaturePerturbationR
      fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds (by norm_num [curvaturePerturbationR]))
  have heZ : ∀ᶠ s : ℝ in 𝓝 0, 0 < curvatureBoundaryZ h s := by
    have hc : Continuous (curvatureBoundaryZ h) := by unfold curvatureBoundaryZ; fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds (by norm_num [curvatureBoundaryZ]))
  have heC : ∀ᶠ s : ℝ in 𝓝 0, 0 < reducedKineticCurvatureCore h
      (9-curvaturePerturbationR h s*h^2) (curvaturePerturbationZ h s) := by
    apply (curvaturePerturbation_core_continuous h).continuousAt.eventually
    apply lt_mem_nhds
    simpa [curvaturePerturbationR,curvaturePerturbationZ,curvatureBoundaryZ] using
      reducedKineticCurvatureCore_terminal_axis_pos h hh0 (by linarith) hh
  have heS : ∀ᶠ s : ℝ in 𝓝 0, s < 1 := gt_mem_nhds (by norm_num)
  have he := heF.and (heR.and (heV.and (heZ.and (heC.and heS))))
  obtain ⟨δ,hδ,hnear⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ,hδ,?_⟩
  intro s hs0 hsδ
  have hdist : dist s 0 < δ := by simpa [Real.dist_eq,abs_of_pos hs0] using hsδ
  obtain ⟨hF,hR,hV,hZ,hC,hS⟩ := hnear hdist
  refine ⟨by linarith,?_,hR,hV,?_,?_,?_,?_⟩
  · exact mul_pos hs0 hF
  · exact mul_pos (by linarith) hZ
  · unfold curvaturePerturbationZ
    nlinarith only [mul_pos hs0 hZ]
  · unfold curvatureBoundaryZ
    nlinarith only [mul_pos (mul_pos hh0 hb) hs0]
  · rw [reducedKineticValue_second_derivative]
    exact mul_pos hV hC

theorem nonconcave_inside_nonlinear_cone (h : ℝ)
    (hh0 : 0 < h) (hh1 : h ≤ 4/5) (hh : 1 ≤ 14*h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      ¬ ConcaveOn ℝ (Set.Icc 0 (curvatureBoundaryZ h s))
        (reducedKineticValue h (9-curvaturePerturbationR h s*h^2)) := by
  obtain ⟨δ,hδ,hp⟩ := positive_curvature_inside_nonlinear_cone h hh0 hh1 hh
  refine ⟨δ,hδ,?_⟩
  intro s hs0 hsδ hconc
  obtain ⟨_,_,_,_,hz0,hz1,_,hc⟩ := hp s hs0 hsδ
  have hm := hconc.antitoneOn_deriv (fun z _ =>
    (reducedKineticValue_hasDerivAt h (9-curvaturePerturbationR h s*h^2) z).differentiableAt)
  have hn := hm.derivWithin_nonpos (x := curvaturePerturbationZ h s)
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hz0 hz1)] at hn
  exact (not_le_of_gt hc) hn

end
end HTGeometry.ThetaRatioKineticContraction
