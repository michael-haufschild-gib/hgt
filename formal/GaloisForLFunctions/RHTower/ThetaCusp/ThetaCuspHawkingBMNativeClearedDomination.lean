import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeScalarUniformCusp
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeResidualUniformWeights
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalAngularModularity

/-! Domination of the entire scalar field against the original quotient residual. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMModularCore D4BMGlobalAngularResponse D4BMAngularSeries
noncomputable section

private theorem parameter_coefficient_bound (f : ℂ → ℂ) (hf : Continuous f) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖u‖ ≤ R → ‖f u‖ ≤ C := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:ℂ) R).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro u hu
  exact (hC u (by simpa only [Metric.mem_closedBall,dist_zero_right] using hu)).trans (le_max_right _ _)

/-- One constant dominates the full cleared scalar-source product over each spectral ball. -/
theorem clearedScalar_squareResidual_fd_uniform (q : XiZeroCopy) (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℂ) (z : UpperHalfPlane), ‖u‖ ≤ R → z ∈ fd →
      ‖clearedScalar u (coordinates z) * squareResidual q (coordinates z)‖ ≤ C := by
  have hXi := differentiable_riemannXi.continuous
  obtain ⟨A,hA,ha⟩ := parameter_coefficient_bound
    (fun u : ℂ => (2*u+1)*riemannXi (2*u)) (by fun_prop) R
  obtain ⟨B,hB,hb⟩ := parameter_coefficient_bound
    (fun u : ℂ => (2*u-1)*riemannXi (1+2*u)) (by fun_prop) R
  obtain ⟨P,hP,hp⟩ := parameter_coefficient_bound clearFactor (by unfold clearFactor; fun_prop) R
  obtain ⟨W,hW,hw⟩ := squareResidual_fd_uniform_weight_bound q (1/2-R) (1/2+R)
  obtain ⟨T,hT,ht⟩ := scalar_tail_uniform_cusp R (1/2) hR (by norm_num)
  obtain ⟨S,hS,hs⟩ := squareResidual_cell_bound q
  refine ⟨A*W+B*W+P*(T*S),by positivity,?_⟩
  intro u z hu hz
  have hre := (Complex.abs_re_le_norm u).trans hu
  have hrel := (abs_le.mp hre).1
  have hreu := (abs_le.mp hre).2
  have hm : ‖(z.im:ℂ)^(1/2-u) * squareResidual q (coordinates z)‖ ≤ W :=
    hw (1/2-u) z (by simp; linarith) (by simp; linarith) hz
  have hplus : ‖(z.im:ℂ)^(1/2+u) * squareResidual q (coordinates z)‖ ≤ W :=
    hw (1/2+u) z (by simp; linarith) (by simp; linarith) hz
  have hy : (1/2:ℝ) ≤ z.im := by
    nlinarith [ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz,z.im_pos]
  have htail : ‖tail u (coordinates z) * squareResidual q (coordinates z)‖ ≤ T*S := by
    rw [norm_mul]
    exact mul_le_mul (ht u (coordinates z) hu hy) (hs z hz) (norm_nonneg _) hT
  have he : clearedScalar u (coordinates z) * squareResidual q (coordinates z) =
      ((2*u+1)*riemannXi (2*u))*((z.im:ℂ)^(1/2-u)*squareResidual q (coordinates z)) +
      ((2*u-1)*riemannXi (1+2*u))*((z.im:ℂ)^(1/2+u)*squareResidual q (coordinates z)) +
      clearFactor u*(tail u (coordinates z)*squareResidual q (coordinates z)) := by
    dsimp [clearedScalar,coordinates]
    ring
  rw [he]
  calc
    _ ≤ ‖((2*u+1)*riemannXi (2*u))*((z.im:ℂ)^(1/2-u)*squareResidual q (coordinates z))‖ +
        ‖((2*u-1)*riemannXi (1+2*u))*((z.im:ℂ)^(1/2+u)*squareResidual q (coordinates z))‖ +
        ‖clearFactor u*(tail u (coordinates z)*squareResidual q (coordinates z))‖ := norm_add₃_le
    _ ≤ _ := by
      apply add_le_add
      · apply add_le_add
        · rw [norm_mul]
          exact mul_le_mul (ha u hu) hm (norm_nonneg _) hA
        · rw [norm_mul]
          exact mul_le_mul (hb u hu) hplus (norm_nonneg _) hB
      · rw [norm_mul]
        exact mul_le_mul (hp u hu) htail (norm_nonneg _) hP

end
end RHTower.D4BMJointSource
