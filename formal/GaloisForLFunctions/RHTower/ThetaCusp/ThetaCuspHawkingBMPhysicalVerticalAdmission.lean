import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMAngularVerticalBounds

/-! Original quotient admission of the actual physical angular field's vertical derivative. -/
open Complex Set Filter Topology MeasureTheory
open scoped ContDiff
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse D4BMAngularSeries D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Differentiating the surviving physical Weyl term retains its exact coefficient and every tail derivative. -/
theorem physicalScalar_vertical_eq (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    coordDeriv 1 (scalar (physicalAngularParameter q)) z =
      reflectedCompletedLambda ((q.1:ℂ)-1)*(1-(q.1:ℂ)/2)*(z 1:ℂ)^(-((q.1:ℂ)/2))+
      coordDeriv 1 (tail (physicalAngularParameter q)) z := by
  let u := physicalAngularParameter q
  let c := reflectedCompletedLambda ((q.1:ℂ)-1)
  let k := 1-(q.1:ℂ)/2
  have he : scalar u = fun w => c*(w 1:ℂ)^k+tail u w := by
    funext w
    change principal u w+tail u w = _
    rw [physicalScalar_principal]
  have hp := height_cpow_hasFDerivAt k z hz
  have ht : DifferentiableAt ℝ (tail u) z :=
    ((cuspTailPart_contDiffOn .scalar u).contDiffAt
      ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)).differentiableAt (by simp)
  change coordDeriv 1 (scalar u) z = _
  unfold coordDeriv
  rw [he,fderiv_fun_add (hp.differentiableAt.const_mul c) ht,
    fderiv_const_mul hp.differentiableAt,hp.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul]
  have hg (X Y : ℂ) : D4BMAngularSeries.gradient X Y (Pi.single 1 1) = Y := by
    simp [D4BMAngularSeries.gradient]
  rw [hg]
  rw [show k-1 = -((q.1:ℂ)/2) by dsimp [k]; ring]
  dsimp [c,k,u]
  ring

/-- The ordinary vertical derivative of the complete physical field is uniformly bounded in the high cusp. -/
theorem physicalScalar_vertical_cusp_bound (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Fin 2 → ℝ, 3 < z 1 →
      ‖coordDeriv 1 (scalar (physicalAngularParameter q)) z‖ ≤ C := by
  obtain ⟨B,hB,hb⟩ := tail_vertical_bounded (physicalAngularParameter q) 3 (by norm_num)
  refine ⟨‖reflectedCompletedLambda ((q.1:ℂ)-1)*(1-(q.1:ℂ)/2)‖+B,by positivity,?_⟩
  intro z hz
  have hy : 0 < z 1 := by linarith
  have hp : ‖(z 1:ℂ)^(-((q.1:ℂ)/2))‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
    simp only [Complex.neg_re,Complex.div_ofNat_re]
    linarith [(xi_divisor_support_re_mem_open_unit q.1).1]
  rw [physicalScalar_vertical_eq q z hy]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_mul]
      have hn := norm_nonneg (reflectedCompletedLambda ((q.1:ℂ)-1)*(1-(q.1:ℂ)/2))
      exact add_le_add (by simpa using mul_le_mul_of_nonneg_left hp hn) (hb z hz.le)

/-- No derivative-admission premise is needed for the full physical angular field in the original quotient L² space. -/
theorem physicalScalar_vertical_memLp (q : XiZeroCopy) :
    MemLp (fun z : UpperHalfPlane => coordDeriv 1 (scalar (physicalAngularParameter q)) (coordinates z))
      2 D4BMModularCore.measure := by
  obtain ⟨C,_hC,hC⟩ := physicalScalar_vertical_cusp_bound q
  apply cuspBound_memLp _ _ C hC
  intro z hz
  have hs := (cuspLeg_contDiffOn .scalar (physicalAngularParameter q)).contDiffAt
    ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)
  exact ((hs.fderiv_right (m := 0) (by simp)).clm_apply contDiffAt_const).continuousAt.continuousWithinAt

end
end RHTower.D4BMJointSource
