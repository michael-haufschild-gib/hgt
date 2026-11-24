import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.HaarBound
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.CircularArcRange

/-! # Attainment of the Haar operator-ball bound by diagonal targets -/
open Matrix Set MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
noncomputable section

private theorem chord_upper (z : UnitAddCircle) {x t : ℝ} (hx : x∈Icc (0:ℝ) 1) (ht : |t|≤x/2) :
    ‖(z.toCircle:ℂ)-((z+(t:UnitAddCircle)).toCircle:ℂ)‖ ≤ zeroGateArcTolerance x := by
  rw [AddCircle.toCircle_add,Circle.coe_mul,←mul_one_sub,norm_mul,Circle.norm_coe,one_mul,
    AddCircle.toCircle_apply_mk,div_one,Circle.coe_exp]
  let a := 2*Real.pi*t
  have h := norm_expI_sub_eq_sin_circDist 0 a
  simp only [Complex.ofReal_zero,zero_mul,Complex.exp_zero] at h
  rw [h,zeroGateArcTolerance]
  have ha : circDist 0 a ≤ Real.pi*x := (circDist_le_abs_sub _ _).trans (by
    dsimp only [a]
    rw [zero_sub,abs_neg,abs_mul,abs_of_pos Real.two_pi_pos]
    linarith only [mul_le_mul_of_nonneg_left ht Real.two_pi_pos.le])
  apply mul_le_mul_of_nonneg_left _ zero_lt_two.le
  exact Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith only [circDist_nonneg 0 a,Real.pi_pos])
    (by linarith only [mul_le_mul_of_nonneg_left hx.2 Real.pi_pos.le]) (by linarith only [ha])

/-- Every diagonal center captures precisely xᴰ of all packets, at every
angular width below one turn. This attains the arbitrary-unitary bound. -/
theorem volume_diagonal_ball {I : Type*} [Fintype I] [DecidableEq I] (b : UnitAddTorus I)
    {x : ℝ} (hx : x∈Ico (0:ℝ) 1) :
    volume {z : UnitAddTorus I | ‖packet b-packet z‖≤zeroGateArcTolerance x} =
      ENNReal.ofReal x^Fintype.card I := by
  have hbc : packet b∈unitary (Matrix I I ℂ) := StaticLocalLaboratoryComplexityGrowthLaw.mem_unitaryGroup_diagonal_general _ (fun _ => Circle.norm_coe _)
  apply le_antisymm (volume_fixed_unitary_ball hbc hx)
  let W (i : I) := (fun u : UnitAddCircle => u+(((x/2:ℝ):UnitAddCircle)-b i)) ⁻¹' forwardUnitArc x
  have hm (i : I) : volume (W i)=ENNReal.ofReal x := by
    exact ((measurePreserving_add_right volume _).measure_preimage
      (isClosed_forwardUnitArc x).measurableSet.nullMeasurableSet).trans (volume_forwardUnitArc_full ⟨x,hx.1,hx.2.le⟩)
  have hp : volume (univ.pi W)=ENNReal.ofReal x^Fintype.card I := by
    rw [volume_pi_pi]
    simp only [hm,Finset.prod_const,Finset.card_univ]
  rw [←hp]
  apply measure_mono
  intro z hz
  change ‖packet b-packet z‖≤_
  unfold packet
  rw [Matrix.diagonal_sub,Matrix.l2_opNorm_diagonal]
  have hnon := strictMonoOn_zeroGateArcTolerance_full.monotoneOn
    (show (0:ℝ)∈Icc (0:ℝ) 1 from ⟨le_rfl,zero_le_one⟩) ⟨hx.1,hx.2.le⟩ hx.1
  apply (pi_norm_le_iff_of_nonneg (show 0≤zeroGateArcTolerance x by simpa only
    [zeroGateArcTolerance,mul_zero,zero_div,Real.sin_zero] using hnon)).mpr
  intro i
  obtain ⟨t,ht,he⟩ := hz i (mem_univ _)
  change (t:UnitAddCircle)=z i+(((x/2:ℝ):UnitAddCircle)-b i) at he
  have hrew : z i=b i+((t-x/2:ℝ):UnitAddCircle) := by
    rw [AddCircle.coe_sub,he]
    abel
  change ‖((b i).toCircle:ℂ)-((z i).toCircle:ℂ)‖≤_
  rw [hrew]
  exact chord_upper _ ⟨hx.1,hx.2.le⟩ (abs_le.mpr ⟨by linarith only [ht.1],by linarith only [ht.2]⟩)

#print axioms volume_diagonal_ball
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
