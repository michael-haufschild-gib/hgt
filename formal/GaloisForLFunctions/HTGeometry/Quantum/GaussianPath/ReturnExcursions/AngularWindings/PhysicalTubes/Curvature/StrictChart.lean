import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.Curvature.StrictMidpoint
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.Chart

/-! # Strict interpolation of lifted phases with distinct clock velocities -/

open Matrix Real Set
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
open private cis cis_add from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.Chart
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- If at most one lifted coordinate agrees at both endpoints, the midpoint
strictly improves the common positive tolerance after a scalar rotation. -/
theorem strict_angle_midpoint (W : unitary (Mat I)) (a b : I → ℝ) {ε : ℝ}
    (he : 0<ε) (hcut : ε^2<2) (hab : ∀ i, |b i-a i|≤π)
    (hfixed : ∀ i j, b i=a i → b j=a j → i=j)
    (ha : ‖(anglePacket a).val-W.val‖≤ε) (hb : ‖(anglePacket b).val-W.val‖≤ε) :
    ∃ δ : ℝ, ‖(anglePacket fun i => (a i+b i)/2+δ).val-W.val‖<ε := by
  let θ (i : I) := (a i+b i)/2
  let d (i : I) := (b i-a i)/2
  let M := anglePacket θ
  let V := M⁻¹*W
  have hMV : M.val*V.val=W.val := congrArg Subtype.val (mul_inv_cancel_left M W)
  have hleft (Z : Mat I) : ‖Z-V.val‖=‖M.val*Z-W.val‖ := by
    rw [←CStarRing.norm_mem_unitary_mul (Z-V.val) M.2,mul_sub,hMV]
  have hprod (g : I → ℝ) : M.val*(anglePacket g).val=(anglePacket fun i => θ i+g i).val := by
    change Matrix.diagonal (fun i => cis (θ i))*Matrix.diagonal (fun i => cis (g i))=
      Matrix.diagonal (fun i => cis (θ i+g i))
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    exact (cis_add _ _).symm
  have hconj (i : I) : conj (cis (d i))=cis (-d i) := by
    dsimp only [cis]
    rw [←Complex.exp_conj]
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_neg,mul_neg,neg_mul]
  have hpos (i : I) : 0≤(cis (d i)).re := by
    rw [Complex.exp_ofReal_mul_I_re]
    have hh := abs_le.mp (hab i)
    apply cos_nonneg_of_neg_pi_div_two_le_of_le <;> dsimp only [d] <;> linarith only [hh.1,hh.2]
  have hplus : (fun i => θ i+d i)=b := funext fun i => by dsimp only [θ,d]; ring
  have hminus : (fun i => θ i+ -d i)=a := funext fun i => by dsimp only [θ,d]; ring
  have hzero (i : I) (hi : (cis (d i)).re=1) : b i=a i := by
    have hd : |d i|≤π := by
      dsimp only [d]
      rw [abs_div,abs_of_pos zero_lt_two]
      linarith only [hab i,pi_pos]
    have hc : cos |d i|=cos 0 := by rwa [cos_abs,cos_zero,←Complex.exp_ofReal_mul_I_re]
    have h₀ := injOn_cos (show |d i|∈Icc (0:ℝ) π from ⟨abs_nonneg _,hd⟩)
      (show (0:ℝ)∈Icc 0 π from ⟨le_rfl,pi_pos.le⟩) hc
    have hz := abs_eq_zero.mp h₀
    dsimp only [d] at hz
    linarith only [hz]
  obtain ⟨c,hc,hfit⟩ := strict_projective_midpoint V (fun i => cis (d i))
    (fun _ => Complex.norm_exp_ofReal_mul_I _) hpos (fun i j hi hj => hfixed i j (hzero i hi) (hzero j hj))
    he hcut (by change ‖(anglePacket d).val-V.val‖≤ε; rwa [hleft,hprod,hplus])
    (by simp only [hconj]; change ‖(anglePacket (fun i => -d i)).val-V.val‖≤ε; rwa [hleft,hprod,hminus])
  have hz : cis c.arg=c := by
    simpa only [hc,Complex.ofReal_one,one_mul] using Complex.norm_mul_exp_arg_mul_I c
  have hscalar : (anglePacket fun _ : I => c.arg).val=c • (1 : Mat I) := by
    change Matrix.diagonal (fun _ : I => cis c.arg)=c • (1 : Mat I)
    rw [hz,←Matrix.diagonal_one,←Matrix.diagonal_smul]
    congr 1
    funext i
    exact (mul_one c).symm
  refine ⟨c.arg,?_⟩
  rwa [←hscalar,hleft,hprod] at hfit

#print axioms strict_angle_midpoint
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
