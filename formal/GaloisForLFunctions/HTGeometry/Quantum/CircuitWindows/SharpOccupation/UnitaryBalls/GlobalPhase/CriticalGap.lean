import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.GlobalPhase.ProjectiveBound

/-! # Critical missing angular gap for arbitrary projective targets -/
open Set Matrix MeasureTheory Real
open scoped ENNReal Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
noncomputable section

/-- If the missing angular gap exceeds (log D+u+1)/D, capture by any
fixed unitary up to a global phase has probability at most exp(-u). -/
theorem projective_critical_gap {I : Type*} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℂ} (hC : C∈unitary (Matrix I I ℂ)) (hD : 1<Fintype.card I)
    {x u : ℝ} (hx : 0≤x) (hu : 0≤u)
    (hgap : Real.log (Fintype.card I)+u+1 ≤ (Fintype.card I:ℝ)*(1-x)) :
    volume.real (rotations {z : UnitAddTorus I | ‖C-packet z‖≤zeroGateArcTolerance x}) ≤
      Real.exp (-u) := by
  let D := Fintype.card I
  have hD' : 1<(D:ℝ) := by exact_mod_cast hD
  have hd : 0<(D:ℝ) := zero_lt_one.trans hD'
  let r := 1/(D:ℝ)
  have hr : 0<r := one_div_pos.mpr hd
  have hDr : (D:ℝ)*r=1 := mul_one_div_cancel hd.ne'
  have hlog : 0<Real.log D := Real.log_pos hD'
  change Real.log D+u+1≤(D:ℝ)*(1-x) at hgap
  have hmul : (D:ℝ)*(x+r-1) ≤ -(Real.log D)-u := by
    linarith only [hDr,hgap]
  have hy : x+r<1 := by
    by_contra! hn
    linarith only [hmul,mul_nonneg hd.le (sub_nonneg.mpr hn),hlog,hu]
  have hb := volume_projective_unitary_ball hC hx hr.le hy
  have ht := ENNReal.toReal_mono (by finiteness) hb
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hr.le,ENNReal.toReal_pow,ENNReal.toReal_ofReal (add_nonneg hx hr.le)] at ht
  let p := volume.real (rotations {z : UnitAddTorus I | ‖C-packet z‖≤zeroGateArcTolerance x})
  change r*p≤(x+r)^D at ht
  have h1 : x+r ≤ Real.exp (x+r-1) := by linarith only [Real.add_one_le_exp (x+r-1)]
  have hp := ht.trans (pow_le_pow_left₀ (add_nonneg hx hr.le) h1 D)
  rw [←Real.exp_nat_mul] at hp
  have he : Real.exp (-(Real.log D)-u)=r*Real.exp (-u) := by
    rw [sub_eq_add_neg,Real.exp_add,Real.exp_neg,Real.exp_log hd]
    rw [show r=(D:ℝ)⁻¹ from one_div _]
  exact (le_of_mul_le_mul_left (hp.trans ((Real.exp_le_exp.mpr hmul).trans_eq he)) hr)

private theorem packet_rotate {I : Type*} [Fintype I] [DecidableEq I] (z : UnitAddTorus I) (t : UnitAddCircle) :
    packet (z+(fun _ => t))=(t.toCircle:ℂ) • packet z := by
  ext i j
  by_cases hij : i=j
  · subst j
    simp only [packet,diagonal_apply_eq,Matrix.smul_apply,Pi.add_apply,AddCircle.toCircle_add,Circle.coe_mul,smul_eq_mul]
    exact mul_comm _ _
  · simp only [packet,diagonal_apply_ne _ hij,Matrix.smul_apply,smul_zero]

/-- A common rotation of the packet is exactly the scalar allowed in
projective operator error. -/
theorem rotations_iff_physical {I : Type*} [Fintype I] [DecidableEq I] (C : Matrix I I ℂ)
    (z : UnitAddTorus I) (ε : ℝ) :
    z∈rotations {w : UnitAddTorus I | ‖C-packet w‖≤ε} ↔
      ∃ c : ℂ, ‖c‖=1 ∧ ‖packet z-c • C‖≤ε := by
  constructor
  · rintro ⟨t,ht⟩
    let q : ℂ := t.toCircle
    have hq : ‖q‖=1 := Circle.norm_coe _
    have hne := norm_ne_zero_iff.mp (hq.trans_ne one_ne_zero)
    change ‖C-packet (z+(fun _ => t))‖≤ε at ht
    rw [packet_rotate] at ht
    refine ⟨q⁻¹,by rw [norm_inv,hq,inv_one],?_⟩
    have he : ‖q⁻¹ • (q • packet z-C)‖=‖q • packet z-C‖ := by rw [norm_smul,norm_inv,hq,inv_one,one_mul]
    rw [smul_sub,smul_smul,inv_mul_cancel₀ hne,one_smul] at he
    rw [he,norm_sub_rev]
    exact ht
  · rintro ⟨c,hc,hd⟩
    have hne := norm_ne_zero_iff.mp (hc.trans_ne one_ne_zero)
    have hi : ‖c⁻¹‖=1 := by rw [norm_inv,hc,inv_one]
    let v : Circle := ⟨c⁻¹,mem_sphere_zero_iff_norm.mpr hi⟩
    obtain ⟨t,ht⟩ := (AddCircle.homeomorphCircle (T:=1) one_ne_zero).surjective v
    rw [AddCircle.homeomorphCircle_apply] at ht
    refine ⟨t,?_⟩
    change ‖C-packet (z+(fun _ => t))‖≤ε
    rw [packet_rotate,ht,norm_sub_rev]
    have he : ‖c⁻¹ • (packet z-c • C)‖=‖packet z-c • C‖ := by rw [norm_smul,hi,one_mul]
    rw [smul_sub,smul_smul,inv_mul_cancel₀ hne,one_smul] at he
    exact he.trans_le hd

/-- The critical-gap bound for the literal projective operator-distance test. -/
theorem physical_critical_gap {I : Type*} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℂ} (hC : C∈unitary (Matrix I I ℂ)) (hD : 1<Fintype.card I)
    {x u : ℝ} (hx : 0≤x) (hu : 0≤u)
    (hgap : Real.log (Fintype.card I)+u+1 ≤ (Fintype.card I:ℝ)*(1-x)) :
    volume.real {z : UnitAddTorus I | ∃ c : ℂ, ‖c‖=1 ∧ ‖packet z-c • C‖≤zeroGateArcTolerance x} ≤
      Real.exp (-u) := by
  have he : rotations {z : UnitAddTorus I | ‖C-packet z‖≤zeroGateArcTolerance x} =
      {z : UnitAddTorus I | ∃ c : ℂ, ‖c‖=1 ∧ ‖packet z-c • C‖≤zeroGateArcTolerance x} :=
    Set.ext (fun z => rotations_iff_physical C z (zeroGateArcTolerance x))
  rw [←he]
  exact projective_critical_gap hC hD hx hu hgap

#print axioms physical_critical_gap
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
