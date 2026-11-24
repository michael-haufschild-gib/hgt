import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.AbsoluteCoordinates
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.HaarBound
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.CircuitNet
import GaloisForLFunctions.HTGeometry.PhaseGridApproximation

/-! # Short-circuit phase volume at every operator tolerance below two -/
open Set MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
noncomputable section

private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

private def gridPhase {m : ℕ} (i : Fin m) := Complex.exp ((gridAngle m i:ℝ) * Complex.I)

private theorem phase_near {m : ℕ} (hm : 0 < m) (c : ℂ) (hc : ‖c‖=1) :
    ∃ i : Fin m, ‖c-gridPhase i‖≤2*Real.pi/m := by
  obtain ⟨i,hi⟩ := exists_gridIndex hm c.arg
  have he : Complex.exp ((c.arg:ℂ)*Complex.I)=c := by
    simpa only [hc,Complex.ofReal_one,one_mul] using Complex.norm_mul_exp_arg_mul_I c
  exact ⟨i,by simpa only [mul_neg_one,neg_neg,he,gridPhase] using hi (-1) (by norm_num)⟩

private theorem phase_unitary {I : Type*} [Fintype I] [DecidableEq I] (U : unitaryGroup I ℂ)
    (c : ℂ) (hc : ‖c‖=1) : c • (U : Matrix I I ℂ) ∈ unitary (Matrix I I ℂ) := by
  have hc' : conj c*c=1 := by rw [Complex.conj_mul',hc]; norm_num
  apply Unitary.mem_iff.mpr
  constructor <;> simp [star_smul,smul_smul,(Unitary.mem_iff.mp U.2).1,
    (Unitary.mem_iff.mp U.2).2,hc',mul_comm c (conj c)]

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

/-- An internal circuit net and m scalar phases suffice. Each enlarged
fixed-center tube costs at most yᴰ, for every y between zero and one. -/
theorem circuit_volume_bound {N d : ℕ} (e : (Fin N → Bool) ≃ Fin (d+1))
    (V : unitaryGroup (Fin N → Bool) ℂ) (s m : ℕ) (hm : 0 < m)
    {ε η y : ℝ} (hη : 0<η) (hy : y∈Ico (0:ℝ) 1)
    (hprice : ε+η+2*Real.pi/m≤zeroGateArcTolerance y) :
    volume.real (projectiveContinuousCircuitCaptureTarget e V s ε) ≤
      (m:ℝ)*(((s:ℝ)+1)*(((N+1:ℝ)^2)*(1+4*(s:ℝ)/η)^32)^s)*y^(2^N) := by
  classical
  obtain ⟨F,hF,hcard⟩ := exists_budget_net N s η hη
  let P := Fin m × ↥F
  let U (W : unitaryGroup (Fin N → Bool) ℂ) := V⁻¹*W*V
  let K (p : P) : Reg N := gridPhase p.1 • ((U p.2.val):Reg N)
  let A (p : P) := {z : UnitAddTorus (Fin N → Bool) | ‖K p-packet z‖≤zeroGateArcTolerance y}
  have hC (p : P) := phase_unitary (U p.2.val) (gridPhase p.1) (Complex.norm_exp_ofReal_mul_I _)
  have hv (p : P) : volume.real (A p)≤y^(2^N) := by
    have h := volume_fixed_unitary_ball (hC p) hy
    exact (ENNReal.toReal_mono (by finiteness) h).trans_eq (by
      rw [ENNReal.toReal_pow,ENNReal.toReal_ofReal hy.1,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin])
  let B := projectiveContinuousCircuitCaptureTarget e V s ε
  have hsub : (anchorMap e) ⁻¹' B ⊆ ⋃ p : P, A p := by
    intro z hz
    obtain ⟨c,hc,C,hCs,hfit⟩ := (mem_projectiveContinuousCircuitCaptureTarget_iff ..).mp hz
    obtain ⟨W,hW,hn⟩ := hF C hCs
    let q : ℂ := (z (e.symm 0)).toCircle
    have hq : ‖q‖=1 := Circle.norm_coe _
    have hg : ‖projectiveSpectralMatrix e V (anchorMap e z)-c • (W:Reg N)‖ ≤ ε+η := by
      apply (norm_sub_le_norm_sub_add_norm_sub _ (c • (C.eval:Reg N)) _).trans
      rw [←smul_sub,norm_smul,hc,one_mul]
      exact add_le_add hfit hn
    have hW' : (V:Reg N)*((U W):Reg N)*star (V:Reg N)=(W:Reg N) := by
      change ((V*(U W)*V⁻¹ : unitaryGroup (Fin N → Bool) ℂ):Reg N)=(W:Reg N)
      simp [U,mul_assoc]
    have hh : ‖packet z-(q*c) • ((U W):Reg N)‖≤ε+η := by
      rw [←l2_opNorm_unitary_conj_eq V.2,Matrix.mul_sub,Matrix.sub_mul,absolute_packet,
        Matrix.mul_smul,Matrix.smul_mul,hW',←smul_smul,←smul_sub,norm_smul,hq,one_mul]
      exact hg
    obtain ⟨i,hi⟩ := phase_near hm (q*c) (by rw [norm_mul,hq,hc,one_mul])
    let p : P := (i,⟨W,hW⟩)
    apply mem_iUnion.mpr ⟨p,?_⟩
    change ‖gridPhase i • ((U W):Reg N)-packet z‖≤zeroGateArcTolerance y
    rw [norm_sub_rev]
    apply (norm_sub_le_norm_sub_add_norm_sub _ ((q*c) • ((U W):Reg N)) _).trans
    rw [←sub_smul,norm_smul,CStarRing.norm_of_mem_unitary (U W).property,mul_one]
    exact (add_le_add hh hi).trans hprice
  have hB : MeasurableSet B := (isClosed_projectiveContinuousCircuitCaptureTarget ..).measurableSet
  rw [←(anchor_preserving e).measureReal_preimage hB.nullMeasurableSet]
  apply ((measureReal_mono hsub).trans (measureReal_iUnion_fintype_le A)).trans
  apply (Finset.sum_le_sum (s:=Finset.univ) fun p _ => hv p).trans
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,P,Fintype.card_prod,Fintype.card_fin,
    Fintype.card_coe,Nat.cast_mul]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg m)) (pow_nonneg hy.1 _)

#print axioms circuit_volume_bound
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
