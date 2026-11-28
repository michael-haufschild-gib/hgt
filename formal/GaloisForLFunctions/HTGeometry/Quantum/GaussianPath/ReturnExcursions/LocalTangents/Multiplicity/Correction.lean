import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.LocalTangents.Multiplicity.Residual
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.LocalTangents.Multiplicity.ActiveSpan
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.LocalTangents.Multiplicity.PauliSweep

/-! # Strict improvement with a number of gates controlled by active multiplicity -/

open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.LocalTangents.Multiplicity
open AccuracyScales.TenthPlateau
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

private theorem strict_generator {N : ℕ} (U V : unitary (Reg N))
    (hpos : 0<‖U.val-V.val‖) (hcut : ‖U.val-V.val‖<2) :
    ∃ B : selfAdjoint (Reg N), ‖U.val-V.val-(Complex.I • B.val)*V.val‖<‖U.val-V.val‖ := by
  obtain ⟨B,hB⟩ := relative_affine_correction (I:=Fin N → Bool) U V
  exact ⟨B,hB.trans_lt (by nlinarith only [mul_lt_mul_of_pos_left hcut hpos])⟩

private theorem act_neg {N : ℕ} (A : Reg N) (ψ : EuclideanSpace ℂ (Fin N → Bool)) :
    matAct (-A) ψ= -matAct A ψ :=
  WithLp.ofLp_injective 2 (Matrix.neg_mulVec ψ.ofLp A)

/-- Exact agreement of the compressed readings preserves strict descent
after any prescribed quadratic simulation error. -/
private theorem sparse_descent {N : ℕ} (X Q : Reg N) (hX : 0<‖X‖)
    (B : selfAdjoint (Reg N)) (hB : ‖X-(Complex.I • B.val)*Q‖<‖X‖) :
    ∃ d ≤ (activeRank X)^2, ∃ (w : Fin d → Fin N → Option (Fin 3)) (a : Fin d → ℝ),
      let L := ∑ i, a i • finitePauliSelfAdjoint (w i)
      ∀ M : ℝ, ∃ r>(0:ℝ), ‖X-(r:ℂ) • ((Complex.I • L.val)*Q)‖+M*r^2<‖X‖ := by
  obtain ⟨d,hd,w,a,hh⟩ := sparse_active_readings (N:=N) X Q B
  refine ⟨d,hd,w,a,?_⟩
  intro L M
  let T : Reg N := (Complex.I • B.val)*Q
  let S : Reg N := (Complex.I • L.val)*Q
  have hgain : ‖X + -T‖<‖X‖ := by simpa only [sub_eq_add_neg] using hB
  have hmatch (ψ) (hψ : ψ∈maxRightSingularSphere X) :
      (inner ℂ (matAct X ψ) (matAct (-S) ψ)).re=(inner ℂ (matAct X ψ) (matAct (-T) ψ)).re := by
    simp only [act_neg,inner_neg_right,Complex.neg_re,neg_inj]
    exact hh ψ hψ
  obtain ⟨r,hr,h⟩ := matched_descent (N:=N) X (-T) (-S) hX hgain hmatch M
  exact ⟨r,hr,by simpa only [smul_neg,sub_eq_add_neg] using h⟩

private theorem transfer_gain {A : Type*} [NormedAddCommGroup A] (U Q Z W : A) {b e : ℝ}
    (h : ‖U-Q-Z‖+b<e) (hfit : ‖Q+Z-W‖≤b) : ‖U-W‖<e := by
  apply (norm_sub_le_norm_sub_add_norm_sub U (Q+Z) W).trans_lt
  rw [←sub_sub]
  exact (add_le_add le_rfl hfit).trans_lt h

/-- Every positive error below two admits strict improvement by at most
(2N+1)r² additional physical two-qubit gates, where r is the complex
dimension of the span of all norming input vectors for this residual. -/
theorem rank_correction {N : ℕ} (hn : 2≤N) (U : unitary (Reg N)) (C : TwoQubitCircuit N)
    {v : ℂ} (hv : ‖v‖=1) :
    let Q := v • C.eval.val
    let X := U.val-Q
    0<‖X‖ → ‖X‖<2 → ∃ D : TwoQubitCircuit N, D.gateCount≤C.gateCount+(activeRank X)^2*(2*N+1) ∧
      ∃ z : ℂ, ‖z‖=1 ∧ ‖U.val-z • D.eval.val‖<‖X‖ := by
  intro Q X hX hcut
  have hvu : v∈unitary ℂ := by
    have h : star v*v=1 := by rw [Complex.star_def,Complex.conj_mul',hv]; norm_num
    exact Unitary.mem_iff.mpr ⟨h,(mul_comm ..).trans h⟩
  let V : unitary (Reg N) := ⟨Q,Unitary.smul_mem_of_mem hvu C.eval.2⟩
  obtain ⟨B,hB⟩ := strict_generator (N:=N) U V hX hcut
  obtain ⟨d,hd,w,a,hs⟩ := sparse_descent (N:=N) X Q hX B hB
  obtain ⟨M,_,hsweep⟩ := sparse_sweep (n:=N) hn w a C hv
  obtain ⟨r,_,hr⟩ := hs M
  obtain ⟨D,hD,z,hz,hfit⟩ := hsweep r
  exact ⟨D,hD.trans (Nat.add_le_add_left (Nat.mul_le_mul_right (2*N+1) hd) C.gateCount),
    z,hz,transfer_gain U.val Q _ (z • D.eval.val) hr hfit⟩

#print axioms rank_correction
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.LocalTangents.Multiplicity
