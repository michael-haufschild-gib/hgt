import GaloisForLFunctions.HTGeometry.ProjectiveOperatorNormReturnTarget
import GaloisForLFunctions.HTGeometry.FidelityPhaseRadius
import GaloisForLFunctions.HTGeometry.UniformProjectiveContinuousCircuitFirstReturnLaw
import GaloisForLFunctions.HTGeometry.ProjectiveContinuousCircuitConeLaw
import GaloisForLFunctions.HTGeometry.ContinuousPlateauGrid

/-!
# A delayed first entrance to the physical circuit set

A simultaneous Dirichlet return of the anchored eigenphases gives a literal
operator-norm approximation by the empty circuit. Compactness supplies the
first entrance to the full circuit budget after any prescribed time.
-/

open Set Topology
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry
noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

private theorem chord_le_of_turns_close (x : ℝ) (Q : ℕ)
    (h : latticeClose (x/(2*Real.pi)) (1/(Q+1 : ℝ))) :
    ‖Complex.exp (-(Complex.I*(x : ℂ))) - 1‖ ≤ 2*Real.pi/(Q+1:ℝ) := by
  obtain ⟨m,hm⟩ := h
  rw [norm_exp_neg_I_mul_sub_one, mul_comm Complex.I]
  have hc := norm_expI_sub_expI_le x 0 m
  simp only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,sub_zero] at hc
  have hpi : 0 < 2*Real.pi := by positivity
  apply hc.trans
  rw [show x-2*Real.pi*m = 2*Real.pi*(x/(2*Real.pi)-m) by field_simp; ring,
    abs_mul,abs_of_pos hpi]
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hm.le hpi.le

/-- After any specified time A, one multiple of |A|+1 returns the whole
operator up to phase, with the Dirichlet exponent equal to the number of
relative phases. No spectral genericity is required. -/
theorem projective_operator_zero_gate_return_after {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d+1)) (H : selfAdjoint (Reg n)) (A : ℝ) (Q : ℕ) :
    ∃ t ∈ Icc (|A|+1) ((|A|+1)*((Q+1:ℝ)^d)),
      HasProjectiveCircuitApproximation n (2*Real.pi/(Q+1:ℝ)) 0 (unitaryEvolution (H : Reg n) t) := by
  let E := H.2.isHermitian.eigenvalues
  let a := e.symm 0
  let tick := |A|+1
  let β (j : Fin d) := tick*(E (e.symm j.succ)-E a)/(2*Real.pi)
  obtain ⟨q,hq,hQ,hb⟩ := exists_simultaneous_dirichlet β (Nat.succ_pos Q)
  let t := tick*q
  have htick : 0 < tick := by dsimp [tick]; positivity
  have h1 : (1:ℝ) ≤ q := by exact_mod_cast hq
  have h2 : (q:ℝ) ≤ (Q+1:ℝ)^d := by exact_mod_cast hQ
  refine ⟨t,⟨?_,mul_le_mul_of_nonneg_left h2 htick.le⟩,?_⟩
  · change tick ≤ tick*q
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h1 htick.le
  refine ⟨anchorPhase E a t,by simp [anchorPhase,Complex.norm_exp],TwoQubitCircuit.one n,by rfl,?_⟩
  rw [TwoQubitCircuit.one_eval]
  change ‖unitaryEvolution (H : Reg n) t - anchorPhase E a t • (1:Reg n)‖ ≤ _
  rw [l2_opNorm_unitaryEvolution_sub_anchorPhase H.2.isHermitian a t]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2*Real.pi/(Q+1:ℝ))).mpr
  intro i
  let x := t * (E i-E a)
  have he : -(Complex.I * ((t:ℂ) * ((E i:ℂ)-(E a:ℂ)))) = -(Complex.I*(x:ℂ)) := by
    dsimp [x]; push_cast; rfl
  change ‖Complex.exp (-(Complex.I*((t:ℂ)*((E i:ℂ)-(E a:ℂ))))) - 1‖ ≤ _
  rw [he]
  apply chord_le_of_turns_close x Q
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  refine Fin.cases ?_ (fun k => ?_) j
  · refine ⟨0,?_⟩
    simp [x,a]
    positivity
  · have h := hb k
    have hz : t*(E (e.symm k.succ)-E a)/(2*Real.pi) = (q:ℝ)*β k := by dsimp [t,β]; ring
    change latticeClose (t*(E (e.symm k.succ)-E a)/(2*Real.pi)) _
    rw [hz]
    simpa only [Nat.cast_add,Nat.cast_one] using h

private theorem closed_physical_circuit_hits {n : ℕ} (H : selfAdjoint (Reg n)) (s : ℕ) (ε : ℝ) :
    IsClosed {t | HasProjectiveCircuitApproximation n ε s (unitaryEvolution (H : Reg n) t)} := by
  let K := phaseCircuitMatrixImageAtMost n s
  have hK := isCompact_phaseCircuitMatrixImageAtMost n s
  have hne := phaseCircuitMatrixImageAtMost_nonempty n s
  have hL : LipschitzWith ⟨‖(H : Reg n)‖,norm_nonneg _⟩ (unitaryEvolution (H : Reg n)) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    change dist (unitaryEvolution (H : Reg n) u) (unitaryEvolution H v) ≤ ‖(H : Reg n)‖ * dist u v
    rw [dist_eq_norm, Real.dist_eq]
    exact norm_unitaryEvolution_time_sub_le H.2 u v
  have heq (t : ℝ) : HasProjectiveCircuitApproximation n ε s (unitaryEvolution (H : Reg n) t) ↔
      Metric.infDist (unitaryEvolution (H : Reg n) t) K ≤ ε := by
    constructor
    · rintro ⟨c,hc,C,hC,h⟩
      have hmem : c • (C.eval : Reg n) ∈ K := mem_phaseCircuitMatrixImageAtMost_iff.mpr ⟨c,hc,C,hC,rfl⟩
      exact (Metric.infDist_le_dist_of_mem hmem).trans (by simpa only [dist_eq_norm] using h)
    · intro h
      obtain ⟨U,hU,hd⟩ := exists_compactTarget_minDist hK hne (unitaryEvolution (H : Reg n) t)
      obtain ⟨c,hc,C,hC,rfl⟩ := mem_phaseCircuitMatrixImageAtMost_iff.mp hU
      exact ⟨c,hc,C,hC,by rwa [← hd,dist_eq_norm] at h⟩
  simp only [heq]
  exact isClosed_compactTargetCaptureTimeSet _ hL.continuous K ε

/-- The first visit at or after A to the complete s-gate set at error 1/10
is attained and has an explicit upper deadline, including for A determined
by the Hamiltonian. -/
theorem projective_first_circuit_visit_deadline {n d : ℕ}
    (e : (Fin n → Bool) ≃ Fin (d+1)) (H : selfAdjoint (Reg n)) (A : ℝ) (s : ℕ) :
    ∃ v ∈ Icc A ((|A|+1)*(100:ℝ)^d),
      HasProjectiveCircuitApproximation n (1/10:ℝ) s (unitaryEvolution (H : Reg n) v) ∧
      ∀ t ∈ Ico A v, ProjectiveCircuitSeparated n (1/10:ℝ) s (unitaryEvolution (H : Reg n) t) := by
  let E := {t | HasProjectiveCircuitApproximation n (1/10:ℝ) s (unitaryEvolution (H : Reg n) t)}
  let B := (|A|+1)*(100:ℝ)^d
  have hcomp : IsCompact (Icc A B ∩ E) :=
    isCompact_Icc.inter_right (closed_physical_circuit_hits H s _)
  obtain ⟨u,hu,c,hc,C,hC,h⟩ := projective_operator_zero_gate_return_after e H A 99
  have huB : u ≤ B := by simpa only [B, show (99+1:ℝ)=100 by norm_num] using hu.2
  have heasy : u ∈ E := by
    refine ⟨c,hc,C,by omega,h.trans ?_⟩
    have hp := Real.pi_lt_four
    linarith
  have hne : (Icc A B ∩ E).Nonempty :=
    ⟨u,⟨by linarith only [le_abs_self A,hu.1],huB⟩,heasy⟩
  obtain ⟨v,hv,hmin⟩ := hcomp.exists_isMinOn hne continuous_id.continuousOn
  refine ⟨v,hv.1,hv.2,?_⟩
  intro t ht c hc C hC
  by_contra! h
  have htE : t ∈ E := ⟨c,hc,C,hC,h⟩
  have hvle := hmin (show t ∈ Icc A B ∩ E from ⟨⟨ht.1,ht.2.le.trans hv.1.2⟩,htE⟩)
  exact (not_le_of_gt ht.2) hvle

#print axioms projective_first_circuit_visit_deadline
end
end GaloisForLFunctions.HTGeometry
