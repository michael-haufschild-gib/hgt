import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Frames.CircuitFit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.CutMass

/-! # All nine coupling directions across one gate-respecting cut -/

open Matrix Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
noncomputable section
variable {n : ℕ}

/-- The same gate-respecting cut passes the half-turn test for every
choice of one Pauli axis per site. Choices may depend on the circuit
and on all the coupling coefficients. -/
theorem every_frame_cut (u : PathShell n) (C : TwoQubitCircuit (n+2)) (c : Cut C)
    (t : ℝ) (z : ℂ) (hz : ‖z‖=1)
    (hc : ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖≤1/4)
    (ht : |t| * ‖u‖≤1/100) (a : Fin (n+2)→Fin 3) :
    4 * |t| * (∑ e∈crossed c, |u (.inr (e,a e.castSucc,a e.succ))|)<π := by
  obtain ⟨T,hT⟩ := frame_preserves_fit a u C t z
  let D : TwoQubitCircuit (n+2) := ⟨C.gateCount,C.architecture,T⟩
  let c' : Cut D := ⟨c.val,c.property⟩
  have hs : crossed c'=crossed c := by
    ext i
    simp only [mem_crossed_iff,c']
  by_contra! h
  have hm : π≤4 * |t| * (∑ e∈crossed c', |rotatedShell a u (.inr (e,2,2))|) := by
    simpa only [rotatedShell_longitudinal,hs] using h
  have h₂ := half_turn_error (rotatedShell a u) D c' t z hz hm
  rw [hT,rotatedShell_norm] at h₂
  have h₃ : sqrt 21≤5 := sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have hb := mul_le_mul (show 8+4*sqrt 21≤28 by linarith only [h₃]) ht
    (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (by norm_num)
  linarith only [h₂,hb,hc]

/-- At most a fixed total Pauli mass can cross any disconnected circuit
cut at short time. The gate deficit forces at least half as many crossed
bonds, counting all axes on each bond. -/
theorem all_axes_sparse_cut (u : PathShell n) (C : TwoQubitCircuit (n+2))
    (t : ℝ) (z : ℂ) (hz : ‖z‖=1)
    (hc : ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖≤1/4)
    (ht : |t| * ‖u‖≤1/100) :
    ∃ c : Cut C, n+1≤C.gateCount+2*(crossed c).card ∧
      4 * |t| * (∑ e∈crossed c, ∑ ab : Fin 3×Fin 3, |u (.inr (e,ab))|)<9*π := by
  obtain ⟨c,hc'⟩ := many_crossed C
  refine ⟨c,hc',?_⟩
  let a (p : Fin 3×Fin 3) (v : Fin (n+2)) := if v.val%2=0 then p.1 else p.2
  have hrow (e : Fin (n+1)) :
      (∑ p, |u (.inr (e,a p e.castSucc,a p e.succ))|)=∑ p, |u (.inr (e,p))| := by
    by_cases h : e.val%2=0
    · have h' : (e.val+1)%2≠0 := by omega
      simp [a,h,h']
    · have h' : (e.val+1)%2=0 := by omega
      simpa only [a,Fin.val_castSucc,Fin.val_succ,if_neg h,if_pos h',Equiv.prodComm_apply,Prod.swap] using
        (Equiv.prodComm (Fin 3) (Fin 3)).sum_comp (fun p => |u (.inr (e,p))|)
  have h := sum_lt_sum_of_nonempty (s:=univ) univ_nonempty (fun p _ => every_frame_cut u C c t z hz hc ht (a p))
  rw [←mul_sum,sum_comm] at h
  simp_rw [hrow] at h
  simpa only [sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_mul,Nat.cast_ofNat,show (3:ℝ)*3=9 by norm_num] using h

#print axioms every_frame_cut
#print axioms all_axes_sparse_cut
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
