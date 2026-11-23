import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ClockSpectrum.DirichletMultiples
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.SingleCut.CutPackets

/-! # Integer returns of two separated physical blocks -/
open Set Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
open WeakBonds WeakBonds.SingleCut DiagonalSynthesis
noncomputable section

private theorem add_turn_errors {a b r : ℝ} (ha : latticeClose a r) (hb : latticeClose b r) :
    latticeClose (a+b) (r+r) := by
  obtain ⟨m,hm⟩ := ha
  obtain ⟨n,hn⟩ := hb
  refine ⟨m+n,?_⟩
  rw [Int.cast_add,show a+b-((m:ℝ)+n)=(a-m)+(b-n) by ring]
  exact (abs_add_le ..).trans_lt (add_lt_add hm hn)

/-- When the spectrum lies in the sum of two finite energy lists, the
Dirichlet exponent counts both lists additively, even on the full register. -/
theorem integer_return_of_split_spectrum {N : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    (H : selfAdjoint (Register N)) (l : I → ℝ) (r : J → ℝ)
    (hE : ∀ a, ∃ i j, H.2.isHermitian.eigenvalues a=l i+r j) (t : ℝ) (Q : ℕ) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ (Q+1)^(Fintype.card I+Fintype.card J) ∧
      ‖unitaryEvolution H.val (t*q)-1‖ ≤ 4*π/(Q+1:ℝ) := by
  classical
  let f := Fintype.equivFin (I ⊕ J)
  let g (i : I ⊕ J) := t*Sum.elim l r i/(2*π)
  let β (i : Fin (Fintype.card (I ⊕ J))) := g (f.symm i)
  obtain ⟨q,hq,hle,hnear⟩ := exists_simultaneous_dirichlet β (Nat.succ_pos Q)
  refine ⟨q,hq,by simpa only [Fintype.card_sum] using hle,?_⟩
  have hh (z : I ⊕ J) : latticeClose ((q:ℝ)*g z) (1/(Q+1:ℝ)) := by
    simpa only [β,Equiv.symm_apply_apply,Nat.cast_succ] using hnear (f z)
  have hnorm := norm_evolution_sub_scalar H (t*q) 1
  rw [one_smul] at hnorm
  rw [hnorm]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0≤4*π/(Q+1:ℝ))).mpr
  intro a
  obtain ⟨i,j,he⟩ := hE a
  let x := t*(q:ℝ)*H.2.isHermitian.eigenvalues a
  have ha := add_turn_errors (hh (Sum.inl i)) (hh (Sum.inr j))
  have hx : x/(2*π)=(q:ℝ)*g (Sum.inl i)+(q:ℝ)*g (Sum.inr j) := by
    dsimp [x,g]; rw [he]; ring
  rw [←hx] at ha
  have hchord := phase_chord_of_turn_error x ha
  have hbound : ‖Complex.exp (-(Complex.I*(x:ℂ)))-1‖ ≤ 4*π/(Q+1:ℝ) :=
    hchord.trans_eq (by ring)
  simpa only [anchorPhase,x,Complex.ofReal_mul] using hbound

/-- Erasing one physical bond gives a simultaneous empty-circuit clock
whose exponent is the sum of the two block Hilbert dimensions. -/
theorem cut_integer_return {n : ℕ} (u : PathShell n) (a : Fin (n+1)) (t : ℝ) (Q : ℕ) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ (Q+1)^(2^(leftBlock a).card+2^(rightBlock a).card) ∧
      ‖unitaryEvolution (pathHamiltonianCut u a) (t*q)-1‖ ≤ 4*π/(Q+1:ℝ) := by
  let L := leftBlock a
  let R := rightBlock a
  have hdis : Disjoint L R := Finset.disjoint_left.mpr fun _ hl hr =>
    (Finset.mem_Ioi.mp hr).not_ge (Finset.mem_Iic.mp hl)
  obtain ⟨B,hB⟩ := exists_liftLocalMatrix_of_isSiteSupported (packet_supported u L)
  obtain ⟨C,hC⟩ := exists_liftLocalMatrix_of_isSiteSupported (packet_supported u R)
  have hb := isHermitian_of_isHermitian_liftLocalMatrix L (hB ▸ (packet_selfAdjoint u L).isHermitian)
  have hc := isHermitian_of_isHermitian_liftLocalMatrix R (hC ▸ (packet_selfAdjoint u R).isHermitian)
  have heq : pathHamiltonianCut u a=liftLocalMatrix L B+liftLocalMatrix R C := by
    rw [cut_eq_packets,hB,hC]
  let H : selfAdjoint (Register (n+2)) := ⟨_,isSelfAdjoint_pathHamiltonianCut u a⟩
  have hh : (liftLocalMatrix L B+liftLocalMatrix R C).IsHermitian := heq ▸ H.2.isHermitian
  have hspec := range_eigenvalues_add_liftLocalMatrix_disjoint hdis hb hc hh
  have hmatch := (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff H.2.isHermitian hh).mpr
    (congrArg Matrix.charpoly heq)
  have hs (x : Fin (n+2) → Bool) : ∃ i j, H.2.isHermitian.eigenvalues x=hb.eigenvalues i+hc.eigenvalues j := by
    have hx : hh.eigenvalues x ∈ range (fun p : LocalConfiguration (fun _ : Fin (n+2) => Bool) L ×
        LocalConfiguration (fun _ : Fin (n+2) => Bool) R => hb.eigenvalues p.1+hc.eigenvalues p.2) := by
      rw [←hspec]
      exact mem_range_self x
    obtain ⟨⟨i,j⟩,he⟩ := hx
    exact ⟨i,j,(congrFun hmatch x).trans he.symm⟩
  obtain ⟨q,hq,hbound,hfit⟩ := integer_return_of_split_spectrum H hb.eigenvalues hc.eigenvalues hs t Q
  refine ⟨q,hq,?_,hfit⟩
  simpa only [LocalConfiguration,Fintype.card_fun,Fintype.card_bool,Fintype.card_coe,L,R] using hbound

#print axioms cut_integer_return
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
