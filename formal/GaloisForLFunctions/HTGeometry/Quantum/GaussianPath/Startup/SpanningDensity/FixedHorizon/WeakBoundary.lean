import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.ThreeBlocks
import GaloisForLFunctions.HTGeometry.FiniteHorizonCStarPerturbationLaw

/-! # Local Heisenberg evolution between two weak path bonds -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
open WeakBonds
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ
local instance {N : ℕ} : CStarAlgebra (Reg N) where

/-- The error of evolving an interior observable with its own packet
Hamiltonian depends only on the two boundary interactions. -/
theorem weak_boundary_reporter {n : ℕ} (u : PathShell n) {a b : Fin (n+1)} (hab : a < b)
    (Y : Reg (n+2)) (hY : IsSiteSupported (A:=fun _ : Fin (n+2) => Bool) (middleBlock a b) Y) (t : ℝ) :
    let U := unitaryEvolution (pathHamiltonian u) t
    let V := unitaryEvolution (packet u (middleBlock a b)) t
    ‖star U*Y*U-star V*Y*V‖ ≤ 2*|t| *(‖edgePart u a‖+‖edgePart u b‖)*‖Y‖ := by
  intro U V
  let L := leftBlock a
  let M := middleBlock a b
  let R := rightBlock b
  let O := packet u L+packet u R
  let K := O+packet u M
  let W := unitaryEvolution O t
  let Z := unitaryEvolution K t
  have hd : Disjoint (L∪R) M := by
    apply Finset.disjoint_left.mpr
    intro i hi hm
    obtain ⟨hl,hr⟩ := Finset.mem_Ioc.mp hm
    rcases Finset.mem_union.mp hi with h|h
    · exact hl.not_ge (Finset.mem_Iic.mp h)
    · exact (Finset.mem_Ioi.mp h).not_ge hr
  have hO : IsSiteSupported (A:=fun _ : Fin (n+2) => Bool) (L∪R) O :=
    (IsSiteSupported.mono Finset.subset_union_left (packet_supported u L)).add
      (IsSiteSupported.mono Finset.subset_union_right (packet_supported u R))
  have hsa : IsSelfAdjoint O := (packet_selfAdjoint u L).add (packet_selfAdjoint u R)
  have hK := hsa.add (packet_selfAdjoint u M)
  have hW := unitaryEvolution_mem_unitary hsa t
  have hZ := unitaryEvolution_mem_unitary hK t
  have hU := unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian u) t
  have hfac : Z=W*V := unitaryEvolution_add_of_isSiteSupported_disjoint hd hO (packet_supported u M) t
  have hc : Commute Y W := commute_of_isSiteSupported_disjoint hd.symm hY (isSiteSupported_unitaryEvolution hO t)
  have hcancel : star W*Y*W=Y := by
    rw [mul_assoc,hc.eq,←mul_assoc,(Unitary.mem_iff.mp hW).1,one_mul]
  have hlocal : star Z*Y*Z=star V*Y*V := by
    rw [hfac,star_mul]
    calc _ = star V*(star W*Y*W)*V := by simp only [mul_assoc]
         _ = _ := by rw [hcancel]
  have hdiff : pathHamiltonian u-K=edgePart u a+edgePart u b := by
    rw [show K=packet u (leftBlock a)+packet u (middleBlock a b)+packet u (rightBlock b) by
      dsimp only [K,O,L,M,R]; abel]
    exact sub_three_packets u hab
  have hpert := norm_unitaryEvolution_sub_le _ _ (isSelfAdjoint_pathHamiltonian u) hK t
  change ‖U-Z‖ ≤ |t| *‖pathHamiltonian u-K‖ at hpert
  rw [hdiff] at hpert
  have hUZ := hpert.trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg t))
  have h := unitary_conjugation_norm_sub_le (star U) (star Z) Y (Unitary.star_mem hU) (Unitary.star_mem hZ)
  rw [star_star,star_star,←star_sub,norm_star,hlocal] at h
  exact h.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hUZ two_pos.le) (norm_nonneg Y))

#print axioms weak_boundary_reporter
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
