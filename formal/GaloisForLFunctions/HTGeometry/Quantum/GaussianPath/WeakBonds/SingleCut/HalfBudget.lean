import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.SingleCut.CutPackets
import GaloisForLFunctions.HTGeometry.NearHilbertContinuousCircuitEntropyLaw

/-! # Diagonal synthesis on both halves fits below half the crossing budget -/
namespace GaloisForLFunctions.HTGeometry.WeakBonds.SingleCut

private theorem polynomial_room (h : ℕ) (hh : 32 ≤ h) : 4096*(h+2)^2 ≤ 2^h := by
  induction h,hh using Nat.le_induction with
  | base => norm_num
  | succ h hh ih =>
    have hs : (h+1+2)^2 ≤ 2*(h+2)^2 := by nlinarith only [hh,Nat.zero_le (h^2)]
    calc _ ≤ 4096*(2*(h+2)^2) := Nat.mul_le_mul_left _ hs
         _ = 4096*(h+2)^2*2 := by ring
         _ ≤ 2^h*2 := Nat.mul_le_mul_right 2 ih
         _ = _ := (pow_succ _ _).symm

/-- One central edge leaves two blocks each requiring only its
diagonal phase budget in the all-time neighborhood. -/
theorem affordable_middle_edge (n : ℕ) (hn : 64 ≤ n+2) :
    ∃ a : Fin (n+1), 2 ≤ (leftBlock a).card ∧ 2 ≤ (rightBlock a).card ∧
      2*(blockCost (leftBlock a).card+blockCost (rightBlock a).card) ≤ nearHilbertContinuousCircuitBudget (n+2) := by
  let h := (n+2)/2
  have hh : 32 ≤ h := by dsimp [h]; omega
  have hlo : 2*h ≤ n+2 := by dsimp [h]; omega
  have hhi : n+2 ≤ 2*h+1 := by dsimp [h]; omega
  let a : Fin (n+1) := ⟨h-1,by omega⟩
  have hl : (leftBlock a).card=h := by rw [leftBlock,Fin.card_Iic]; change h-1+1=h; omega
  have hr : (rightBlock a).card=n+2-h := by rw [rightBlock,Fin.card_Ioi]; change n+2-1-(h-1)=_; omega
  refine ⟨a,by omega,by omega,?_⟩
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 64*(n+2+1))).mpr
  have cost (k : ℕ) (hk : k ≤ h+1) : blockCost k ≤ 2^(h+1)*(2*(h+1)+1) := by
    unfold blockCost
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hk) (by omega)
  have hsum := Nat.add_le_add (cost _ (by omega : (leftBlock a).card ≤ h+1))
    (cost _ (by omega : (rightBlock a).card ≤ h+1))
  calc
    _ ≤ 2*((2^(h+1)*(2*(h+1)+1))+(2^(h+1)*(2*(h+1)+1)))*(64*(2*h+1+1)) := by
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hsum) (Nat.mul_le_mul_left _ (by omega))
    _ ≤ (4096*(h+2)^2)*2^h := by rw [pow_succ]; nlinarith only [Nat.zero_le (2^h),Nat.zero_le (h*2^h),Nat.zero_le (h^2*2^h)]
    _ ≤ 2^h*2^h := Nat.mul_le_mul_right _ (polynomial_room h hh)
    _ = 2^(2*h) := by rw [←pow_add,two_mul]
    _ ≤ 2^(n+2) := Nat.pow_le_pow_right (by decide) hlo

#print axioms affordable_middle_edge
end GaloisForLFunctions.HTGeometry.WeakBonds.SingleCut
