import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.SingleCut.HalfBudget

/-! # Gate budget for two half-chains sharing the central spin -/
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open WeakBonds.SingleCut
open private polynomial_room from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.SingleCut.HalfBudget

/-- Both incident edges exist. Counting the central spin twice still
leaves half of the near-Hilbert budget available at the first crossing. -/
theorem affordable_middle_spin (n : ℕ) (hn : 64≤n+2) :
    ∃ a b : Fin (n+1), a.succ=b.castSucc ∧ 2≤(Finset.Iic a.succ).card ∧
      2≤(Finset.Ici a.succ).card ∧
      2*(blockCost (Finset.Iic a.succ).card+blockCost (Finset.Ici a.succ).card)≤
        nearHilbertContinuousCircuitBudget (n+2) := by
  let h := (n+2)/2
  have hh : 32≤h := by dsimp only [h]; omega
  have hlo : 2*h≤n+2 := by dsimp only [h]; omega
  have hhi : n+2≤2*h+1 := by dsimp only [h]; omega
  let a : Fin (n+1) := ⟨h-1,by omega⟩
  let b : Fin (n+1) := ⟨h,by omega⟩
  have hv : a.succ.val=h := by change h-1+1=h; omega
  have hl : (Finset.Iic a.succ).card=h+1 := by rw [Fin.card_Iic,hv]
  have hr : (Finset.Ici a.succ).card=n+2-h := by rw [Fin.card_Ici,hv]
  refine ⟨a,b,Fin.ext hv,by omega,by omega,?_⟩
  apply (Nat.le_div_iff_mul_le (by positivity : 0<64*(n+2+1))).mpr
  have cost (k : ℕ) (hk : k≤h+1) : blockCost k≤2^(h+1)*(2*(h+1)+1) :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hk) (by omega)
  have hs := Nat.add_le_add (cost _ hl.le) (cost _ (by omega : (Finset.Ici a.succ).card≤h+1))
  calc
    _ ≤ 2*(2^(h+1)*(2*(h+1)+1)+2^(h+1)*(2*(h+1)+1))*(64*(2*h+1+1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hs) (Nat.mul_le_mul_left _ (by omega))
    _ ≤ (4096*(h+2)^2)*2^h := by
      rw [pow_succ]; nlinarith only [Nat.zero_le (2^h),Nat.zero_le (h*2^h),Nat.zero_le (h^2*2^h)]
    _ ≤ 2^h*2^h := Nat.mul_le_mul_right _ (polynomial_room h hh)
    _ = 2^(2*h) := by rw [←pow_add,two_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hlo

#print axioms affordable_middle_spin
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
