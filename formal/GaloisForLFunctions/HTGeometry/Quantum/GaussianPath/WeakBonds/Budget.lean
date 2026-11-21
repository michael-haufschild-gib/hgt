import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.ThreeBlocks
import GaloisForLFunctions.HTGeometry.NearHilbertContinuousCircuitEntropyLaw

/-! # Three balanced path blocks fit below half the first-crossing budget -/
open Finset
namespace GaloisForLFunctions.HTGeometry.WeakBonds
open Subregister

private theorem packetCost_mono {i j : ℕ} (h : i ≤ j) : packetCost i ≤ packetCost j := by
  unfold packetCost
  gcongr
  omega

private theorem thirds_polynomial (h : ℕ) (hh : 64 ≤ h) : 2^18*(h+3)^3 ≤ 2^h := by
  induction h,hh using Nat.le_induction with
  | base => norm_num
  | succ h hh ih =>
    have hstep : (h+1+3)^3 ≤ 2*(h+3)^3 := by nlinarith only [hh,Nat.zero_le (h^2),Nat.zero_le (h^3)]
    calc
      _ ≤ 2^18*(2*(h+3)^3) := Nat.mul_le_mul_left _ hstep
      _ = (2^18*(h+3)^3)*2 := by ring
      _ ≤ 2^h*2 := Nat.mul_le_mul_right 2 ih
      _ = _ := (pow_succ _ _).symm

private theorem three_small_cost {N h : ℕ} (hh : 64 ≤ h) (hlo : 3*h ≤ N) (hhi : N ≤ 3*h+2) :
    6*packetCost (h+2) ≤ nearHilbertContinuousCircuitBudget N := by
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 64*(N+1))).2
  have hp : (2^(h+2):ℕ)^2 = 16*2^(2*h) := by
    rw [←pow_mul,show (h+2)*2=4+2*h by omega,pow_add,show (2:ℕ)^4=16 by norm_num]
  calc
    _ = 6144*((4*(h+2)+1)*(2*(h+2)+2)*(N+1))*2^(2*h) := by unfold packetCost; rw [hp]; ring
    _ ≤ 6144*((4*(h+3))*(2*(h+3))*(3*(h+3)))*2^(2*h) := by gcongr <;> omega
    _ ≤ (2^18*(h+3)^3)*2^(2*h) := by
      apply Nat.mul_le_mul_right
      calc
        _ = 147456*(h+3)^3 := by ring
        _ ≤ 2^18*(h+3)^3 := Nat.mul_le_mul_right _ (by norm_num)
    _ ≤ 2^h*2^(2*h) := Nat.mul_le_mul_right _ (thirds_polynomial h hh)
    _ = 2^(3*h) := by rw [←pow_add,show h+2*h=3*h by omega]
    _ ≤ 2^N := Nat.pow_le_pow_right (by decide) hlo

/-- Cut just after one third and two thirds of the sites. The retained
full-register operator then costs at most half the near-Hilbert budget. -/
theorem exists_affordable_cuts (n : ℕ) (hn : 192 ≤ n+2) :
    ∃ a b : Fin (n+1), a < b ∧
      2 ≤ (leftBlock a).card ∧ 2 ≤ (middleBlock a b).card ∧ 2 ≤ (rightBlock b).card ∧
      2*(packetCost (leftBlock a).card + packetCost (middleBlock a b).card + packetCost (rightBlock b).card)
        ≤ nearHilbertContinuousCircuitBudget (n+2) := by
  let h := (n+2)/3
  have hh : 64 ≤ h := by dsimp [h]; omega
  have hl : 3*h ≤ n+2 := by dsimp [h]; omega
  have hu : n+2 ≤ 3*h+2 := by dsimp [h]; omega
  let a : Fin (n+1) := ⟨h-1,by omega⟩
  let b : Fin (n+1) := ⟨2*h-1,by omega⟩
  have hL : (leftBlock a).card = h := by rw [leftBlock,Fin.card_Iic]; change h-1+1=h; omega
  have hM : (middleBlock a b).card = h := by rw [middleBlock,Fin.card_Ioc]; change 2*h-1-(h-1)=h; omega
  have hR : (rightBlock b).card = n+2-2*h := by rw [rightBlock,Fin.card_Ioi]; change n+2-1-(2*h-1)=_; omega
  refine ⟨a,b,show (h-1:ℕ)<2*h-1 by omega,?_,?_,?_,?_⟩
  · omega
  · omega
  · omega
  · rw [hL,hM,hR]
    have h₁ := packetCost_mono (show h ≤ h+2 by omega)
    have h₂ := packetCost_mono (show n+2-2*h ≤ h+2 by omega)
    exact le_trans (by omega) (three_small_cost hh hl hu)

#print axioms exists_affordable_cuts
end GaloisForLFunctions.HTGeometry.WeakBonds
