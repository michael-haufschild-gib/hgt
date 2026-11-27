import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! # Gap and dilation scales for balanced physical blocks -/
open Real
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
noncomputable section

/-- The spacing reserved for a register of K wires. -/
def gapScale (K : ℕ) : ℝ := (1/1024:ℝ)^K

theorem gapScale_pos (K : ℕ) : 0<gapScale K := by unfold gapScale; positivity

theorem gapScale_antitone : Antitone gapScale :=
  fun _ _ h => pow_le_pow_of_le_one (by norm_num) (by norm_num) h

abbrev gridCount (l r : ℕ) :=
  Fintype.card ((Fin (2^(l+2))×Fin (2^(r+2)))×(Fin (2^(l+2))×Fin (2^(r+2))))+1

theorem gridCount_bound (l r : ℕ) : gridCount l r ≤ 2^(2*(l+r+4)+1) := by
  simp only [gridCount,Fintype.card_prod,Fintype.card_fin,←pow_add]
  rw [show l+2+(r+2)+(l+2+(r+2))=2*(l+r+4) by omega,pow_succ]
  have h : 1≤2^(2*(l+r+4)) := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
  omega

/-- Half the retained product gap exceeds the parent scale, including
the unbalanced-by-one split required by odd chain lengths. -/
theorem parent_spacing (l r : ℕ) (hr : r≤l+1) :
    2*gapScale (l+r+4) ≤ gapScale (r+2)/(8*(gridCount l r:ℝ)) := by
  have hn : (0:ℝ)<gridCount l r := Nat.cast_pos.mpr (Nat.succ_pos _)
  have hpow : (16:ℝ)*gridCount l r ≤ 1024^(l+2) := by
    have hh : 16*gridCount l r ≤ 2^(2*(l+r+4)+1+4) := calc
      _ ≤ 16*2^(2*(l+r+4)+1) := Nat.mul_le_mul_left 16 (gridCount_bound l r)
      _ = _ := by rw [pow_add (2:ℕ) (2*(l+r+4)+1) 4]; exact Nat.mul_comm _ _
    have he : 2*(l+r+4)+1+4≤10*(l+2) := by omega
    have hle := hh.trans (Nat.pow_le_pow_right (by decide : 0<2) he)
    rw [pow_mul] at hle
    exact_mod_cast hle
  have he : gapScale (l+r+4)=gapScale (r+2)/(1024:ℝ)^(l+2) := by
    rw [show l+r+4=r+2+(l+2) by omega,gapScale,pow_add,one_div_pow]
    simp [gapScale,div_eq_mul_inv]
  rw [he,le_div_iff₀ (mul_pos (by norm_num) hn)]
  have hd : 0<(1024:ℝ)^(l+2) := by positivity
  calc 2*(gapScale (r+2)/1024^(l+2))*(8*gridCount l r)
        = (gapScale (r+2)*(16*gridCount l r))/1024^(l+2) := by ring
       _ ≤ _ := (div_le_iff₀ hd).mpr (mul_le_mul_of_nonneg_left hpow (gapScale_pos _).le)

#print axioms parent_spacing
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
