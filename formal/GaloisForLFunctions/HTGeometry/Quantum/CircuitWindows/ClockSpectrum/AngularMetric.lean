import GaloisForLFunctions.RHTower.Sieve.DirichletLipschitz
import GaloisForLFunctions.RHTower.RootOfUnityIntervalCompletion

/-! # Chord distances of phases given in turns -/
namespace GaloisForLFunctions.HTGeometry.ClockSpectrum
noncomputable section

/-- Unit complex phase of an angle expressed in turns. -/
def expTurns (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)

theorem expTurns_lip (x y : ℝ) : ‖expTurns x-expTurns y‖ ≤ 2*Real.pi*|x-y| := by
  apply (_root_.RHTower.Sieve.norm_exp_phase_sub_le _ _).trans_eq
  rw [←mul_sub,abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi)]

theorem norm_expTurns (x : ℝ) : ‖expTurns x‖=1 := Complex.norm_exp_ofReal_mul_I _

private theorem expTurns_sub (x y : ℝ) : expTurns x-expTurns y=expTurns y*(expTurns (x-y)-1) := by
  rw [mul_sub,mul_one]
  unfold expTurns
  rw [←Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Distinct equally spaced phases are separated by at least four
divided by the clock order, including the wraparound gap. -/
theorem root_separation {m : ℕ} (i j : Fin m) (hne : i ≠ j) :
    4/(m:ℝ) ≤ ‖expTurns (i.val/(m:ℝ))-expTurns (j.val/(m:ℝ))‖ := by
  have ordered (i j : Fin m) (h : j < i) :
      4/(m:ℝ) ≤ ‖expTurns (i.val/(m:ℝ))-expTurns (j.val/(m:ℝ))‖ := by
    let k := i.val-j.val
    have hpos : 0 < k := Nat.sub_pos_of_lt h
    have hlt : k < m := (Nat.sub_le _ _).trans_lt i.isLt
    have hmin : (1:ℕ) ≤ min k (m-k) := le_min hpos (Nat.sub_pos_of_lt hlt)
    have hm : 0 < (m:ℝ) := Nat.cast_pos.mpr (hpos.trans hlt)
    have hch := GaloisForLFunctions.RHTower.RootOfUnityCompletion.norm_exp_sub_one_ge hpos hlt
    have he : expTurns (i.val/(m:ℝ)-j.val/(m:ℝ))=Complex.exp (2*Real.pi*Complex.I*k/m) := by
      unfold expTurns
      congr 1
      dsimp only [k]
      push_cast [Nat.cast_sub h.le]
      ring
    rw [expTurns_sub,norm_mul,norm_expTurns,one_mul,he]
    apply le_trans _ hch
    have hc : (1:ℝ) ≤ (min k (m-k):ℕ) := by exact_mod_cast hmin
    exact div_le_div_of_nonneg_right (by linarith only [hc]) hm.le
  rcases lt_or_gt_of_ne hne with h|h
  · rw [norm_sub_rev]
    exact ordered j i h
  · exact ordered i j h

#print axioms root_separation
end
end GaloisForLFunctions.HTGeometry.ClockSpectrum
