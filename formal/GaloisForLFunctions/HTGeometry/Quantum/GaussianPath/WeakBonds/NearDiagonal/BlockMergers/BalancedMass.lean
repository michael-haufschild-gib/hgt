import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! # Probability cost of restoring all seams in a balanced chain -/
open Real
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
noncomputable section

/-- Each generation restores seams of total block length at most K.
Thus an exponential loss per merged length accumulates only once per
level, including chains whose lengths are not powers of two. -/
theorem balanced_mass (p : ℕ→ℝ) (hp : ∀ m, 0≤p m) (c : ℝ) (hc : 0≤c)
    (hsmall : ∀ m : ℕ, 2≤m → m≤3 → exp (-c*(m:ℝ)) ≤ p m)
    (hmerge : ∀ m : ℕ, 4≤m → exp (-c*(m:ℝ))*p (m/2)*p ((m+1)/2) ≤ p m) :
    ∀ t m : ℕ, 2≤m → m≤2^t → exp (-c*(m:ℝ)*((t:ℝ)+1)) ≤ p m := by
  intro t
  induction t with
  | zero => intro m hm h; simp only [pow_zero] at h; omega
  | succ t ih =>
    intro m hm hupper
    have hb (s : ℕ) : 0 ≤ c*(s:ℝ) := mul_nonneg hc (Nat.cast_nonneg _)
    by_cases hleaf : m≤3
    · apply (exp_le_exp.mpr _).trans (hsmall m hm hleaf)
      rw [Nat.cast_succ]
      nlinarith only [hb m,mul_nonneg (hb m) (Nat.cast_nonneg t)]
    let l := m/2
    let r := (m+1)/2
    have he : l+r=m := by dsimp only [l,r]; omega
    rw [pow_succ] at hupper
    have hl := ih l (by dsimp only [l]; omega) (by dsimp only [l]; omega)
    have hr := ih r (by dsimp only [r]; omega) (by dsimp only [r]; omega)
    have he' : (l:ℝ)+(r:ℝ)=m := by exact_mod_cast he
    have hparts : exp (-c*(m:ℝ)*((t+1:ℕ)+1:ℝ)) =
        exp (-c*(m:ℝ))*exp (-c*(l:ℝ)*((t:ℝ)+1))*exp (-c*(r:ℝ)*((t:ℝ)+1)) := by
      rw [←exp_add,←exp_add,Nat.cast_succ,←he']
      congr 1
      ring
    rw [hparts]
    apply le_trans _ (hmerge m (by omega))
    exact mul_le_mul (mul_le_mul_of_nonneg_left hl (exp_pos _).le) hr (exp_pos _).le
      (mul_nonneg (exp_pos _).le (hp l))

#print axioms balanced_mass
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
