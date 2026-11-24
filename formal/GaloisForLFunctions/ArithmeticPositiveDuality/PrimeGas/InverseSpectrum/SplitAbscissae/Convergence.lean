import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Geometric weights with a prescribed number of finite polynomial moments -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

/-- Scalar series for the energy moments on a prime-power ray. -/
def towerTerm (r : ℝ) (m d k : ℕ) := (k:ℝ)^m*r^k/(k:ℝ)^d

private theorem below_one {r : ℝ} (hr : 0 < r) (h : r < 1) (m d : ℕ) : Summable (towerTerm r m d) := by
  have hn : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr.le]
  apply (summable_pow_mul_geometric_of_norm_lt_one m hn).of_nonneg_of_le
  · intro k
    exact div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg k) _) (pow_nonneg hr.le _)) (pow_nonneg (Nat.cast_nonneg k) _)
  · intro k
    cases k with
    | zero => cases d <;> simp [towerTerm]
    | succ k =>
      exact div_le_self (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg hr.le _))
        (one_le_pow₀ (show (1:ℝ) ≤ (k+1:ℕ) by exact_mod_cast Nat.succ_pos k))

private theorem at_one (m d : ℕ) : Summable (towerTerm 1 m d) ↔ m+1 < d := by
  have he (k : ℕ) : towerTerm 1 m d (k+1) = ((k+1:ℕ):ℝ)^((m:ℝ)-(d:ℝ)) := by
    rw [towerTerm,one_pow,mul_one,Real.rpow_sub (by positivity),Real.rpow_natCast,Real.rpow_natCast]
  rw [← summable_nat_add_iff (f := towerTerm 1 m d) 1]
  simp_rw [he]
  rw [summable_nat_add_iff (f := fun k : ℕ => (k:ℝ)^((m:ℝ)-(d:ℝ))) 1,Real.summable_nat_rpow]
  constructor
  · intro h
    exact_mod_cast (show (m:ℝ)+1 < d by linarith only [h])
  · intro h
    have h' : (m:ℝ)+1 < d := by exact_mod_cast h
    linarith only [h']

private theorem above_one {r : ℝ} (hr : 1 < r) (m d : ℕ) : ¬ Summable (towerTerm r m d) := by
  intro h
  have hp := zero_lt_one.trans hr
  have hi : ‖r⁻¹‖ < 1 := by rw [Real.norm_of_nonneg (inv_pos.mpr hp).le]; exact inv_lt_one_of_one_lt₀ hr
  have hlim := h.tendsto_atTop_zero.mul (summable_pow_mul_geometric_of_norm_lt_one d hi).tendsto_atTop_zero
  obtain ⟨k,hk,hs⟩ := ((eventually_gt_atTop (0:ℕ)).and (hlim.eventually_lt_const (show (0:ℝ)*0 < 1 by norm_num))).exists
  have hk' : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have he : towerTerm r m d k*((k:ℝ)^d*(r⁻¹)^k) = (k:ℝ)^m := by
    rw [towerTerm,inv_pow]
    field_simp [hk',hp.ne']
  change towerTerm r m d k*((k:ℝ)^d*(r⁻¹)^k) < 1 at hs
  rw [he] at hs
  exact hs.not_ge (one_le_pow₀ (show (1:ℝ) ≤ k by exact_mod_cast hk))

/-- Inside the unit disk all moments converge. At the boundary exactly the ordinary power-sum condition remains. -/
theorem summable_towerTerm_iff {r : ℝ} (hr : 0 < r) (m d : ℕ) :
    Summable (towerTerm r m d) ↔ r < 1 ∨ r = 1 ∧ m+1 < d := by
  rcases lt_trichotomy r 1 with h|h|h
  · exact iff_of_true (below_one hr h m d) (Or.inl h)
  · subst r
    simp only [lt_irrefl,false_or,true_and,at_one]
  · exact iff_of_false (above_one h m d) (fun he => he.elim (not_lt_of_gt h) (fun heq => h.ne' heq.1))

#print axioms summable_towerTerm_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
