import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzUniformTail

/-! Exact repeated phase cells of the arithmetic completion. On these cells
the uncorrected sum is zero and the repaired tail has an explicit positive value. -/

open MeasureTheory Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

/-- The exact cubic collar relation improves the coarse support budget. -/
theorem sourceFactorialCollar_scaled_le_twelfth {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ)*sourceFactorialCollar N ≤ 1/12 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hε := (sourceFactorialCollar_pos hN).le
  have hc : (1+sourceFactorialCollar N)^3 = 1+1/(4*(N : ℝ)) := by
    rw [← exp_three_sourceFactorialWidth N]
    unfold sourceFactorialCollar
    rw [show 1+(Real.exp (sourceFactorialWidth N)-1) = Real.exp (sourceFactorialWidth N) by ring,
      show 3*sourceFactorialWidth N = sourceFactorialWidth N+sourceFactorialWidth N+
        sourceFactorialWidth N by ring, Real.exp_add, Real.exp_add]
    ring
  have h : 3*sourceFactorialCollar N ≤ 1/(4*(N : ℝ)) := by
    nlinarith [sq_nonneg (sourceFactorialCollar N),
      mul_nonneg hε (sq_nonneg (sourceFactorialCollar N))]
  have hh := (le_div_iff₀ (show 0 < 4*(N : ℝ) by positivity)).1 h
  nlinarith

/-- A collar that meets no new integer leaves exactly `m` complete samples. -/
theorem clampedLatticeSum_eq_nat_of_cell {ε a t : ℝ} (hε : 0 < ε)
    (ha : 0 < a) (ht : 0 < t) (m : ℕ)
    (hm0 : (m : ℝ) ≤ a/t) (hm1 : a*(1+ε)/t ≤ (m : ℝ)+1) :
    clampedLatticeSum ε a t = m := by
  unfold clampedLatticeSum
  have hzero (k : ℕ) (hk : k ∉ Finset.range m) :
      clampedRamp ε (((k : ℝ)+1)*t/a) = 0 := by
    have hmk : m ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    have hmkR : (m : ℝ) ≤ k := by exact_mod_cast hmk
    apply clampedRamp_eq_zero hε
    apply (le_div_iff₀ ha).2
    have h := (div_le_iff₀ ht).1 hm1
    nlinarith
  rw [tsum_eq_sum hzero]
  have hone (k : ℕ) (hk : k ∈ Finset.range m) :
      clampedRamp ε (((k : ℝ)+1)*t/a) = 1 := by
    have hkm : k+1 ≤ m := by have := Finset.mem_range.mp hk; omega
    have hkmR : (k : ℝ)+1 ≤ m := by exact_mod_cast hkm
    apply clampedRamp_eq_one hε
    apply (div_le_one ha).2
    have h := (le_div_iff₀ ht).1 hm0
    nlinarith
  simp_rw [Finset.sum_congr rfl hone]
  simp

/-- Every unit phase contains a fixed-width interval of exact arithmetic zero. -/
theorem factorialMuntzSum_eq_zero_on_phase (n j : ℕ)
    (hj1 : j < 2*(n+1)) {t : ℝ} (ht : 0 < t)
    (hy0 : (j : ℝ) ≤ ((n+1 : ℕ) : ℝ)/t)
    (hy1 : ((n+1 : ℕ) : ℝ)/t ≤ (j : ℝ)+1/16) :
    factorialMuntzSum n t = 0 := by
  let N : ℝ := ((n+1 : ℕ) : ℝ)
  let ε := sourceFactorialCollar (n+1)
  have hN : 0 < N := by dsimp [N]; positivity
  have hε : 0 < ε := sourceFactorialCollar_pos (by omega)
  have hjR : (j : ℝ)+1 ≤ 2*N := by dsimp [N]; exact_mod_cast hj1
  have hy : N/t ≤ 2*N := by dsimp [N] at *; linarith
  have hc : N*ε ≤ 1/12 := sourceFactorialCollar_scaled_le_twelfth (by omega)
  have hshift : ε*(N/t) ≤ 1/6 := by
    have h := mul_le_mul_of_nonneg_left hy hε.le
    nlinarith
  have hcount (d : ℕ) (hd0 : 1 ≤ d) (hd1 : d ≤ 4) :
      clampedLatticeSum ε ((d : ℝ)*N) t = (d*j : ℕ) := by
    have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hd4 : (d : ℝ) ≤ 4 := by exact_mod_cast hd1
    apply clampedLatticeSum_eq_nat_of_cell hε (by positivity) ht
    · push_cast
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hy0 hd.le
    · push_cast
      have ha := mul_le_mul_of_nonneg_left hy1 hd.le
      have hb := mul_le_mul_of_nonneg_left hshift hd.le
      rw [show (d : ℝ)*N*(1+ε)/t = (d : ℝ)*(N/t)+(d : ℝ)*(ε*(N/t)) by ring]
      nlinarith
  rw [factorialMuntzSum_eq_clampedLattice n ht]
  change clampedLatticeSum ε (4*N) t-4*clampedLatticeSum ε (2*N) t+
    4*clampedLatticeSum ε N t = 0
  have h1 := hcount 1 (by omega) (by omega)
  have h2 := hcount 2 (by omega) (by omega)
  have h4 := hcount 4 (by omega) (by omega)
  norm_num only [Nat.cast_ofNat, one_mul] at h1 h2 h4
  rw [h1, h2, h4]
  push_cast
  ring

def factorialMuntzTailPhaseCell (n j : ℕ) : Set ℝ :=
  Icc (Real.log (((n+1 : ℕ) : ℝ)/((j : ℝ)+1/16)))
    (Real.log (((n+1 : ℕ) : ℝ)/(j : ℝ)))

theorem factorialMuntzTailPhaseCell_nonpos (n j : ℕ) (hj : n+1 ≤ j) {x : ℝ}
    (hx : x ∈ factorialMuntzTailPhaseCell n j) : x ≤ 0 := by
  have hjp : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  apply hx.2.trans
  apply Real.log_nonpos (by positivity)
  exact (div_le_one hjp).2 (by exact_mod_cast hj)

theorem factorialMuntzTailPhaseCell_bounds (n j : ℕ) (hj : n+1 ≤ j) {x : ℝ}
    (hx : x ∈ factorialMuntzTailPhaseCell n j) :
    (j : ℝ) ≤ ((n+1 : ℕ) : ℝ)/Real.exp x ∧
      ((n+1 : ℕ) : ℝ)/Real.exp x ≤ (j : ℝ)+1/16 := by
  have hjp : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hN : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hlow := Real.exp_le_exp.mpr hx.1
  have hupp := Real.exp_le_exp.mpr hx.2
  rw [Real.exp_log (by positivity)] at hlow hupp
  constructor
  · apply (le_div_iff₀ (Real.exp_pos x)).2
    have h := (le_div_iff₀ hjp).1 hupp
    nlinarith
  · apply (div_le_iff₀ (Real.exp_pos x)).2
    have h := (div_le_iff₀ (show 0 < (j : ℝ)+1/16 by positivity)).1 hlow
    nlinarith

/-- Exact positive repaired source on each repeated cell, including endpoints. -/
theorem factorialMuntzCorrectedTail_on_phaseCell (n j : ℕ) (hj0 : n+1 ≤ j)
    (hj1 : j < 2*(n+1)) {x : ℝ} (hx : x ∈ factorialMuntzTailPhaseCell n j) :
    factorialMuntzCorrectedTail n x = Real.exp (x/2)/(2*Real.sqrt ((n+1 : ℕ) : ℝ)) := by
  have hx0 := factorialMuntzTailPhaseCell_nonpos n j hj0 hx
  obtain ⟨hy0,hy1⟩ := factorialMuntzTailPhaseCell_bounds n j hj0 hx
  have hz := factorialMuntzSum_eq_zero_on_phase n j hj1 (Real.exp_pos x) hy0 hy1
  simp only [factorialMuntzCorrectedTail, factorialMuntzBoundaryCorrected,
    indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx0), factorialMuntzCompletion,
    hz, mul_zero, zero_div, zero_add, factorialMuntzBoundaryCoefficient]
  ring

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
