import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Tactic

/-!
# A power majorant for Chebyshev growth

Hyperbolic addition and Bernoulli's inequality prove
`cosh(n*t) <= cosh(t)^(n*n)` for nonnegative arguments. Consequently the classical
Chebyshev polynomial satisfies `T_n(x) <= x^(n*n)` for `x >= 1`.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

theorem sinh_nat_comparison (t : ℝ) (n : ℕ) :
    Real.sinh ((n : ℝ)*|t|)*Real.cosh |t| ≤
      (n : ℝ)*Real.sinh |t| * Real.cosh ((n : ℝ)*|t|) := by
  have hs : 0 ≤ Real.sinh |t| := Real.sinh_nonneg_iff.mpr (abs_nonneg _)
  have hc : 0 ≤ Real.cosh |t| := (Real.cosh_pos _).le
  induction n with
  | zero => simp
  | succ n ih =>
    have hsn : 0 ≤ Real.sinh ((n : ℝ)*|t|) := Real.sinh_nonneg_iff.mpr (by positivity)
    have hmul := mul_le_mul_of_nonneg_right ih hc
    have hpos := mul_nonneg (show (0 : ℝ) ≤ n+1 by positivity)
      (mul_nonneg hsn (sq_nonneg (Real.sinh |t|)))
    simp only [Nat.cast_add,Nat.cast_one,add_mul,one_mul,Real.sinh_add,Real.cosh_add]
    nlinarith

theorem cosh_nat_power_bound (t : ℝ) (n : ℕ) :
    Real.cosh ((n : ℝ)*|t|) ≤ Real.cosh |t| ^ (n*n) := by
  let c := Real.cosh |t|
  let s := Real.sinh |t|
  have hc : 0 < c := Real.cosh_pos _
  have hs : 0 ≤ s := Real.sinh_nonneg_iff.mpr (abs_nonneg _)
  have hrel : c^2 = 1+s^2 := Real.cosh_sq' _
  change Real.cosh ((n : ℝ)*|t|) ≤ c^(n*n)
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := sinh_nat_comparison t n
    change Real.sinh ((n : ℝ)*|t|)*c ≤ (n : ℝ)*s*Real.cosh ((n : ℝ)*|t|) at hn
    have hm := mul_le_mul_of_nonneg_right hn hs
    have hber := one_add_mul_le_pow (a := s^2) (by nlinarith [sq_nonneg s]) (n+1)
    rw [← hrel,← pow_mul] at hber
    have hber' := mul_le_mul_of_nonneg_left hber (Real.cosh_pos ((n : ℝ)*|t|)).le
    have hstep : Real.cosh (((n+1 : ℕ) : ℝ)*|t|)*c ≤
        Real.cosh ((n : ℝ)*|t|)*c^(2*(n+1)) := by
      simp only [Nat.cast_add,Nat.cast_one,add_mul,one_mul,Real.cosh_add]
      change Real.cosh ((n : ℝ)*|t|)*c*c+Real.sinh ((n : ℝ)*|t|)*s*c ≤ _
      have hr := congrArg (fun x => Real.cosh ((n : ℝ)*|t|)*x) hrel
      push_cast at hber'
      nlinarith
    have hfinal := hstep.trans (mul_le_mul_of_nonneg_right ih (pow_nonneg hc.le _))
    apply (mul_le_mul_iff_left₀ hc).mp
    have he : (n+1)*(n+1)+1 = n*n+2*(n+1) := by ring
    calc
      Real.cosh (((n+1 : ℕ) : ℝ)*|t|)*c ≤ c^(n*n)*c^(2*(n+1)) := hfinal
      _ = c^((n+1)*(n+1))*c := by rw [← pow_add,← he,pow_succ]

theorem chebyshev_power_bound (t : ℝ) (n : ℕ) :
    (Polynomial.Chebyshev.T ℝ n).eval (1+|t|) ≤ (1+|t|)^(n*n) := by
  have hx : (1 : ℝ) ≤ 1+|t| := by linarith [abs_nonneg t]
  have ha := Real.arcosh_nonneg hx
  have h := cosh_nat_power_bound (Real.arcosh (1+|t|)) n
  rw [abs_of_nonneg ha,Real.cosh_arcosh hx] at h
  have he := Polynomial.Chebyshev.T_real_cosh (θ := Real.arcosh (1+|t|)) (n : ℤ)
  rw [Real.cosh_arcosh hx] at he
  simp only [Int.cast_natCast] at he
  rw [he]
  exact h


end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
