import GaloisForLFunctions.HeightHomotopyArithmeticCounts.PrimitiveTorsionDivisorFormula
import GaloisForLFunctions.HeightHomotopyArithmeticCounts.UniformSpacingDiagonal

/-!
# Power bounds for primitive torsion remainders

The logarithmic spacing defect is nonnegative and grows at most logarithmically.
Every positive power therefore controls the exact double Möbius remainder,
with an explicit divisor-count and gcd envelope.
-/

noncomputable section
open Finset
open scoped ArithmeticFunction.Moebius
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts
open ArithmeticEffectivityTheory ArithmeticIntersectionTheory

/-- Exponential convexity bounds the logarithmic spacing defect by a logarithm. -/
theorem logarithmicSpacingDefect_bounds (u : ℝ) (hu : 0 < u) :
    0 ≤ logarithmicSpacingDefect u ∧ logarithmicSpacingDefect u ≤ Real.log (1+u) := by
  have hd : 0 < 1-Real.exp (-u) := sub_pos.mpr
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu))
  have hu1 : 0 < 1+u := by linarith only [hu]
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp u) (Real.exp_pos (-u)).le
  have hexp : Real.exp u*Real.exp (-u)=1 := by rw [← Real.exp_add]; simp only [add_neg_cancel, Real.exp_zero]
  rw [hexp] at he
  have hprod : u ≤ (1-Real.exp (-u))*(1+u) := by nlinarith only [he]
  have hl := Real.log_le_log hu hprod
  rw [Real.log_mul hd.ne' hu1.ne'] at hl
  refine ⟨(spacing_log_defect_bounds u hu).1, ?_⟩
  unfold logarithmicSpacingDefect
  linarith only [hl]

/-- Every positive power controls the defect, with an explicit constant. -/
theorem logarithmicSpacingDefect_le_rpow (u α : ℝ) (hu : 0 < u)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    logarithmicSpacingDefect u ≤ (1+1/α)*u^α := by
  have hp0 := Real.rpow_nonneg hu.le α
  have hc : 1 ≤ 1+1/α := by
    have hdiv : 0 ≤ 1/α := by positivity
    linarith only [hdiv]
  by_cases hu1 : u ≤ 1
  · have hpow : u ≤ u^α := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hu hu1 hα1
    calc logarithmicSpacingDefect u ≤ u := (spacing_log_defect_bounds u hu).2
         _ ≤ u^α := hpow
         _ ≤ (1+1/α)*u^α := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hp0
  · have hu1' : 1 ≤ u := (lt_of_not_ge hu1).le
    have hp1 := Real.one_le_rpow hu1' hα.le
    have hlog := Real.log_le_rpow_div hu.le hα
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    have hmono := Real.log_le_log (show (0:ℝ)<1+u by linarith only [hu])
      (show 1+u≤2*u by linarith only [hu1'])
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hu.ne'] at hmono
    calc logarithmicSpacingDefect u ≤ Real.log (1+u) := (logarithmicSpacingDefect_bounds u hu).2
         _ ≤ u^α+u^α/α := by linarith only [hmono, hlog2, hlog, hp1]
         _ = (1+1/α)*u^α := by ring

/-- Möbius coefficients cannot enlarge the unsigned divisor envelope. -/
theorem abs_doubleMoebius_le (m n : ℕ) (X : ℕ → ℕ → ℝ) :
    |doubleMoebius m n X| ≤ ∑ d ∈ m.divisors, ∑ e ∈ n.divisors, |X d e| := by
  have hμ (a : ℕ) : |(μ a:ℝ)| ≤ 1 := by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := a))
  rw [doubleMoebius_swap]
  calc
    |∑ d ∈ m.divisors, (μ (m/d):ℝ)*∑ e ∈ n.divisors, (μ (n/e):ℝ)*X d e| ≤
        ∑ d ∈ m.divisors, |(μ (m/d):ℝ)*∑ e ∈ n.divisors, (μ (n/e):ℝ)*X d e| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ m.divisors, ∑ e ∈ n.divisors, |X d e| := by
      apply sum_le_sum
      intro d _hd
      rw [abs_mul]
      calc |(μ (m/d):ℝ)| *|∑ e ∈ n.divisors, (μ (n/e):ℝ)*X d e| ≤
          |∑ e ∈ n.divisors, (μ (n/e):ℝ)*X d e| := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right (hμ _) (abs_nonneg _)
           _ ≤ ∑ e ∈ n.divisors, |(μ (n/e):ℝ)*X d e| := abs_sum_le_sum_abs _ _
           _ ≤ ∑ e ∈ n.divisors, |X d e| := by
            apply sum_le_sum
            intro e _he
            rw [abs_mul]
            simpa only [one_mul] using mul_le_mul_of_nonneg_right (hμ _) (abs_nonneg _)

/-- A uniform divisor envelope for the exact exponential-radius remainder. -/
theorem torsionExponentialDefect_abs_le (t α : ℝ) (ht : 0 < t)
    (hα : 0 < α) (hα1 : α ≤ 1) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    |torsionExponentialDefect t m n| ≤
      (1+1/α)*(m.divisors.card:ℝ)*(n.divisors.card:ℝ)*
        (Nat.gcd m n:ℝ)*(t*(Nat.lcm m n:ℝ))^α := by
  have hg : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n hm
  have hL : 0 < Nat.lcm m n := Nat.lcm_pos hm hn
  have hC : 0 ≤ 1+1/α := by positivity
  have hpair (d : ℕ) (hd : d∈m.divisors) (e : ℕ) (he : e∈n.divisors) :
      |(Nat.gcd d e:ℝ)*logarithmicSpacingDefect (t*(Nat.lcm d e:ℝ))| ≤
        (Nat.gcd m n:ℝ)*((1+1/α)*(t*(Nat.lcm m n:ℝ))^α) := by
    have hdv := Nat.dvd_of_mem_divisors hd
    have hev := Nat.dvd_of_mem_divisors he
    have hgdiv : Nat.gcd d e∣Nat.gcd m n := Nat.dvd_gcd_iff.mpr
      ⟨(Nat.gcd_dvd_left d e).trans hdv, (Nat.gcd_dvd_right d e).trans hev⟩
    have hLdiv : Nat.lcm d e∣Nat.lcm m n := Nat.lcm_dvd_iff.mpr
      ⟨hdv.trans (Nat.dvd_lcm_left m n), hev.trans (Nat.dvd_lcm_right m n)⟩
    have hgd : (Nat.gcd d e:ℝ)≤Nat.gcd m n := by exact_mod_cast Nat.le_of_dvd hg hgdiv
    have hLd : (Nat.lcm d e:ℝ)≤Nat.lcm m n := by exact_mod_cast Nat.le_of_dvd hL hLdiv
    have hLd0 : (0:ℝ)<Nat.lcm d e := by
      exact_mod_cast Nat.lcm_pos (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors he)
    have hu : 0<t*(Nat.lcm d e:ℝ) := mul_pos ht hLd0
    have hF0 := (logarithmicSpacingDefect_bounds _ hu).1
    have hF := (logarithmicSpacingDefect_le_rpow _ α hu hα hα1).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hu.le (mul_le_mul_of_nonneg_left hLd ht.le) hα.le) hC)
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg hF0]
    exact mul_le_mul hgd hF hF0 (Nat.cast_nonneg _)
  calc |torsionExponentialDefect t m n| ≤
        ∑ d ∈ m.divisors, ∑ e ∈ n.divisors,
          |(Nat.gcd d e:ℝ)*logarithmicSpacingDefect (t*(Nat.lcm d e:ℝ))| :=
          abs_doubleMoebius_le m n _
       _ ≤ ∑ _d ∈ m.divisors, ∑ _e ∈ n.divisors,
          (Nat.gcd m n:ℝ)*((1+1/α)*(t*(Nat.lcm m n:ℝ))^α) :=
          sum_le_sum fun d hd => sum_le_sum fun e he => hpair d hd e he
       _ = _ := by
          simp only [sum_const, nsmul_eq_mul]
          ring

#print axioms logarithmicSpacingDefect_le_rpow
#print axioms abs_doubleMoebius_le
#print axioms torsionExponentialDefect_abs_le

end GaloisForLFunctions.HeightHomotopyArithmeticCounts
