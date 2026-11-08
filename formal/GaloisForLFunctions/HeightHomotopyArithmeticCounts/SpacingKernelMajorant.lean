import GaloisForLFunctions.HeightHomotopyArithmeticCounts.SpacingErrorIdentity
import GaloisForLFunctions.HeightHomotopyArithmeticCounts.PrimitiveSpacingRemainder
import GaloisForLFunctions.RHTower.DivisorBound

/-!
# Arithmetic majorants for the full spacing kernel

The gcd twist costs at most a divisor count. Subpolynomial divisor growth and
the power bound for the primitive remainder give a normalized gcd envelope
for every actual spacing-error entry, with arbitrarily small extra conductor
powers. The product spacing radius is retained throughout.
-/

noncomputable section
open Finset
open scoped ArithmeticFunction.Moebius
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts
open ArithmeticEffectivityTheory ArithmeticIntersectionTheory

/-- The positive gcd twist is bounded by the number of divisors of the gcd. -/
theorem gcdTwist_divisor_bounds (m n : ℕ) :
    0 ≤ gcdTwist m n ∧ gcdTwist m n ≤ (Nat.gcd m n).divisors.card := by
  refine ⟨sum_nonneg fun d _ => twistWeight_nonneg d, ?_⟩
  calc gcdTwist m n ≤ ∑ _d ∈ (Nat.gcd m n).divisors, (1:ℝ) := by
        apply sum_le_sum
        intro d hd
        have hd0 := Nat.pos_of_mem_divisors hd
        have hφ : (1:ℝ) ≤ Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd0
        have hμ : |(μ d:ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
        have hμ2 : (μ d:ℝ)^2 ≤ 1 := by
          have hmul := mul_le_mul hμ hμ (abs_nonneg (μ d:ℝ)) zero_le_one
          simpa only [← pow_two, sq_abs, one_pow] using hmul
        exact (div_le_one (lt_of_lt_of_le zero_lt_one hφ)).mpr (hμ2.trans hφ)
       _ = _ := by simp only [sum_const, nsmul_eq_mul, mul_one]

/-- Subpolynomial divisor growth controls all arithmetic losses in the remainder. -/
theorem spacing_arithmetic_weight_bound (κ : ℝ) (hκ : 0 < κ) :
    ∃ D : ℝ, 0 < D ∧ ∀ m n : ℕ, 0 < m → 0 < n →
      gcdTwist m n*(m.divisors.card:ℝ)*(n.divisors.card:ℝ) ≤ 
        D*((m:ℝ)*n)^(2*κ) := by
  obtain ⟨A, hA, hdiv⟩ := RHTower.card_divisors_le_const_mul_rpow hκ
  refine ⟨A^3, pow_pos hA _, ?_⟩
  intro m n hm hn
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hg := Nat.gcd_pos_of_pos_left n hm
  have hg0 : (0:ℝ) < Nat.gcd m n := by exact_mod_cast hg
  have hgm : (Nat.gcd m n:ℝ) ≤ (m:ℝ)*n := by
    have hgm' : (Nat.gcd m n:ℝ) ≤ m := by exact_mod_cast Nat.le_of_dvd hm (Nat.gcd_dvd_left m n)
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    exact hgm'.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hn1 hm0.le)
  have hG : gcdTwist m n ≤ A*((m:ℝ)*n)^κ :=
    (gcdTwist_divisor_bounds m n).2.trans ((hdiv _ hg).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hg0.le hgm hκ.le) hA.le))
  have hmn := mul_le_mul (hdiv m hm) (hdiv n hn) (Nat.cast_nonneg _) (by positivity : 0 ≤ A*(m:ℝ)^κ)
  calc gcdTwist m n*(m.divisors.card:ℝ)*(n.divisors.card:ℝ) =
        gcdTwist m n*((m.divisors.card:ℝ)*(n.divisors.card:ℝ)) := by ring
       _ ≤ (A*((m:ℝ)*n)^κ)*((A*(m:ℝ)^κ)*(A*(n:ℝ)^κ)) :=
        mul_le_mul hG hmn (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by positivity)
       _ = A^3*((m:ℝ)*n)^(2*κ) := by
        rw [show 2*κ=κ+κ by ring, Real.rpow_add (mul_pos hm0 hn0)]
        simp only [Real.mul_rpow hm0.le hn0.le]
        ring

/-- A power modulus for every entry of the actual renormalized spacing kernel. -/
theorem spacingKernelError_conductor_bound (α κ : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (m n : ℕ), 0 < ε → 0 < m → 0 < n →
      |spacingKernelError ε m n| ≤ 
        C*ε^α*(Nat.gcd m n:ℝ)*((m:ℝ)*n)^(α+2*κ)/Real.sqrt ((m:ℝ)*n) := by
  obtain ⟨D, hD, hweight⟩ := spacing_arithmetic_weight_bound κ hκ
  refine ⟨(1+1/α)*D*(2:ℝ)^α, by positivity, ?_⟩
  intro ε m n hε hm hn
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  let t := ε*((m:ℝ)⁻¹+(n:ℝ)⁻¹)
  have ht : 0 < t := mul_pos hε (add_pos (inv_pos.mpr hm0) (inv_pos.mpr hn0))
  have ht2 : t ≤ 2*ε := by
    have hmi := (inv_le_one₀ hm0).mpr hm1
    have hni := (inv_le_one₀ hn0).mpr hn1
    calc t ≤ ε*(1+1) := mul_le_mul_of_nonneg_left (add_le_add hmi hni) hε.le
         _ = 2*ε := by ring
  have hL : (Nat.lcm m n:ℝ) ≤ (m:ℝ)*n := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos hm hn)
      (Nat.lcm_dvd_iff.mpr ⟨dvd_mul_right m n, dvd_mul_left n m⟩)
  have hscale : (t*(Nat.lcm m n:ℝ))^α ≤ (2*ε*((m:ℝ)*n))^α :=
    Real.rpow_le_rpow (by positivity)
      (mul_le_mul ht2 hL (Nat.cast_nonneg _) (by positivity)) hα.le
  have hG := (gcdTwist_divisor_bounds m n).1
  rw [spacingKernelError_eq ε hε m n hm hn, abs_div, abs_mul,
    abs_of_nonneg hG, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  calc gcdTwist m n*|torsionExponentialDefect t m n| ≤ 
        gcdTwist m n*((1+1/α)*(m.divisors.card:ℝ)*(n.divisors.card:ℝ)*
          (Nat.gcd m n:ℝ)*(t*(Nat.lcm m n:ℝ))^α) :=
        mul_le_mul_of_nonneg_left (torsionExponentialDefect_abs_le t α ht hα hα1 m n hm hn) hG
       _ ≤ (1+1/α)*D*((m:ℝ)*n)^(2*κ)*(Nat.gcd m n:ℝ)*(2*ε*((m:ℝ)*n))^α := by
        calc _ = (1+1/α)*(gcdTwist m n*(m.divisors.card:ℝ)*(n.divisors.card:ℝ))*
                    (Nat.gcd m n:ℝ)*(t*(Nat.lcm m n:ℝ))^α := by ring
             _ ≤ (1+1/α)*(D*((m:ℝ)*n)^(2*κ))*(Nat.gcd m n:ℝ)*
                 (2*ε*((m:ℝ)*n))^α := mul_le_mul
               (mul_le_mul_of_nonneg_right
                 (mul_le_mul_of_nonneg_left (hweight m n hm hn) (by positivity)) (Nat.cast_nonneg _))
               hscale (by positivity) (by positivity)
             _ = _ := by ring
       _ = _ := by
        rw [Real.mul_rpow (by positivity : 0 ≤ 2*ε) (mul_nonneg hm0.le hn0.le),
          Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hε.le,
          Real.rpow_add (mul_pos hm0 hn0)]
        ring

#print axioms gcdTwist_divisor_bounds
#print axioms spacing_arithmetic_weight_bound
#print axioms spacingKernelError_conductor_bound
end GaloisForLFunctions.HeightHomotopyArithmeticCounts
