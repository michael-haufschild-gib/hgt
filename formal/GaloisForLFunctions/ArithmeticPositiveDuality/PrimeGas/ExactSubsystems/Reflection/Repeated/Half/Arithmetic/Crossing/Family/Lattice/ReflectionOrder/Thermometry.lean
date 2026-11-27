import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Family
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Exact global thermometry from one prime reflection reading -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder

open Real
open _root_.HTGeometry (finiteGibbsStateWeight)
open PrimeCalibration (log_pos_prime)
open PrimeCalibration.Multiplicity (gibbs_defect lawDefect)

/-- The signed comparison of a single probability law, with order
controlled by the number of four-branch lifts. -/
def thermometer (n : ℕ) (q : Nat.Primes) (d : ℝ) :=
  lawDefect (finiteGibbsStateWeight d (primeModes q (shells (n+1)))) 1

private theorem square (t : ℝ) : multiplier 1 t=(2*sinh (t/2))^2 := by
  have e : exp t=exp (t/2)^2 := by rw [sq,←exp_add]; congr 1; ring
  rw [multiplier,mul_one,e,sinh_eq,exp_neg]
  field_simp

/-- The reading is exactly an odd power of a hyperbolic sine of the
physical prime energy, at every real damping. -/
theorem exact_reading (n : ℕ) (q : Nat.Primes) (d : ℝ) :
    thermometer n q d= -(2*sinh (d*log q.val/2))^(2*n+3) := by
  rw [thermometer,gibbs_defect,one_mul,shell_trace,square,←pow_mul]
  let t := d*log q.val
  have seed : exp (t*(-1/2))-exp (t*(1/2))= -(2*sinh (t/2)) := by
    rw [sinh_eq,show t*(-1/2)= -(t/2) by ring,show t*(1/2)=t/2 by ring]
    ring
  change (2*sinh (t/2))^(2*(n+1))*(exp (t*(-1/2))-exp (t*(1/2)))=_
  rw [seed,mul_neg,show 2*n+3=2*(n+1)+1 by omega,pow_succ _ (2*(n+1))]

/-- An unlabeled Gibbs law determines signed damping globally. -/
theorem thermometer_strictAnti (n : ℕ) (q : Nat.Primes) : StrictAnti (thermometer n q) := by
  intro x y xy
  rw [exact_reading,exact_reading,neg_lt_neg_iff]
  have odd : Odd (2*n+3) := ⟨n+1,by omega⟩
  apply odd.strictMono_pow
  exact mul_lt_mul_of_pos_left (sinh_lt_sinh.mpr
    (div_lt_div_of_pos_right (mul_lt_mul_of_pos_right xy (log_pos_prime q)) (by norm_num))) (by norm_num)

/-- Exact error threshold for a prescribed distance. The two endpoints
attain it and all points farther away give a strictly larger reading. -/
theorem error_window (n : ℕ) (q : Nat.Primes) (d δ : ℝ) :
    |thermometer n q d|≤(2*sinh (δ*log q.val/2))^(2*n+3) ↔ |d|≤δ := by
  have odd : Odd (2*n+3) := ⟨n+1,by omega⟩
  rw [exact_reading,abs_neg,abs_pow,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2),abs_sinh,
    abs_div,abs_mul,abs_of_pos (log_pos_prime q),abs_of_pos (by norm_num : (0 : ℝ)<2)]
  exact odd.strictMono_pow.le_iff_le.trans ((mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ)<2)).trans
    (sinh_le_sinh.trans ((div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ)<2)).trans
      (mul_le_mul_iff_left₀ (log_pos_prime q)))))

#print axioms exact_reading
#print axioms thermometer_strictAnti
#print axioms error_window

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder
