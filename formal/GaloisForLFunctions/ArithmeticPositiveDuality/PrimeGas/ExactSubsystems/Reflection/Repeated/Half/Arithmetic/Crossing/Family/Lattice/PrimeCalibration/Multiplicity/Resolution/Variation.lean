import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Flow
import Mathlib.Analysis.Calculus.LHopital

/-! # Order of contact of a reflected finite heat trace -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Resolution

open Finset Filter Real
open scoped Topology

variable {I : Type*} [Fintype I]

/-- The two reflected exponentials differentiated in the damping parameter. -/
def variation (E : I → ℝ) (j : ℕ) (t : ℝ) :=
  ∑ i, ((E i)^j * exp (t*E i) - (-E i)^j * exp (t*(-E i)))

theorem variation_zero_order (E : I → ℝ) : variation E 0 = oddTrace E := by
  funext t
  simp only [variation,oddTrace,oddTerm,pow_zero,one_mul,mul_neg,neg_mul]

theorem variation_origin (E : I → ℝ) (j : ℕ) :
    variation E j 0 = moment E j - moment (fun i => -E i) j := by
  simp only [variation,zero_mul,exp_zero,mul_one,sum_sub_distrib,moment]

theorem variation_deriv (E : I → ℝ) (j : ℕ) (t : ℝ) :
    HasDerivAt (variation E j) (variation E (j+1) t) t := by
  have term (x : ℝ) : HasDerivAt (fun v : ℝ => x^j*exp (v*x))
      (x^(j+1)*exp (t*x)) t := by
    have lin : HasDerivAt (fun v : ℝ => v*x) x t := by
      simpa only [id_eq,one_mul] using (hasDerivAt_id t).mul_const x
    exact (lin.exp.const_mul (x^j)).congr_deriv (by rw [pow_succ]; ring)
  exact HasDerivAt.fun_sum fun i _ => (term (E i)).sub (term (-E i))

/-- Each lower-order cancellation permits one division by the damping.
The surviving coefficient is the first remaining derivative divided by a factorial. -/
theorem variation_limit (E : I → ℝ) (m j : ℕ)
    (vanish : ∀ k < m, variation E (j+k) 0=0) :
    Tendsto (fun t => variation E j t/t^m) (𝓝[≠] 0)
      (𝓝 (variation E (j+m) 0/(m.factorial : ℝ))) := by
  induction m generalizing j with
  | zero =>
    simpa only [Nat.add_zero,Nat.factorial_zero,Nat.cast_one,pow_zero,div_one] using
      (variation_deriv E j 0).continuousAt.continuousWithinAt.tendsto
  | succ m ih =>
    have low (k : ℕ) (hk : k < m) : variation E (j+1+k) 0=0 := by
      simpa only [show j+1+k=j+(k+1) by omega] using vanish (k+1) (by omega)
    have top := (ih (j+1) low).div_const (m+1 : ℝ)
    have slope : Tendsto (fun t : ℝ => variation E (j+1) t/((m+1 : ℝ)*t^m))
        (𝓝[≠] 0) (𝓝 (variation E (j+(m+1)) 0/((m+1).factorial : ℝ))) := by
      simpa only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ,div_div,
        show j+1+m=j+(m+1) by omega,mul_comm (m+1 : ℝ)] using top
    have hpow (t : ℝ) : HasDerivAt (fun x : ℝ => x^(m+1)) ((m+1 : ℝ)*t^m) t := by
      simpa only [Nat.cast_succ,Nat.add_sub_cancel] using hasDerivAt_pow (m+1) t
    have hne : ∀ᶠ t : ℝ in 𝓝[≠] 0, t≠0 := self_mem_nhdsWithin
    have hz : variation E j 0=0 := by simpa only [Nat.add_zero] using vanish 0 (Nat.zero_lt_succ _)
    apply HasDerivAt.lhopital_zero_nhdsNE (Eventually.of_forall (variation_deriv E j))
      (Eventually.of_forall hpow) (hne.mono fun t ht => mul_ne_zero (by positivity) (pow_ne_zero _ ht))
    · simpa only [hz] using (variation_deriv E j 0).continuousAt.continuousWithinAt.tendsto
    · simpa only [zero_pow (Nat.succ_ne_zero m)] using (hpow 0).continuousAt.continuousWithinAt.tendsto
    · exact slope

/-- The tangent in moment order has the same leading order as the trace,
with coefficient multiplied by that order. -/
theorem joint_limit (E : I → ℝ) (m : ℕ) (vanish : ∀ k < m+1, variation E k 0=0) :
    Tendsto (fun t => oddTrace E t/t^(m+1)) (𝓝[≠] 0)
      (𝓝 (variation E (m+1) 0/((m+1).factorial : ℝ))) ∧
    Tendsto (fun t => t*variation E 1 t/t^(m+1)) (𝓝[≠] 0)
      (𝓝 (variation E (m+1) 0/(m.factorial : ℝ))) := by
  constructor
  · simpa only [Nat.zero_add,variation_zero_order] using
      variation_limit E (m+1) 0 (by simpa only [Nat.zero_add] using vanish)
  · have h := variation_limit E m 1 (fun k hk => vanish (1+k) (by omega))
    rw [Nat.add_comm 1 m] at h
    apply h.congr'
    filter_upwards [show ∀ᶠ t : ℝ in 𝓝[≠] 0, t≠0 from self_mem_nhdsWithin] with t ht
    rw [pow_succ]
    field_simp

#print axioms variation_zero_order
#print axioms variation_origin
#print axioms variation_deriv
#print axioms variation_limit
#print axioms joint_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.PrimeCalibration.Multiplicity.Resolution
