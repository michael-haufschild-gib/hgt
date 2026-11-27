import GaloisForLFunctions.RHTower.PrimeZetaOneLineConvergence
import GaloisForLFunctions.RHTower.PrimeHarmonicLogLower
import Mathlib.Analysis.Complex.Circle

/-! # Fourier coefficients of the elementary harmonic prime ensemble -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Real Finset Filter
open scoped Topology

/-- Primes up to N+2, so that every cutoff contains an elementary state. -/
def primes (N : ℕ) := Nat.primesBelow (N+3)

def weight (p : ℕ) : ℝ := (p : ℝ)⁻¹

def mass (N : ℕ) := ∑ p ∈ primes N, weight p

def phase (t : ℝ) (p : ℕ) : Circle := Circle.exp (-(t*log p))

theorem weight_nonneg (p : ℕ) : 0 ≤ weight p := inv_nonneg.mpr (Nat.cast_nonneg p)

theorem mass_pos (N : ℕ) : 0 < mass N := by
  apply sum_pos' (fun p _ => weight_nonneg p)
  refine ⟨2,?_,by norm_num [weight]⟩
  exact Nat.mem_primesBelow.mpr ⟨by omega,Nat.prime_two⟩

theorem mass_diverges : Tendsto mass atTop atTop := by
  have shifted : Tendsto (fun N : ℕ => (N : ℝ)+3) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have logs := tendsto_log_atTop.comp (tendsto_log_atTop.comp shifted)
  have lower : Tendsto (fun N : ℕ => log (log ((N : ℝ)+3))-1) atTop atTop := by
    simpa only [sub_eq_add_neg,Function.comp_def] using
      (tendsto_atTop_add_const_right atTop (-1 : ℝ) logs)
  apply tendsto_atTop_mono (fun N => ?_) lower
  have bound := _root_.RHTower.log_log_sub_one_le_sum_primesBelow_inv (N+2) (by omega)
  simpa only [mass,primes,weight,Nat.cast_add,Nat.cast_ofNat,add_assoc,show (2 : ℝ)+1=3 by norm_num]
    using bound

private theorem primes_eq (N : ℕ) : primes N=(Icc 0 (N+2)).filter Nat.Prime := by
  ext p
  simp only [primes,Nat.mem_primesBelow,mem_filter,mem_Icc,zero_le,true_and]
  exact and_congr_left fun _ => by omega

/-- Integrand of the kth circle moment, with the negative Fourier sign. -/
def coefficient (t : ℝ) (k : ℤ) (N : ℕ) :=
  (∑ p ∈ primes N, (weight p : ℂ)*(phase t p : ℂ)^(-k)) / (mass N : ℂ)

private theorem summand (p : ℕ) (hp : p.Prime) (t : ℝ) (k : ℤ) :
    (weight p : ℂ)*(phase t p : ℂ)^(-k) =
      (p : ℂ)^(-1-((-(k : ℝ)*t : ℝ) : ℂ)*Complex.I) := by
  rw [_root_.RHTower.natCast_cpow_neg_one_sub _ hp.pos]
  congr 1
  rw [phase,Circle.coe_exp,←Complex.exp_int_mul,_root_.RHTower.logPhase]
  congr 1
  push_cast
  ring

/-- Every nonconstant Fourier coefficient vanishes in the large cutoff
limit at each nonzero height. Only prime-ordered convergence is used. -/
theorem nonzero_mode (t : ℝ) (ht : t≠0) (k : ℤ) (hk : k≠0) :
    Tendsto (coefficient t k) atTop (𝓝 0) := by
  let frequency := -(k : ℝ)*t
  have nonzero : frequency≠0 := mul_ne_zero (neg_ne_zero.mpr (Int.cast_ne_zero.mpr hk)) ht
  obtain ⟨L,hL⟩ := _root_.RHTower.exists_tendsto_primeCpowSum nonzero
  have cutoff : Tendsto (fun N : ℕ => ((N+2 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  have numerator : Tendsto (fun N => ∑ p ∈ primes N, (weight p : ℂ)*(phase t p : ℂ)^(-k))
      atTop (𝓝 L) := by
    apply (hL.comp cutoff).congr
    intro N
    simp only [Function.comp_apply,Nat.floor_natCast]
    rw [primes_eq]
    exact sum_congr rfl (fun p hp => (summand p (mem_filter.mp hp).2 t k).symm)
  have inv : Tendsto (fun N => ((mass N : ℂ))⁻¹) atTop (𝓝 0) := by
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_inv_atTop_zero.comp mass_diverges)
    change Tendsto (fun N => (((mass N)⁻¹ : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ)) at h
    simpa only [Complex.ofReal_inv] using h
  change Tendsto (fun N => _ / (mass N : ℂ)) atTop (𝓝 0)
  simpa only [div_eq_mul_inv,mul_zero] using numerator.mul inv

theorem zero_mode (t : ℝ) (N : ℕ) : coefficient t 0 N=1 := by
  have nz := Complex.ofReal_ne_zero.mpr (mass_pos N).ne'
  simp only [coefficient,neg_zero,zpow_zero,mul_one,←Complex.ofReal_sum]
  exact div_self nz

theorem zero_height_coefficient (k : ℤ) (N : ℕ) : coefficient 0 k N=1 := by
  simpa only [coefficient,phase,zero_mul,neg_zero,Circle.exp_zero,Circle.coe_one,one_zpow,mul_one]
    using zero_mode 0 N

#print axioms zero_height_coefficient
#print axioms weight_nonneg
#print axioms mass_pos
#print axioms mass_diverges
#print axioms nonzero_mode
#print axioms zero_mode

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
