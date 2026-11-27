import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.TiltWindow
import GaloisForLFunctions.RestrictedFactorizationCalculus.PrimeWindowsInLogarithmicCoordinates
import GaloisForLFunctions.RHTower.LogIntegralLaplaceComparison

/-! # Derivative of the finite elementary tilt in log-prime coordinates -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover

open Finset Real Filter
open GaloisForLFunctions.RestrictedFactorizationCalculus

private theorem primeSet {N : ℕ} (hN : 2≤N) : primes (cutoff N)=Nat.primesLE N := by
  ext p
  rw [mem_cutoff (by exact_mod_cast hN : (2:ℝ)≤N),Nat.mem_primesLE]
  simp only [Nat.cast_le]
  exact and_comm

/-- Differentiating in the tilt parameter inserts the logarithmic prime
weight. The remaining test is a pure exponential on the unit interval. -/
theorem correction_deriv {N : ℕ} (hN : 2≤N) (w : ℝ) :
    HasDerivAt (fun q => tiltCorrection q N)
      (primeCoordinateSum (log N) (fun v => exp (w*v)) N) w := by
  have hfun : (fun q => tiltCorrection q N) = fun q =>
      ∑ p ∈ Nat.primesLE N, (exp (q*(log p/log N))-1)/(p:ℝ) := by
    funext q
    simp only [tiltCorrection,powerMass,primeSet hN,←sum_sub_distrib,zero_sub,rpow_neg_one]
    apply sum_congr rfl
    intro p hp
    have pp : 0<(p:ℝ) := Nat.cast_pos.mpr (Nat.mem_primesLE.mp hp).2.pos
    rw [rpow_sub pp,rpow_one,rpow_def_of_pos pp,show log (p:ℝ)*(q/log N)=q*(log p/log N) by ring]
    ring
  rw [hfun]
  have term (p : ℕ) : HasDerivAt (fun q : ℝ => (exp (q*(log p/log N))-1)/(p:ℝ))
      ((log p/p/log N)*exp (w*(log p/log N))) w := by
    have h := (((hasDerivAt_id w).mul_const (log p/log N)).exp.sub_const 1).div_const (p:ℝ)
    convert h using 1 <;> first | rfl | dsimp; ring
  exact HasDerivAt.fun_sum (fun i _ => term i)

private def primitive (q x : ℝ) := if q=0 then x else exp (q*x)/q

private theorem primitive_deriv (q x : ℝ) : HasDerivAt (primitive q) (exp (q*x)) x := by
  by_cases h : q=0
  · subst q
    rw [show primitive 0=id from funext (fun y => by simp [primitive]),zero_mul,exp_zero]
    exact hasDerivAt_id x
  · have hd := (((hasDerivAt_id x).const_mul q).exp).div_const q
    rw [show primitive q = fun y => exp (q*y)/q from funext (fun y => by simp [primitive,h])]
    simpa [h] using hd

private theorem primitive_ends (q : ℝ) :
    primitive q 1 - primitive q 0 = _root_.RHTower.logIntegralKernel q := by
  by_cases h : q=0
  · subst q; simp [primitive,_root_.RHTower.logIntegralKernel_zero]
  · rw [_root_.RHTower.logIntegralKernel_of_ne h]
    simp only [primitive,if_neg h,mul_one,mul_zero,exp_zero]
    ring

private theorem test_bound (q : ℝ) {x : ℝ} (hx : x∈Set.Icc (-1:ℝ) 2) :
    |exp (q*x)| ≤ exp (2*|q|) := by
  rw [abs_of_pos (exp_pos _),exp_le_exp]
  have hab : |x|≤2 := abs_le.mpr ⟨by linarith only [hx.1],hx.2⟩
  calc
    q*x ≤ |q*x| := le_abs_self _
    _ = |q| * |x| := abs_mul _ _
    _ ≤ |q| * 2 := mul_le_mul_of_nonneg_left hab (abs_nonneg _)
    _ = _ := mul_comm _ _

private theorem test_lipschitz (q : ℝ) {x z : ℝ} (hx : x∈Set.Icc (-1:ℝ) 2)
    (hz : z∈Set.Icc (-1:ℝ) 2) :
    |exp (q*x)-exp (q*z)| ≤ |q| * exp (2*|q|)*|x-z| := by
  have hd (v : ℝ) := ((hasDerivAt_id v).const_mul q).exp
  have h := (convex_Icc (-1:ℝ) 2).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun v : ℝ => exp (q*v)) (fun v _ => (hd v).hasDerivWithinAt)
    (C := |q| * exp (2*|q|)) (fun v hv => by
      simp only [Real.norm_eq_abs,abs_mul,mul_one,id_eq]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (test_bound q hv) (abs_nonneg _)) hz hx
  simpa only [Real.norm_eq_abs] using h

/-- A uniform derivative error for real tilts. Its only arithmetic input
is the sharp quadrature bound for the logarithmic prime coordinates. -/
theorem derivative_error {N : ℕ} (hN : 2≤N) (hδ : coordinateRadius (log N)≤1) (q : ℝ) :
    |primeCoordinateSum (log N) (fun v => exp (q*v)) N - _root_.RHTower.logIntegralKernel q| ≤
      coordinateRadius (log N) * ((2+3*|q|)*exp (2*|q|)) := by
  have lN := log_pos (show (1:ℝ)<N by exact_mod_cast (by omega : 1<N))
  have h0 : 0≤coordinateRadius (log N) := div_nonneg
    (add_nonneg _root_.RHTower.Sieve.mertensBlockGapConst_nonneg (log_nonneg (by norm_num))) lN.le
  have incl : Set.Icc (log (1:ℕ)/log N-coordinateRadius (log N)) (log N/log N+coordinateRadius (log N))
      ⊆ Set.Icc (-1:ℝ) 2 := by
    simp only [Nat.cast_one,log_one,zero_div,zero_sub,div_self lN.ne']
    intro v hv
    exact ⟨by linarith only [hv.1,hδ],by linarith only [hv.2,hδ]⟩
  have bound := sharp_prime_quadrature (h := log N) lN
    (mul_nonneg (abs_nonneg q) (exp_pos (2*|q|)).le) (exp_pos (2*|q|)).le
    1 N le_rfl (by omega) (fun v => exp (q*v)) (primitive q)
    (fun v _ => primitive_deriv q v) (fun _ hx _ hz => test_lipschitz q (incl hx) (incl hz))
    (fun _ hx => test_bound q (incl hx))
  simp only [Nat.cast_one,log_one,zero_div,div_self lN.ne',primeCoordinateSum,Nat.primesLE_one,
    sum_empty,sub_zero,primitive_ends] at bound
  refine bound.trans (mul_le_mul_of_nonneg_left ?_ h0)
  have hf := mul_nonneg (abs_nonneg q) (exp_pos (2*|q|)).le
  nlinarith only [mul_nonneg hf (sub_nonneg.mpr hδ)]

#print axioms correction_deriv
#print axioms derivative_error

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover
