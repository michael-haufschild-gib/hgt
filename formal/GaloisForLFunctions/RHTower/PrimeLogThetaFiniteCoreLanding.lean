import GaloisForLFunctions.RHTower.PrimeLogCubicLaplaceGraphFormation
import GaloisForLFunctions.RHTower.MobiusThetaComplexSourceToXiLanding

/-!
# Prime-log theta finite-core landing

This module gives the literal theta action on the finite core of the critical prime-log
Laplace graph.  A prime coordinate is sent to the corresponding logarithmic translate of
the actual theta-cusp source, with its fixed `2 log(p)^2 / sqrt(p)` coefficient.  The
Fourier--Laplace transform factors before any zero or quotient specialization.

At `w = -I t`, for `0 < t < 1`, the exact product identity is

```text
t * FL(Theta(l))(-I t) = XiC(-I t) * (A_* l)(t).
```

It is deliberately a product identity, not division by `XiC`, and does not claim a closed
graph extension, cubic-clock covariance, a Calderón class, or an Xi escape pairing.  Those
are the remaining PHCCED gate.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

/-- Literal theta-cusp image of one prime coordinate of the critical Laplace core. -/
def primeLogThetaSourceTerm (p : Nat.Primes) (x : ℝ) : ℂ :=
  ((2 * Real.log (p : ℝ) ^ 2 / Real.sqrt (p : ℝ) : ℝ) : ℂ) *
    (thetaCuspFullSource (x - Real.log (p : ℝ)) : ℂ)

/-- Literal finite-prime theta synthesis. -/
def primeLogThetaSource (l : Nat.Primes →₀ ℂ) (x : ℝ) : ℂ :=
  ∑ p ∈ l.support, l p * primeLogThetaSourceTerm p x

/-- Fourier--Laplace transform of the literal finite-prime theta synthesis. -/
def primeLogThetaFourierLaplace (l : Nat.Primes →₀ ℂ) (w : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-I * w * (x : ℂ)) * primeLogThetaSource l x

/-- One translated theta packet factors into its prime character and the base theta integrand. -/
theorem primeLogThetaSourceTerm_integrand_eq
    (p : Nat.Primes) (w : ℂ) (x : ℝ) :
    Complex.exp (-I * w * (x : ℂ)) * primeLogThetaSourceTerm p x =
      ((2 * Real.log (p : ℝ) ^ 2 / Real.sqrt (p : ℝ) : ℝ) : ℂ) *
        Complex.exp (-I * w * (Real.log (p : ℝ) : ℂ)) *
          thetaCuspFourierLaplaceIntegrand w (x - Real.log (p : ℝ)) := by
  rw [primeLogThetaSourceTerm, thetaCuspFourierLaplaceIntegrand]
  rw [show Complex.exp (-I * w * (x : ℂ)) =
      Complex.exp (-I * w * (Real.log (p : ℝ) : ℂ)) *
        Complex.exp (-I * w * ((x - Real.log (p : ℝ) : ℝ) : ℂ)) by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring]
  ring

/-- Each finite-core theta packet is integrable throughout the honest theta strip. -/
theorem integrable_primeLogThetaSourceTerm_integrand
    {w : ℂ} (hw : |w.im| < 1) (p : Nat.Primes) :
    Integrable (fun x : ℝ =>
      Complex.exp (-I * w * (x : ℂ)) * primeLogThetaSourceTerm p x) := by
  rw [show (fun x : ℝ =>
      Complex.exp (-I * w * (x : ℂ)) * primeLogThetaSourceTerm p x) =
      fun x => ((2 * Real.log (p : ℝ) ^ 2 / Real.sqrt (p : ℝ) : ℝ) : ℂ) *
        Complex.exp (-I * w * (Real.log (p : ℝ) : ℂ)) *
          thetaCuspFourierLaplaceIntegrand w (x - Real.log (p : ℝ)) by
    funext x
    exact primeLogThetaSourceTerm_integrand_eq p w x]
  exact ((integrable_thetaCuspFourierLaplaceIntegrand hw).comp_add_right
    (-Real.log (p : ℝ))).const_mul _

/-- Exact Fourier--Laplace transform of one literal finite-core theta packet. -/
theorem integral_primeLogThetaSourceTerm_integrand
    {w : ℂ} (hw : |w.im| < 1) (p : Nat.Primes) :
    ∫ x : ℝ, Complex.exp (-I * w * (x : ℂ)) * primeLogThetaSourceTerm p x =
      ((2 * Real.log (p : ℝ) ^ 2 / Real.sqrt (p : ℝ) : ℝ) : ℂ) *
        Complex.exp (-I * w * (Real.log (p : ℝ) : ℂ)) * XiC w := by
  rw [show (fun x : ℝ =>
      Complex.exp (-I * w * (x : ℂ)) * primeLogThetaSourceTerm p x) =
      fun x => ((2 * Real.log (p : ℝ) ^ 2 / Real.sqrt (p : ℝ) : ℝ) : ℂ) *
        Complex.exp (-I * w * (Real.log (p : ℝ) : ℂ)) *
          thetaCuspFourierLaplaceIntegrand w (x - Real.log (p : ℝ)) by
    funext x
    exact primeLogThetaSourceTerm_integrand_eq p w x]
  rw [integral_const_mul]
  rw [show (∫ x : ℝ, thetaCuspFourierLaplaceIntegrand w
      (x - Real.log (p : ℝ))) = ∫ x : ℝ, thetaCuspFourierLaplaceIntegrand w x by
    simpa only [sub_eq_add_neg] using
      (integral_add_right_eq_self (thetaCuspFourierLaplaceIntegrand w)
        (-Real.log (p : ℝ)))]
  rw [← thetaCuspFourierLaplace]
  rw [thetaCuspFourierLaplace_eq_XiC_on_strip]
  simpa [thetaCuspFourierLaplaceStrip] using (abs_lt.mp hw)

/-- The literal finite theta synthesis factors as `XiC` times its all-prime source symbol. -/
theorem primeLogThetaFourierLaplace_eq
    (l : Nat.Primes →₀ ℂ) {w : ℂ} (hw : |w.im| < 1) :
    primeLogThetaFourierLaplace l w =
      XiC w * ∑ p ∈ l.support, l p *
        (((2 * Real.log (p : ℝ) ^ 2 / Real.sqrt (p : ℝ) : ℝ) : ℂ) *
          Complex.exp (-I * w * (Real.log (p : ℝ) : ℂ))) := by
  unfold primeLogThetaFourierLaplace
  simp_rw [primeLogThetaSource]
  rw [show (fun x : ℝ =>
      Complex.exp (-I * w * (x : ℂ)) *
        ∑ p ∈ l.support, l p * primeLogThetaSourceTerm p x) =
      fun x : ℝ => ∑ p ∈ l.support,
        Complex.exp (-I * w * (x : ℂ)) * (l p * primeLogThetaSourceTerm p x) by
    funext x
    rw [Finset.mul_sum]]
  rw [MeasureTheory.integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [show (fun x : ℝ =>
        Complex.exp (-I * w * (x : ℂ)) * (l p * primeLogThetaSourceTerm p x)) =
        fun x : ℝ => l p * (Complex.exp (-I * w * (x : ℂ)) *
          primeLogThetaSourceTerm p x) by
      funext x
      ring, integral_const_mul, integral_primeLogThetaSourceTerm_integrand hw]
    ring
  · intro p hp
    rw [show (fun x : ℝ =>
        Complex.exp (-I * w * (x : ℂ)) * (l p * primeLogThetaSourceTerm p x)) =
        fun x : ℝ => l p * (Complex.exp (-I * w * (x : ℂ)) *
          primeLogThetaSourceTerm p x) by
      funext x
      ring]
    exact (integrable_primeLogThetaSourceTerm_integrand hw p).const_mul _

/--
On the imaginary Laplace ray inside the theta strip, the theta finite-core transform is
exactly the critical graph report times `XiC`, without any division by `XiC`.
-/
theorem mul_primeLogThetaFourierLaplace_neg_I_eq_XiC_mul_graph
    (l : Nat.Primes →₀ ℂ) {t : ℝ} (ht : 0 < t) (htstrip : t < 1) :
    (t : ℂ) * primeLogThetaFourierLaplace l (-I * (t : ℂ)) =
      XiC (-I * (t : ℂ)) *
        ∑ p ∈ l.support, l p * primeLogCriticalLaplaceFeatureC p t := by
  have hw : |(-I * (t : ℂ)).im| < 1 := by
    rw [Complex.mul_im]
    norm_num
    rw [abs_of_nonneg ht.le]
    exact htstrip
  rw [primeLogThetaFourierLaplace_eq l hw]
  calc
    (t : ℂ) * (XiC (-I * (t : ℂ)) * ∑ p ∈ l.support,
        l p * (((2 * Real.log (p : ℝ) ^ 2 / Real.sqrt (p : ℝ) : ℝ) : ℂ) *
          Complex.exp (-I * (-I * (t : ℂ)) * (Real.log (p : ℝ) : ℂ)))) =
        (t : ℂ) * ∑ p ∈ l.support,
        XiC (-I * (t : ℂ)) *
          (l p * (((2 * Real.log (p : ℝ) ^ 2 / Real.sqrt (p : ℝ) : ℝ) : ℂ) *
            Complex.exp (-I * (-I * (t : ℂ)) * (Real.log (p : ℝ) : ℂ)))) := by
      rw [Finset.mul_sum]
    _ =
        ∑ p ∈ l.support, (t : ℂ) *
          (XiC (-I * (t : ℂ)) *
            (l p * (((2 * Real.log (p : ℝ) ^ 2 / Real.sqrt (p : ℝ) : ℝ) : ℂ) *
              Complex.exp (-I * (-I * (t : ℂ)) * (Real.log (p : ℝ) : ℂ))))) := by
      rw [Finset.mul_sum]
    _ = ∑ p ∈ l.support, XiC (-I * (t : ℂ)) *
          (l p * primeLogCriticalLaplaceFeatureC p t) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [primeLogCriticalLaplaceFeatureC, primeLogCriticalLaplaceFeature]
      have hexparg : -I * (-I * (t : ℂ)) * (Real.log (p : ℝ) : ℂ) =
          (-(Real.log (p : ℝ) * t) : ℝ) := by
        push_cast
        calc
          -I * (-I * (t : ℂ)) * Complex.log (p : ℂ) =
              ((-I) * (-I)) * (t : ℂ) * Complex.log (p : ℂ) := by ring
          _ = (-1 : ℂ) * (t : ℂ) * Complex.log (p : ℂ) := by
            rw [show (-I : ℂ) * (-I) = -1 by norm_num]
          _ = -(Complex.log (p : ℂ) * (t : ℂ)) := by ring
      rw [hexparg, show Complex.exp ((-(Real.log (p : ℝ) * t) : ℝ) : ℂ) =
          (Real.exp (-(Real.log (p : ℝ) * t)) : ℂ) by
        rw [Complex.ofReal_exp]]
      push_cast
      ring
    _ = XiC (-I * (t : ℂ)) *
        ∑ p ∈ l.support, l p * primeLogCriticalLaplaceFeatureC p t := by
      rw [Finset.mul_sum]

end

end RHTower
