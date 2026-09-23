import GaloisForLFunctions.RHTower.PrimeLogCubicClockGraphCoreCovariance
import GaloisForLFunctions.RHTower.PrimeLogThetaFiniteCoreLanding
import GaloisForLFunctions.RHTower.XiEulerSafeCauchyLoss

/-!
# Denominator-free cubic theta jet on the literal prime-log core

The finite theta landing factors as

```text
t * Theta_l(-i t) = xiCent(t) * A_l(t)
```

inside the honest theta strip.  Dividing by `xiCent` would be circular at its zeros.  This file
instead constructs the literal relative Wronskian ladder

```text
W_m(y) = xiCent * (-d/dt + 1/t)(y) + m * xiCent' * y.
```

For a level-`m` section `xiCent^m * f`, the `xiCent'` term cancels the differentiated power
without any inverse:

```text
W_m(xiCent^m * f) = xiCent^(m+1) * (-d/dt + 1/t)(f).
```

Combined with the literal cubic prime-log graph clock, the third theta jet is exactly

```text
W_3 W_2 W_1 (t * Theta_l(-i t))
  = xiCent(t)^(4 : ℕ) * sum_p l_p log(p)^(3 : ℕ) phi_p(t).
```

Every equality is a positive-time germ in the theta strip.  No zero is selected and no `Xi`
factor is inverted.  The surviving factor `xiCent^(4 : ℕ)` identifies the relative four-level graph
that any later complex-zero extension must retain; this real-ray theorem itself makes no
zero-evaluation claim.

This establishes only finite-core cubic theta covariance.  It does not construct the required
closed `Graph(cl A_*)` extension, Calderón class, boundary index, or same-representative nuclear
budget.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal InnerProduct LinearPMap

namespace RHTower

noncomputable section

/-- The literal centered-Xi factor on the positive theta ray. -/
def primeLogThetaXiRay (t : ℝ) : ℂ := xiCent (t : ℂ)

/-- Literal finite theta landing on the positive imaginary Fourier--Laplace ray. -/
def primeLogThetaRay (l : Nat.Primes →₀ ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) * primeLogThetaFourierLaplace l (-I * (t : ℂ))

/-- The denominator-free relative Wronskian step from Xi level `m` to level `m + 1`. -/
def primeLogThetaWronskianStep (m : ℕ) (y : ℝ → ℂ) (t : ℝ) : ℂ :=
  primeLogThetaXiRay t * primeLogCriticalLaplaceEuler y t +
    (m : ℂ) * deriv primeLogThetaXiRay t * y t

private theorem hasDerivAt_primeLogThetaXiRay (t : ℝ) :
    HasDerivAt primeLogThetaXiRay (deriv xiCent (t : ℂ)) t := by
  exact (xiCent_differentiable (t : ℂ)).hasDerivAt.comp_ofReal

/-- The finite theta ray is exactly the first Xi level of the literal graph core. -/
theorem primeLogThetaRay_eq_XiRay_mul_core
    (l : Nat.Primes →₀ ℂ) {t : ℝ} (ht : 0 < t) (htstrip : t < 1) :
    primeLogThetaRay l t =
      primeLogThetaXiRay t * primeLogCriticalLaplaceClockedMass 0 l t := by
  unfold primeLogThetaRay primeLogThetaXiRay
  rw [mul_primeLogThetaFourierLaplace_neg_I_eq_XiC_mul_graph l ht htstrip,
    xiCent_eq_XiC]
  simp only [primeLogCriticalLaplaceClockedMass, pow_zero, mul_one]

private theorem differentiableAt_primeLogCriticalLaplaceClockedMass
    (n : ℕ) (l : Nat.Primes →₀ ℂ) (t : ℝ) :
    DifferentiableAt ℝ (primeLogCriticalLaplaceClockedMass n l) t := by
  unfold primeLogCriticalLaplaceClockedMass
  have hfun : (fun s : ℝ => ∑ p ∈ l.support,
      l p * (Real.log (p : ℝ) : ℂ) ^ n *
        primeLogCriticalLaplaceFeatureC p s) =
      ∑ p ∈ l.support, fun s : ℝ =>
        l p * (Real.log (p : ℝ) : ℂ) ^ n *
          primeLogCriticalLaplaceFeatureC p s := by
    funext s
    simp
  rw [hfun]
  apply DifferentiableAt.sum
  intro p hp
  unfold primeLogCriticalLaplaceFeatureC primeLogCriticalLaplaceFeature
  fun_prop

private theorem hasDerivAt_primeLogThetaXiRay_pow (m : ℕ) (t : ℝ) :
    HasDerivAt (primeLogThetaXiRay ^ m)
      ((m : ℂ) * primeLogThetaXiRay t ^ (m - 1) * deriv xiCent (t : ℂ)) t := by
  simpa only [Pi.pow_apply] using (hasDerivAt_primeLogThetaXiRay t).pow m

/-- One Wronskian step cancels the Xi-power derivative and raises exactly one literal source-clock
degree, with no inverse-Xi expression. -/
theorem primeLogThetaWronskianStep_clockedMass
    (m n : ℕ) (l : Nat.Primes →₀ ℂ) {t : ℝ} (ht : 0 < t) :
    primeLogThetaWronskianStep m
      ((primeLogThetaXiRay ^ m) * primeLogCriticalLaplaceClockedMass n l) t =
      primeLogThetaXiRay t ^ (m + 1) *
        primeLogCriticalLaplaceClockedMass (n + 1) l t := by
  have hprod := ((hasDerivAt_primeLogThetaXiRay_pow m t).mul
    (differentiableAt_primeLogCriticalLaplaceClockedMass n l t).hasDerivAt).deriv
  have hXi : deriv primeLogThetaXiRay t = deriv xiCent (t : ℂ) :=
    (hasDerivAt_primeLogThetaXiRay t).deriv
  have hsource : -deriv (primeLogCriticalLaplaceClockedMass n l) t +
      primeLogCriticalLaplaceClockedMass n l t / (t : ℂ) =
      primeLogCriticalLaplaceClockedMass (n + 1) l t := by
    simpa [primeLogCriticalLaplaceEuler] using
      primeLogCriticalLaplaceEuler_clockedMass n l ht
  unfold primeLogThetaWronskianStep primeLogCriticalLaplaceEuler
  rw [hXi, hprod]
  simp only [Pi.mul_apply, Pi.pow_apply]
  calc
    primeLogThetaXiRay t *
          (-(↑m * primeLogThetaXiRay t ^ (m - 1) * deriv xiCent (t : ℂ) *
                primeLogCriticalLaplaceClockedMass n l t +
              primeLogThetaXiRay t ^ m *
                deriv (primeLogCriticalLaplaceClockedMass n l) t) +
            primeLogThetaXiRay t ^ m *
              primeLogCriticalLaplaceClockedMass n l t / ↑t) +
        ↑m * deriv xiCent (t : ℂ) *
          (primeLogThetaXiRay t ^ m *
            primeLogCriticalLaplaceClockedMass n l t) =
        primeLogThetaXiRay t ^ (m + 1) *
          (-deriv (primeLogCriticalLaplaceClockedMass n l) t +
            primeLogCriticalLaplaceClockedMass n l t / ↑t) := by
      cases m with
      | zero => norm_num
      | succ m =>
          simp only [Nat.cast_add, Nat.cast_one, Nat.succ_sub_one, pow_succ]
          ring
    _ = primeLogThetaXiRay t ^ (m + 1) *
        primeLogCriticalLaplaceClockedMass (n + 1) l t := by rw [hsource]

/-- Iteration of the relative Wronskian step.  Its level records the Xi-power filtration rather
than erasing it by scalar division. -/
def primeLogThetaWronskianIterate : ℕ → ℕ → (ℝ → ℂ) → (ℝ → ℂ)
  | _m, 0, y => y
  | m, n + 1, y => fun t =>
      primeLogThetaWronskianStep (m + n)
        (primeLogThetaWronskianIterate m n y) t

/-- The complete relative Wronskian ladder transports every Xi-level finite source section by
the literal source-clock power. -/
theorem primeLogThetaWronskianIterate_clockedMass
    (m n : ℕ) (l : Nat.Primes →₀ ℂ) {t : ℝ} (ht : 0 < t) :
    primeLogThetaWronskianIterate m n
      ((primeLogThetaXiRay ^ m) * primeLogCriticalLaplaceClockedMass 0 l) t =
      primeLogThetaXiRay t ^ (m + n) *
        primeLogCriticalLaplaceClockedMass n l t := by
  induction n generalizing t with
  | zero => simp [primeLogThetaWronskianIterate]
  | succ n ih =>
      have hlocal : primeLogThetaWronskianIterate m n
          ((primeLogThetaXiRay ^ m) * primeLogCriticalLaplaceClockedMass 0 l) =ᶠ[𝓝 t]
          ((primeLogThetaXiRay ^ (m + n)) *
            primeLogCriticalLaplaceClockedMass n l) := by
        filter_upwards [Ioi_mem_nhds ht] with s hs
        exact ih (show 0 < s from hs)
      change primeLogThetaWronskianStep (m + n)
        (primeLogThetaWronskianIterate m n
          ((primeLogThetaXiRay ^ m) *
            primeLogCriticalLaplaceClockedMass 0 l)) t = _
      unfold primeLogThetaWronskianStep primeLogCriticalLaplaceEuler
      rw [hlocal.deriv_eq, hlocal.self_of_nhds]
      change primeLogThetaWronskianStep (m + n)
        ((primeLogThetaXiRay ^ (m + n)) *
          primeLogCriticalLaplaceClockedMass n l) t = _
      simpa [Nat.add_assoc] using
        primeLogThetaWronskianStep_clockedMass (m + n) n l ht

/-- The literal theta ray has exact relative Wronskian jets throughout the theta strip. -/
theorem primeLogThetaWronskianIterate_thetaRay
    (n : ℕ) (l : Nat.Primes →₀ ℂ) {t : ℝ}
    (ht : 0 < t) (htstrip : t < 1) :
    primeLogThetaWronskianIterate 1 n (primeLogThetaRay l) t =
      primeLogThetaXiRay t ^ (1 + n) *
        primeLogCriticalLaplaceClockedMass n l t := by
  induction n generalizing t with
  | zero =>
      rw [primeLogThetaWronskianIterate]
      have h := primeLogThetaRay_eq_XiRay_mul_core l ht htstrip
      simpa only [Pi.one_apply, Nat.add_zero, pow_one] using h
  | succ n ih =>
      have hlocal : primeLogThetaWronskianIterate 1 n
          (primeLogThetaRay l) =ᶠ[𝓝 t]
          ((primeLogThetaXiRay ^ (1 + n)) *
            primeLogCriticalLaplaceClockedMass n l) := by
        filter_upwards [Ioo_mem_nhds ht htstrip] with s hs
        exact ih hs.1 hs.2
      change primeLogThetaWronskianStep (1 + n)
        (primeLogThetaWronskianIterate 1 n (primeLogThetaRay l)) t = _
      unfold primeLogThetaWronskianStep primeLogCriticalLaplaceEuler
      rw [hlocal.deriv_eq, hlocal.self_of_nhds]
      change primeLogThetaWronskianStep (1 + n)
        ((primeLogThetaXiRay ^ (1 + n)) *
          primeLogCriticalLaplaceClockedMass n l) t = _
      simpa [Nat.add_assoc] using
        primeLogThetaWronskianStep_clockedMass (1 + n) n l ht

/-- **Literal cubic theta covariance.**  The third denominator-free theta Wronskian jet is the
fourth Xi-level representative of the exact `(log p)^(3 : ℕ)` finite graph core. -/
theorem primeLogThetaWronskian_cubic_thetaRay
    (l : Nat.Primes →₀ ℂ) {t : ℝ}
    (ht : 0 < t) (htstrip : t < 1) :
    primeLogThetaWronskianIterate 1 3 (primeLogThetaRay l) t =
      primeLogThetaXiRay t ^ 4 *
        primeLogCriticalLaplaceClockedMass 3 l t := by
  simpa using primeLogThetaWronskianIterate_thetaRay 3 l ht htstrip

end

end RHTower
