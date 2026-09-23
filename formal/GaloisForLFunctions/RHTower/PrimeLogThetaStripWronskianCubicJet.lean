import GaloisForLFunctions.RHTower.PrimeLogThetaFiniteCoreLanding

/-!
# Complex-strip cubic theta jet on the literal prime-log core

The literal finite-prime theta transform has the exact, pre-divisor factorization

```text
Theta_l(w) = XiC(w) Q_0,l(w),
Q_n,l(w) = sum_p l_p (2 log(p)^(2 : ℕ) / sqrt(p)) log(p)^n exp(-i w log(p)).
```

This file differentiates that actual finite theta formula in the full strip `|Im w| < 1`.
With `D = i d/dw`, the source clock is exactly `D Q_n = Q_(n+1)`.  The relative,
denominator-free Wronskian step

```text
W_m(y) = XiC * D(y) - m * D(XiC) * y
```

therefore satisfies `W_m(XiC^m Q_n) = XiC^(m+1) Q_(n+1)` without inverting `XiC`.
Its cubic iterate on the literal theta transform is `XiC^(4 : ℕ) Q_3`.

Consequently, at any zero of `XiC` in the theta strip, scalar cubic evaluation kills every
prime-labelled theta jet even though the corresponding one-prime cubic source symbol is nonzero.
This is a source-specific scalar-loss theorem.  Its positive survivor is the four-level
`XiC` filtration: a later literal `Graph(cl A_*)` theta quotient must retain that filtration;
it cannot be replaced by pointwise scalar evaluation at a zero.

This file does not construct the required closed graph extension, theta Calderón class,
boundary-index pairing, or same-representative nuclear budget.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal InnerProduct LinearPMap

namespace RHTower

noncomputable section

/-- Complex critical clock on the literal theta strip. -/
def primeLogThetaStripClock (f : ℂ → ℂ) (w : ℂ) : ℂ := I * deriv f w

/-- Fixed literal coefficient of one translated prime theta packet. -/
def primeLogThetaStripCoefficient (p : Nat.Primes) : ℂ :=
  ((2 * Real.log (p : ℝ) ^ 2 / Real.sqrt (p : ℝ) : ℝ) : ℂ)

/-- The finite-prime source symbol at clock degree `n` in the literal theta strip. -/
def primeLogThetaStripSymbol (n : ℕ) (l : Nat.Primes →₀ ℂ) (w : ℂ) : ℂ :=
  ∑ p ∈ l.support, l p * primeLogThetaStripCoefficient p *
    (Real.log (p : ℝ) : ℂ) ^ n * Complex.exp (-I * w * (Real.log (p : ℝ) : ℂ))

private theorem hasDerivAt_primeLogThetaStripPhase (p : Nat.Primes) (w : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.exp (-I * z * (Real.log (p : ℝ) : ℂ)))
      (Complex.exp (-I * w * (Real.log (p : ℝ) : ℂ)) *
        (-I * (Real.log (p : ℝ) : ℂ))) w := by
  have hlin : HasDerivAt (fun z : ℂ => -I * z * (Real.log (p : ℝ) : ℂ))
      (-I * (Real.log (p : ℝ) : ℂ)) w := by
    have hbase : HasDerivAt (fun z : ℂ => -I * z) (-I) w := by
      simpa using (hasDerivAt_id w).const_mul (-I)
    exact hbase.mul_const (Real.log (p : ℝ) : ℂ)
  simpa only [Function.comp_def] using
    (Complex.hasDerivAt_exp (-I * w * (Real.log (p : ℝ) : ℂ))).comp w hlin

private theorem hasDerivAt_primeLogThetaStripSymbolTerm
    (n : ℕ) (p : Nat.Primes) (c : ℂ) (w : ℂ) :
    HasDerivAt (fun z : ℂ => c * (Real.log (p : ℝ) : ℂ) ^ n *
      Complex.exp (-I * z * (Real.log (p : ℝ) : ℂ)))
      (c * (Real.log (p : ℝ) : ℂ) ^ n *
        (Complex.exp (-I * w * (Real.log (p : ℝ) : ℂ)) *
          (-I * (Real.log (p : ℝ) : ℂ)))) w := by
  exact (hasDerivAt_primeLogThetaStripPhase p w).const_mul
    (c * (Real.log (p : ℝ) : ℂ) ^ n)

private theorem hasDerivAt_primeLogThetaStripSymbol
    (n : ℕ) (l : Nat.Primes →₀ ℂ) (w : ℂ) :
    HasDerivAt (primeLogThetaStripSymbol n l)
      (∑ p ∈ l.support, l p * primeLogThetaStripCoefficient p *
        (Real.log (p : ℝ) : ℂ) ^ n *
          (Complex.exp (-I * w * (Real.log (p : ℝ) : ℂ)) *
            (-I * (Real.log (p : ℝ) : ℂ)))) w := by
  change HasDerivAt (fun z : ℂ => ∑ p ∈ l.support,
    l p * primeLogThetaStripCoefficient p * (Real.log (p : ℝ) : ℂ) ^ n *
      Complex.exp (-I * z * (Real.log (p : ℝ) : ℂ))) _ w
  rw [show (fun z : ℂ => ∑ p ∈ l.support,
      l p * primeLogThetaStripCoefficient p * (Real.log (p : ℝ) : ℂ) ^ n *
        Complex.exp (-I * z * (Real.log (p : ℝ) : ℂ))) =
      ∑ p ∈ l.support, fun z : ℂ =>
        l p * primeLogThetaStripCoefficient p * (Real.log (p : ℝ) : ℂ) ^ n *
          Complex.exp (-I * z * (Real.log (p : ℝ) : ℂ)) by
    funext z
    simp]
  apply HasDerivAt.sum
  intro p hp
  exact hasDerivAt_primeLogThetaStripSymbolTerm n p
    (l p * primeLogThetaStripCoefficient p) w

/-- The literal complex theta source clock raises the prime-log degree by one. -/
theorem primeLogThetaStripClock_symbol
    (n : ℕ) (l : Nat.Primes →₀ ℂ) (w : ℂ) :
    primeLogThetaStripClock (primeLogThetaStripSymbol n l) w =
      primeLogThetaStripSymbol (n + 1) l w := by
  have hderiv := (hasDerivAt_primeLogThetaStripSymbol n l w).deriv
  unfold primeLogThetaStripClock
  rw [hderiv, primeLogThetaStripSymbol, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [show (Real.log (p : ℝ) : ℂ) ^ (n + 1) =
      (Real.log (p : ℝ) : ℂ) ^ n * (Real.log (p : ℝ) : ℂ) by rw [pow_succ]]
  calc
    I * (l p * primeLogThetaStripCoefficient p * (Real.log (p : ℝ) : ℂ) ^ n *
          (Complex.exp (-I * w * (Real.log (p : ℝ) : ℂ)) *
            (-I * (Real.log (p : ℝ) : ℂ)))) =
        (I * (-I : ℂ)) *
          (l p * primeLogThetaStripCoefficient p * (Real.log (p : ℝ) : ℂ) ^ n *
            Complex.exp (-I * w * (Real.log (p : ℝ) : ℂ)) *
              (Real.log (p : ℝ) : ℂ)) := by ring
    _ = l p * primeLogThetaStripCoefficient p *
          ((Real.log (p : ℝ) : ℂ) ^ n * (Real.log (p : ℝ) : ℂ)) *
            Complex.exp (-I * w * (Real.log (p : ℝ) : ℂ)) := by
      rw [show I * (-I : ℂ) = 1 by norm_num]
      ring

/-- Relative Xi Wronskian step, preserving all Xi factors instead of dividing by one. -/
def primeLogThetaStripWronskianStep (m : ℕ) (y : ℂ → ℂ) (w : ℂ) : ℂ :=
  XiC w * primeLogThetaStripClock y w -
    (m : ℂ) * primeLogThetaStripClock XiC w * y w

private theorem hasDerivAt_XiC_pow_primeLogThetaStrip (m : ℕ) (w : ℂ) :
    HasDerivAt (XiC ^ m)
      ((m : ℂ) * XiC w ^ (m - 1) * deriv XiC w) w := by
  simpa only [Pi.pow_apply] using (XiC_differentiable w).hasDerivAt.pow m

/-- One denominator-free Wronskian step raises both Xi filtration and literal source degree. -/
theorem primeLogThetaStripWronskianStep_symbol
    (m n : ℕ) (l : Nat.Primes →₀ ℂ) (w : ℂ) :
    primeLogThetaStripWronskianStep m
      ((XiC ^ m) * primeLogThetaStripSymbol n l) w =
      XiC w ^ (m + 1) * primeLogThetaStripSymbol (n + 1) l w := by
  have hprod := ((hasDerivAt_XiC_pow_primeLogThetaStrip m w).mul
    (hasDerivAt_primeLogThetaStripSymbol n l w).differentiableAt.hasDerivAt).deriv
  have hsource : I * deriv (primeLogThetaStripSymbol n l) w =
      primeLogThetaStripSymbol (n + 1) l w := by
    simpa [primeLogThetaStripClock] using primeLogThetaStripClock_symbol n l w
  unfold primeLogThetaStripWronskianStep primeLogThetaStripClock
  rw [hprod]
  simp only [Pi.mul_apply, Pi.pow_apply]
  calc
    XiC w *
          (I *
            ((m : ℂ) * XiC w ^ (m - 1) * deriv XiC w *
                primeLogThetaStripSymbol n l w +
              XiC w ^ m * deriv (primeLogThetaStripSymbol n l) w)) -
        (m : ℂ) * (I * deriv XiC w) *
          (XiC w ^ m * primeLogThetaStripSymbol n l w) =
        XiC w ^ (m + 1) *
          (I * deriv (primeLogThetaStripSymbol n l) w) := by
      cases m with
      | zero => norm_num
      | succ m =>
          simp only [Nat.cast_add, Nat.cast_one, Nat.succ_sub_one, pow_succ]
          ring
    _ = XiC w ^ (m + 1) * primeLogThetaStripSymbol (n + 1) l w := by rw [hsource]

/-- Iterated relative Wronskian transport through the Xi filtration. -/
def primeLogThetaStripWronskianIterate : ℕ → ℕ → (ℂ → ℂ) → (ℂ → ℂ)
  | _m, 0, y => y
  | m, n + 1, y => fun w =>
      primeLogThetaStripWronskianStep (m + n)
        (primeLogThetaStripWronskianIterate m n y) w

/-- The full relative ladder transports every finite source symbol exactly. -/
theorem primeLogThetaStripWronskianIterate_symbol
    (m n : ℕ) (l : Nat.Primes →₀ ℂ) (w : ℂ) :
    primeLogThetaStripWronskianIterate m n
      ((XiC ^ m) * primeLogThetaStripSymbol 0 l) w =
      XiC w ^ (m + n) * primeLogThetaStripSymbol n l w := by
  induction n generalizing w with
  | zero => simp [primeLogThetaStripWronskianIterate]
  | succ n ih =>
      have hlocal : primeLogThetaStripWronskianIterate m n
          ((XiC ^ m) * primeLogThetaStripSymbol 0 l) =ᶠ[𝓝 w]
          ((XiC ^ (m + n)) * primeLogThetaStripSymbol n l) :=
        Filter.Eventually.of_forall (fun z => ih z)
      change primeLogThetaStripWronskianStep (m + n)
        (primeLogThetaStripWronskianIterate m n
          ((XiC ^ m) * primeLogThetaStripSymbol 0 l)) w = _
      unfold primeLogThetaStripWronskianStep primeLogThetaStripClock
      rw [hlocal.deriv_eq, hlocal.self_of_nhds]
      change primeLogThetaStripWronskianStep (m + n)
        ((XiC ^ (m + n)) * primeLogThetaStripSymbol n l) w = _
      simpa [Nat.add_assoc] using
        primeLogThetaStripWronskianStep_symbol (m + n) n l w

/-- The raw finite theta transform is the first Xi level of the literal strip symbol. -/
theorem primeLogThetaFourierLaplace_eq_XiC_mul_stripSymbol
    (l : Nat.Primes →₀ ℂ) {w : ℂ} (hw : |w.im| < 1) :
    primeLogThetaFourierLaplace l w = XiC w * primeLogThetaStripSymbol 0 l w := by
  rw [primeLogThetaFourierLaplace_eq l hw]
  unfold primeLogThetaStripSymbol primeLogThetaStripCoefficient
  simp only [pow_zero, mul_one]
  apply congrArg (fun z : ℂ => XiC w * z)
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- The literal theta transform has exact relative Wronskian jets throughout the full strip. -/
theorem primeLogThetaStripWronskianIterate_thetaFourierLaplace
    (n : ℕ) (l : Nat.Primes →₀ ℂ) {w : ℂ} (hw : |w.im| < 1) :
    primeLogThetaStripWronskianIterate 1 n (primeLogThetaFourierLaplace l) w =
      XiC w ^ (1 + n) * primeLogThetaStripSymbol n l w := by
  induction n generalizing w with
  | zero =>
      rw [primeLogThetaStripWronskianIterate]
      have h := primeLogThetaFourierLaplace_eq_XiC_mul_stripSymbol l hw
      simpa only [Pi.one_apply, Nat.add_zero, pow_one] using h
  | succ n ih =>
      have hlocal : primeLogThetaStripWronskianIterate 1 n
          (primeLogThetaFourierLaplace l) =ᶠ[𝓝 w]
          ((XiC ^ (1 + n)) * primeLogThetaStripSymbol n l) := by
        filter_upwards [isOpen_thetaCuspFourierLaplaceStrip.mem_nhds
          (show w ∈ thetaCuspFourierLaplaceStrip by
            simpa [thetaCuspFourierLaplaceStrip] using (abs_lt.mp hw))] with z hz
        exact ih (abs_lt.mpr (by simpa [thetaCuspFourierLaplaceStrip] using hz))
      change primeLogThetaStripWronskianStep (1 + n)
        (primeLogThetaStripWronskianIterate 1 n (primeLogThetaFourierLaplace l)) w = _
      unfold primeLogThetaStripWronskianStep primeLogThetaStripClock
      rw [hlocal.deriv_eq, hlocal.self_of_nhds]
      change primeLogThetaStripWronskianStep (1 + n)
        ((XiC ^ (1 + n)) * primeLogThetaStripSymbol n l) w = _
      simpa [Nat.add_assoc] using
        primeLogThetaStripWronskianStep_symbol (1 + n) n l w

/-- The third literal theta jet is the fourth Xi-level representative of the cubic source. -/
theorem primeLogThetaStripWronskian_cubic_thetaFourierLaplace
    (l : Nat.Primes →₀ ℂ) {w : ℂ} (hw : |w.im| < 1) :
    primeLogThetaStripWronskianIterate 1 3 (primeLogThetaFourierLaplace l) w =
      XiC w ^ 4 * primeLogThetaStripSymbol 3 l w := by
  simpa using primeLogThetaStripWronskianIterate_thetaFourierLaplace 3 l hw

/-- Scalar cubic theta evaluation vanishes at every strip zero of XiC. -/
theorem primeLogThetaStripWronskian_cubic_thetaFourierLaplace_eq_zero
    (l : Nat.Primes →₀ ℂ) {w : ℂ} (hw : |w.im| < 1) (hzero : XiC w = 0) :
    primeLogThetaStripWronskianIterate 1 3 (primeLogThetaFourierLaplace l) w = 0 := by
  rw [primeLogThetaStripWronskian_cubic_thetaFourierLaplace l hw, hzero]
  norm_num

/-- A one-prime cubic source symbol never vanishes anywhere in the complex theta strip. -/
theorem primeLogThetaStripSymbol_cube_single_ne_zero
    (p : Nat.Primes) (w : ℂ) :
    primeLogThetaStripSymbol 3 (Finsupp.single p (1 : ℂ)) w ≠ 0 := by
  have hp_nat : 1 < (p : ℕ) := p.2.one_lt
  have hp_real : 1 < (p : ℝ) := by exact_mod_cast hp_nat
  have hlog_pos : 0 < Real.log (p : ℝ) := Real.log_pos hp_real
  have hlog_ne : (Real.log (p : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hlog_pos
  have hcoeff_real : 2 * Real.log (p : ℝ) ^ 2 / Real.sqrt (p : ℝ) ≠ 0 := by
    apply div_ne_zero
    · positivity
    · exact (Real.sqrt_ne_zero').mpr (by positivity)
  have hcoeff_ne : primeLogThetaStripCoefficient p ≠ 0 := by
    unfold primeLogThetaStripCoefficient
    exact_mod_cast hcoeff_real
  rw [primeLogThetaStripSymbol, Finsupp.support_single p one_ne_zero,
    Finset.sum_singleton, Finsupp.single_eq_same]
  simp only [one_mul]
  exact mul_ne_zero (mul_ne_zero hcoeff_ne (pow_ne_zero 3 hlog_ne))
    (Complex.exp_ne_zero _)

/-- At any strip zero, scalar cubic theta evaluation kills a provably nonzero prime source
direction.  Thus it cannot be the faithful final target of the literal theta graph. -/
theorem primeLogThetaStrip_XiZero_has_nontrivial_prime_cubic_scalar_loss
    (p : Nat.Primes) {w : ℂ} (hw : |w.im| < 1) (hzero : XiC w = 0) :
    primeLogThetaStripSymbol 3 (Finsupp.single p (1 : ℂ)) w ≠ 0 ∧
      primeLogThetaStripWronskianIterate 1 3
        (primeLogThetaFourierLaplace (Finsupp.single p (1 : ℂ))) w = 0 := by
  exact ⟨primeLogThetaStripSymbol_cube_single_ne_zero p w,
    primeLogThetaStripWronskian_cubic_thetaFourierLaplace_eq_zero
      (Finsupp.single p (1 : ℂ)) hw hzero⟩

end

end RHTower
