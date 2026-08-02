import GaloisForLFunctions.RHTower.SuzukiSecondDefectParityCommutator
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Suzuki's finite-prime position-commutator torque

Suzuki's restricted Weil operator has prime translation atoms

`-(Λ(n)/sqrt(n)) (tau_(log n) + tau_(-log n))`.

Commutation with position multiplies an atom at lag `h` by `h` and antisymmetrizes its two
translations.  Against an even response `e` and an odd response `o`, reflection then collapses
the two overlap integrals to one:

`prime torque = -2 (Λ(n)/sqrt(n)) log(n) C_(e,o)(log n)`,

where

`C_(e,o)(h) = ∫_(h-a)^a e(x)o(x-h) dx`.

Thus the second Suzuki defect sees the logarithmically differentiated Mangoldt layer, not the
first-jet coefficient alone.  For the free large-negative-shift profile
`e=cosh`, `o=sinh`, the correlation is exactly

`C(h)=-(2a-h)sinh(h)/2`.

Every visible prime-power atom therefore contributes strictly positive commutator anomaly.  This
is the first correction opposing the local negative curvature of the free deficiency profile.

No RH assumption, distributional formalization, or numerical computation occurs.  The statements
below are the exact finite-translation layer of Suzuki's distributional kernel formula.
-/

open scoped BigOperators
open Finset MeasureTheory Set

namespace RHTower

noncomputable section

/-- Oriented overlap correlation between an even and an odd compact response at positive lag
`h`.  For `0 ≤ h ≤ 2a`, this is the literal overlap of the zero-extended functions. -/
def suzukiLagCrossCorrelation
    (e o : ℝ → ℝ) (a h : ℝ) : ℝ :=
  ∫ x in h - a..a, e x * o (x - h)

/-- Matrix element of the position commutator of one symmetric translation atom with coefficient
`coefficient` and lag `h`. -/
def suzukiPrimeCommutatorAtom
    (coefficient h a : ℝ) (e o : ℝ → ℝ) : ℝ :=
  -coefficient * h *
    ((∫ x in h - a..a, e x * o (x - h)) -
      ∫ x in -a..a - h, e x * o (x + h))

/-- Reflection turns the two directed translation overlaps into one parity torque. -/
theorem suzukiPrimeCommutatorAtom_eq_lagCrossCorrelation
    {coefficient h a : ℝ} {e o : ℝ → ℝ}
    (he : Function.Even e) (ho : Function.Odd o) :
    suzukiPrimeCommutatorAtom coefficient h a e o =
      -2 * coefficient * h * suzukiLagCrossCorrelation e o a h := by
  have hreflect :
      (∫ x in -a..a - h, e x * o (x + h)) =
        -(∫ x in h - a..a, e x * o (x - h)) := by
    let f : ℝ → ℝ := fun x => e x * o (x + h)
    calc
      (∫ x in -a..a - h, e x * o (x + h)) =
          ∫ x in h - a..a, f (-x) := by
            have hcomp := intervalIntegral.integral_comp_neg
              (f := f) (a := h - a) (b := a)
            dsimp only [f] at hcomp ⊢
            convert hcomp.symm using 1 <;> ring
      _ = ∫ x in h - a..a, -(e x * o (x - h)) := by
        apply intervalIntegral.integral_congr
        intro x _hx
        dsimp only [f]
        rw [he x, show -x + h = -(x - h) by ring, ho (x - h)]
        ring
      _ = -(∫ x in h - a..a, e x * o (x - h)) := by
        rw [intervalIntegral.integral_neg]
  rw [suzukiPrimeCommutatorAtom, suzukiLagCrossCorrelation, hreflect]
  ring

/-- Actual finite Mangoldt layer of Suzuki's position commutator. -/
def suzukiFiniteWeilPrimeTorque
    (S : Finset ℕ) (a : ℝ) (e o : ℝ → ℝ) : ℝ :=
  ∑ n ∈ S,
    suzukiPrimeCommutatorAtom
      (ArithmeticFunction.vonMangoldt n / Real.sqrt n)
      (Real.log n) a e o

/-- Exact logarithmically differentiated Mangoldt torque formula. -/
theorem suzukiFiniteWeilPrimeTorque_eq
    (S : Finset ℕ) (a : ℝ) {e o : ℝ → ℝ}
    (he : Function.Even e) (ho : Function.Odd o) :
    suzukiFiniteWeilPrimeTorque S a e o =
      ∑ n ∈ S,
        -2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          Real.log n *
          suzukiLagCrossCorrelation e o a (Real.log n) := by
  apply Finset.sum_congr rfl
  intro n hn
  exact suzukiPrimeCommutatorAtom_eq_lagCrossCorrelation he ho

/-! ## The free resolvent profile -/

/-- Exact overlap correlation of the even/odd free deficiency pair. -/
theorem suzukiLagCrossCorrelation_cosh_sinh (a h : ℝ) :
    suzukiLagCrossCorrelation Real.cosh Real.sinh a h =
      -(2 * a - h) * Real.sinh h / 2 := by
  let H : ℝ → ℝ := fun x =>
    Real.cosh (2 * x - h) / 4 - x * Real.sinh h / 2
  have hderiv : ∀ x : ℝ,
      HasDerivAt H (Real.cosh x * Real.sinh (x - h)) x := by
    intro x
    have hlin : HasDerivAt (fun y : ℝ => 2 * y - h) 2 x := by
      simpa using ((hasDerivAt_id x).const_mul 2).sub_const h
    have hfirst :=
      ((Real.hasDerivAt_cosh (2 * x - h)).comp x hlin).div_const 4
    have hsecond := ((hasDerivAt_id x).mul_const (Real.sinh h)).div_const 2
    have hraw := hfirst.sub hsecond
    have hproduct :
        Real.sinh (2 * x - h) / 2 - Real.sinh h / 2 =
          Real.cosh x * Real.sinh (x - h) := by
      have hadd := Real.sinh_add x (x - h)
      have hsub := Real.sinh_sub x (x - h)
      rw [show x + (x - h) = 2 * x - h by ring] at hadd
      rw [show x - (x - h) = h by ring] at hsub
      linarith
    have hraw' : HasDerivAt H
        (Real.sinh (2 * x - h) * 2 / 4 -
          1 * Real.sinh h / 2) x := by
      have hfun :
          H =
            (fun y => Real.cosh (2 * y - h) / 4) -
              fun y => y * Real.sinh h / 2 := by
        funext y
        rfl
      rw [hfun]
      simpa only [Function.comp_apply, Function.id_def] using hraw
    convert hraw' using 1
    rw [← hproduct]
    ring
  have hint : IntervalIntegrable
      (fun x => Real.cosh x * Real.sinh (x - h)) volume (h - a) a :=
    (Real.continuous_cosh.mul
      (Real.continuous_sinh.comp (continuous_id.sub continuous_const))).intervalIntegrable _ _
  rw [suzukiLagCrossCorrelation,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _hx => hderiv x) hint]
  dsimp only [H]
  rw [show 2 * (h - a) - h = -(2 * a - h) by ring, Real.cosh_neg]
  ring

/-- Closed form of one free-profile prime commutator atom. -/
theorem suzukiPrimeCommutatorAtom_cosh_sinh
    (coefficient h a : ℝ) :
    suzukiPrimeCommutatorAtom coefficient h a Real.cosh Real.sinh =
      coefficient * h * (2 * a - h) * Real.sinh h := by
  rw [suzukiPrimeCommutatorAtom_eq_lagCrossCorrelation
      (fun x => Real.cosh_neg x) (fun x => Real.sinh_neg x),
    suzukiLagCrossCorrelation_cosh_sinh]
  ring

/-- Every positive visible translation atom produces strictly positive torque in the free
large-negative-shift deficiency profile. -/
theorem suzukiPrimeCommutatorAtom_cosh_sinh_pos
    {coefficient h a : ℝ}
    (hcoefficient : 0 < coefficient) (hh : 0 < h) (hvisible : h < 2 * a) :
    0 < suzukiPrimeCommutatorAtom coefficient h a Real.cosh Real.sinh := by
  rw [suzukiPrimeCommutatorAtom_cosh_sinh]
  exact mul_pos (mul_pos (mul_pos hcoefficient hh) (sub_pos.mpr hvisible))
    (Real.sinh_pos_iff.mpr hh)

/-- Every visible prime power gives a strictly positive free-profile arithmetic torque atom. -/
theorem suzukiWeilPrimeCommutatorAtom_cosh_sinh_pos
    {n : ℕ} {a : ℝ} (hn : 1 < n) (hnPower : IsPrimePow n)
    (hvisible : Real.log n < 2 * a) :
    0 < suzukiPrimeCommutatorAtom
      (ArithmeticFunction.vonMangoldt n / Real.sqrt n)
      (Real.log n) a Real.cosh Real.sinh := by
  apply suzukiPrimeCommutatorAtom_cosh_sinh_pos
  · exact div_pos (ArithmeticFunction.vonMangoldt_pos_iff.mpr hnPower)
      (Real.sqrt_pos.2 (by positivity))
  · exact Real.log_pos (by exact_mod_cast hn)
  · exact hvisible

/-- The full finite Mangoldt torque has an explicit positive free-profile form. -/
theorem suzukiFiniteWeilPrimeTorque_cosh_sinh
    (S : Finset ℕ) (a : ℝ) :
    suzukiFiniteWeilPrimeTorque S a Real.cosh Real.sinh =
      ∑ n ∈ S,
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          Real.log n * (2 * a - Real.log n) * Real.sinh (Real.log n) := by
  apply Finset.sum_congr rfl
  intro n hn
  exact suzukiPrimeCommutatorAtom_cosh_sinh _ _ _

/-- Every finite set of visible integers contributes nonnegative free-profile Weil torque. -/
theorem suzukiFiniteWeilPrimeTorque_cosh_sinh_nonneg
    {S : Finset ℕ} {a : ℝ}
    (hn : ∀ n ∈ S, 1 ≤ n)
    (hvisible : ∀ n ∈ S, Real.log n ≤ 2 * a) :
    0 ≤ suzukiFiniteWeilPrimeTorque S a Real.cosh Real.sinh := by
  rw [suzukiFiniteWeilPrimeTorque_cosh_sinh]
  apply Finset.sum_nonneg
  intro n hnS
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hn n hnS))
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn n hnS)
  have hsqrt : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hcoefficient :
      0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg hsqrt
  have hsinh : 0 ≤ Real.sinh (Real.log n) :=
    Real.sinh_nonneg_iff.mpr hlog
  exact mul_nonneg
    (mul_nonneg (mul_nonneg hcoefficient hlog)
      (sub_nonneg.mpr (hvisible n hnS))) hsinh

end

end RHTower
