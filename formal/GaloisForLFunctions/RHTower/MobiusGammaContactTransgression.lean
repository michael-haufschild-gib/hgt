import GaloisForLFunctions.HTGeometry.GammaPeriodicConstraintCorona
import GaloisForLFunctions.HTGeometry.GammaFactorialAsymptoticConnection

/-!
# A formal Gamma-conormal cross-pair with the critical squarefree-Mobius germ

The completed critical Fisher score has analytic score-density

`f(z) = 2 (1-z) exp(-z)`.

This file pairs its complete derivative jet with the factorial-tail functional occurring in the
Gamma unit-shift source.  The basic functional evaluates the germ to the exact boundary jump

`(exp D - 1) f(0) = f(1) - f(0) = -2`,

whose squared modulus is the four-unit critical source budget.  More generally, every
differentiated Gamma conormal `D^k (exp D - 1)` evaluates to the corresponding derivative jump.
The calculation is an exact formal cross-pair.  It does not identify the critical variable with
Gamma's affine argument and therefore is not, by itself, a source-natural transgression.  The
source-natural comparison is Mellin duality and is formalized separately in
`MobiusMellinGammaNormalCone`.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Complexified analytic score-density of the completed critical squarefree-Mobius tangent. -/
def completedMobiusGammaContactGerm (z : ℂ) : ℂ :=
  2 * (1 - z) * Complex.exp (-z)

/-- Closed formula for every derivative of the completed contact germ. -/
def completedMobiusGammaContactDerivative (n : ℕ) (z : ℂ) : ℂ :=
  2 * (-1 : ℂ) ^ n * ((n + 1 : ℕ) - z) * Complex.exp (-z)

theorem hasDerivAt_completedMobiusGammaContactDerivative (n : ℕ) (z : ℂ) :
    HasDerivAt (completedMobiusGammaContactDerivative n)
      (completedMobiusGammaContactDerivative (n + 1) z) z := by
  have hlin : HasDerivAt (fun w : ℂ => ((n + 1 : ℕ) : ℂ) - w) (-1) z := by
    have hraw :=
      (hasDerivAt_const z (((n + 1 : ℕ) : ℂ))).sub (hasDerivAt_id z)
    apply (hraw.congr_deriv (by simp)).congr_of_eventuallyEq
    filter_upwards with w
    rfl
  have hneg : HasDerivAt (fun w : ℂ => -w) (-1) z := by
    simpa only [Pi.neg_apply, id_eq] using! (hasDerivAt_id z).neg
  have hexp : HasDerivAt (fun w : ℂ => Complex.exp (-w))
      (-Complex.exp (-z)) z := by
    have hraw := (Complex.hasDerivAt_exp (-z)).comp z hneg
    apply (hraw.congr_deriv (by ring)).congr_of_eventuallyEq
    filter_upwards with w
    rfl
  have hprod := hlin.mul hexp
  have h := hprod.const_mul (2 * (-1 : ℂ) ^ n)
  have hderiv :
      2 * (-1 : ℂ) ^ n *
          (-1 * Complex.exp (-z) +
            (((n + 1 : ℕ) : ℂ) - z) * -Complex.exp (-z)) =
        completedMobiusGammaContactDerivative (n + 1) z := by
    simp only [completedMobiusGammaContactDerivative, pow_succ]
    push_cast
    ring
  apply (h.congr_deriv hderiv).congr_of_eventuallyEq
  filter_upwards with w
  simp only [completedMobiusGammaContactDerivative, Pi.mul_apply]
  ring

/-- The displayed closed formula is the complete derivative tower of the contact germ. -/
theorem iteratedDeriv_completedMobiusGammaContactGerm (n : ℕ) :
    iteratedDeriv n completedMobiusGammaContactGerm =
      completedMobiusGammaContactDerivative n := by
  induction n with
  | zero =>
      funext z
      simp [completedMobiusGammaContactGerm, completedMobiusGammaContactDerivative]
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by rfl, iteratedDeriv_succ, ih]
      funext z
      exact (hasDerivAt_completedMobiusGammaContactDerivative n z).deriv

theorem iteratedDeriv_completedMobiusGammaContactGerm_zero (n : ℕ) :
    iteratedDeriv n completedMobiusGammaContactGerm 0 =
      2 * (-1 : ℂ) ^ n * (n + 1) := by
  rw [congrFun (iteratedDeriv_completedMobiusGammaContactGerm n) 0]
  simp [completedMobiusGammaContactDerivative]

/-- The positive derivative-tail jet seen by the basic Gamma conormal. -/
def mobiusGammaContactJet (n : ℕ) : ℂ :=
  2 * (-1 : ℂ) ^ (n + 1) * (n + 2)

theorem mobiusGammaContactJet_eq_derivative (n : ℕ) :
    mobiusGammaContactJet n =
      iteratedDeriv (n + 1) completedMobiusGammaContactGerm 0 := by
  rw [iteratedDeriv_completedMobiusGammaContactGerm_zero]
  simp only [mobiusGammaContactJet]
  push_cast
  ring

/-- Each finite Gamma-conormal summand is an exact discrete derivative of the exponential series. -/
theorem mobiusGammaContactConormalTerm_eq_telescope (n : ℕ) :
    HTGeometry.gammaPeriodicConormalCoefficient n * mobiusGammaContactJet n =
      2 * (((-1 : ℂ) ^ (n + 1) / ((n + 1).factorial : ℂ)) -
        ((-1 : ℂ) ^ n / (n.factorial : ℂ))) := by
  simp only [HTGeometry.gammaPeriodicConormalCoefficient, mobiusGammaContactJet, one_div]
  rw [Nat.factorial_succ]
  push_cast
  have hn : (n : ℂ) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  field_simp [hn]
  ring

/-- Charge exposed by the first `N` raw Gamma boundary symbols. -/
def mobiusGammaContactPartialCharge (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N,
    HTGeometry.gammaPeriodicConormalCoefficient n * mobiusGammaContactJet n

/-- Raw finite Gamma transgression oscillates around the terminal charge with exact factorial
error `2 (-1)^N/N!`. -/
theorem mobiusGammaContactPartialCharge_eq (N : ℕ) :
    mobiusGammaContactPartialCharge N =
      2 * (((-1 : ℂ) ^ N / (N.factorial : ℂ)) - 1) := by
  let e : ℕ → ℂ := fun n => (-1 : ℂ) ^ n / (n.factorial : ℂ)
  calc
    mobiusGammaContactPartialCharge N =
        ∑ n ∈ Finset.range N, 2 * (e (n + 1) - e n) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [mobiusGammaContactConormalTerm_eq_telescope]
    _ = 2 * ∑ n ∈ Finset.range N, (e (n + 1) - e n) := by
      rw [Finset.mul_sum]
    _ = 2 * (e N - e 0) := by
      rw [Finset.sum_range_sub]
    _ = 2 * (((-1 : ℂ) ^ N / (N.factorial : ℂ)) - 1) := by
      simp [e]

/-- The first raw boundary layer overshoots the terminal four-unit charge: its charge is `-4`. -/
@[simp] theorem mobiusGammaContactPartialCharge_one :
    mobiusGammaContactPartialCharge 1 = -4 := by
  rw [mobiusGammaContactPartialCharge_eq]
  norm_num

/-- The first raw boundary layer has energy sixteen, so no stagewise four-unit contraction can
use the naive jet truncation. -/
theorem norm_sq_mobiusGammaContactPartialCharge_one :
    ‖mobiusGammaContactPartialCharge 1‖ ^ 2 = 16 := by
  rw [mobiusGammaContactPartialCharge_one]
  norm_num

/-- Gamma's actual reciprocal-pole scale supplies the canonical finite-depth counterterm. -/
def renormalizedMobiusGammaContactCharge (N : ℕ) : ℂ :=
  mobiusGammaContactPartialCharge N +
    2 * GaloisForLFunctions.reciprocalGammaFactorialScale N

/-- **Exact factorial renormalization.**  At every finite Gamma depth, adding twice the actual
reciprocal-Gamma pole scale removes the complete truncation error and leaves the terminal contact
charge `-2`.  No asymptotic choice or fitted counterterm is used. -/
@[simp] theorem renormalizedMobiusGammaContactCharge_eq (N : ℕ) :
    renormalizedMobiusGammaContactCharge N = -2 := by
  rw [renormalizedMobiusGammaContactCharge, mobiusGammaContactPartialCharge_eq]
  simp only [GaloisForLFunctions.reciprocalGammaFactorialScale]
  ring

/-- Every factorially renormalized finite boundary charge already has the terminal four-unit
energy. -/
theorem norm_sq_renormalizedMobiusGammaContactCharge (N : ℕ) :
    ‖renormalizedMobiusGammaContactCharge N‖ ^ 2 = 4 := by
  rw [renormalizedMobiusGammaContactCharge_eq]
  norm_num

/-- The completed contact jet belongs to the basic factorial conormal domain and carries exact
oriented boundary charge `-2`. -/
theorem mobiusGammaContactJet_conormal_hasSum :
    HasSum (fun n : ℕ =>
      HTGeometry.gammaPeriodicConormalCoefficient n * mobiusGammaContactJet n) (-2) := by
  let e : ℕ → ℂ := fun n => (-1 : ℂ) ^ n / (n.factorial : ℂ)
  have hexp : HasSum e (NormedSpace.exp (-1 : ℂ)) := by
    simpa [e] using NormedSpace.expSeries_div_hasSum_exp (-1 : ℂ)
  have htail : HasSum (fun n => e (n + 1)) (NormedSpace.exp (-1 : ℂ) - 1) := by
    have h := (hasSum_nat_add_iff' (f := e) 1).mpr hexp
    simpa [e] using h
  have hdiff : HasSum (fun n => 2 * (e (n + 1) - e n)) (-2) := by
    have h := (htail.sub hexp).mul_left 2
    have hvalue :
        2 * (NormedSpace.exp (-1 : ℂ) - 1 - NormedSpace.exp (-1 : ℂ)) =
          (-2 : ℂ) := by
      have hcancel :
          NormedSpace.exp (-1 : ℂ) - 1 - NormedSpace.exp (-1 : ℂ) =
            (-1 : ℂ) := by
        abel
      rw [hcancel]
      norm_num
    rw [← hvalue]
    exact h
  apply hdiff.congr_fun
  intro n
  simp only [HTGeometry.gammaPeriodicConormalCoefficient, mobiusGammaContactJet, e, one_div]
  rw [Nat.factorial_succ]
  push_cast
  have hn : (n : ℂ) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  field_simp [hn]
  ring

/-- Every differentiated Gamma conormal evaluates the contact section to an explicit derivative
jump.  This is the full cyclic transgression, not only its scalar order-zero charge. -/
theorem shifted_completedMobiusGammaContact_conormal_hasSum (k : ℕ) :
    HasSum (fun n : ℕ => HTGeometry.gammaPeriodicConormalCoefficient n *
      iteratedDeriv (n + k + 1) completedMobiusGammaContactGerm 0)
      (2 * (-1 : ℂ) ^ k *
        ((k : ℂ) * NormedSpace.exp (-1 : ℂ) - (k + 1 : ℕ))) := by
  let e : ℕ → ℂ := fun n => (-1 : ℂ) ^ n / (n.factorial : ℂ)
  have hexp : HasSum e (NormedSpace.exp (-1 : ℂ)) := by
    simpa [e] using NormedSpace.expSeries_div_hasSum_exp (-1 : ℂ)
  have htail : HasSum (fun n => e (n + 1)) (NormedSpace.exp (-1 : ℂ) - 1) := by
    have h := (hasSum_nat_add_iff' (f := e) 1).mpr hexp
    simpa [e] using h
  have hcomb := ((htail.mul_left ((k + 1 : ℕ) : ℂ)).sub hexp).mul_left
    (2 * (-1 : ℂ) ^ k)
  have htarget : HasSum
      (fun n => 2 * (-1 : ℂ) ^ k * (((k + 1 : ℕ) : ℂ) * e (n + 1) - e n))
      (2 * (-1 : ℂ) ^ k *
        ((k : ℂ) * NormedSpace.exp (-1 : ℂ) - (k + 1 : ℕ))) := by
    have hvalue :
        2 * (-1 : ℂ) ^ k *
            ((((k + 1 : ℕ) : ℂ) *
                (NormedSpace.exp (-1 : ℂ) - 1)) -
              NormedSpace.exp (-1 : ℂ)) =
          2 * (-1 : ℂ) ^ k *
            ((k : ℂ) * NormedSpace.exp (-1 : ℂ) - (k + 1 : ℕ)) := by
      push_cast
      ring
    rw [← hvalue]
    exact hcomb
  apply htarget.congr_fun
  intro n
  rw [iteratedDeriv_completedMobiusGammaContactGerm_zero]
  simp only [HTGeometry.gammaPeriodicConormalCoefficient, e, one_div]
  rw [Nat.factorial_succ]
  push_cast
  have hn : (n : ℂ) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  field_simp [hn]
  ring

/-- The explicit target of the shifted conormal sum is literally
`D^k f(1) - D^k f(0)`. -/
theorem shifted_completedMobiusGammaContact_conormal_target_eq_jump (k : ℕ) :
    2 * (-1 : ℂ) ^ k *
        ((k : ℂ) * NormedSpace.exp (-1 : ℂ) - (k + 1 : ℕ)) =
      iteratedDeriv k completedMobiusGammaContactGerm 1 -
        iteratedDeriv k completedMobiusGammaContactGerm 0 := by
  rw [congrFun (iteratedDeriv_completedMobiusGammaContactGerm k) 1,
    congrFun (iteratedDeriv_completedMobiusGammaContactGerm k) 0]
  simp only [completedMobiusGammaContactDerivative]
  rw [Complex.exp_eq_exp_ℂ]
  simp only [neg_zero, NormedSpace.exp_zero, mul_one]
  push_cast
  ring

/-- The basic Gamma boundary jump of the contact section is `-2`. -/
@[simp] theorem completedMobiusGammaContactGerm_one_sub_zero :
    completedMobiusGammaContactGerm 1 - completedMobiusGammaContactGerm 0 = -2 := by
  simp [completedMobiusGammaContactGerm]

/-- Squared modulus of the oriented Gamma contact charge is exactly the four-unit Fisher budget. -/
theorem norm_sq_mobiusGammaContactCharge :
    ‖(-2 : ℂ)‖ ^ 2 = 4 := by
  norm_num

end

end GaloisForLFunctions.RHTower

namespace GaloisForLFunctions.RHTower

open Complex MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

theorem mobiusContactGammaFactorialScale_eq (n : ℕ) :
    (-2 - mobiusGammaContactPartialCharge n) / 2 =
      GaloisForLFunctions.reciprocalGammaFactorialScale n := by
  rw [mobiusGammaContactPartialCharge_eq]
  simp only [GaloisForLFunctions.reciprocalGammaFactorialScale]
  ring

end

end GaloisForLFunctions.RHTower
