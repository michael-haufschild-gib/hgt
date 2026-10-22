import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDampingAverageOfTheRelativeLossSuffices

/-!
# The escape is an out-and-back excursion

In the pronic space the damping parameter traces a curve: `ε ↦ A_ε`, with velocity the centred
damped Chebyshev tangent.  Minkowski's inequality says the curve moves at most the integrated speed,
and applying it on both sides of an interior damping gives the **out-and-back bound**

`∫_a^c ‖E_x‖_T dx ≥ 2 √(E_T(ε)) − √(E_T(a)) − √(E_T(c))`  for `a ≤ ε ≤ c`
(`integral_pronicNorm_tangent_ge`).

Both ends of the damping range are paid — the energy returns below one at zero damping and is
bounded at half damping — so an escape at an interior damping is an excursion that must be paid for
*twice*, on the way out and on the way back.  Quantitatively the integrated tangent norm is at least
twice the square root of the escaping energy, up to the two paid ends
(`integral_pronicNorm_tangent_ge_of_admitted_end`).

This is the exact converse of the averaged tangent-norm criterion: that criterion says a horizon-free
bound on `∫ ‖E_ε‖_T dε` gives RH, and this says a failure of RH forces that same integral to grow
like twice the square root of the energy it fails to control.  No estimate can be cheaper than the
excursion it has to forbid.
-/

open Set Filter MeasureTheory RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-- The curve moves at most the integrated speed: Minkowski for the damping interval. -/
theorem pronicNorm_centeredPrefix_sub_le {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (T : ℕ) :
    pronicNorm T (fun n => pmPowerDampedCenteredDivisorPrefix c n -
        pmPowerDampedCenteredDivisorPrefix a n) ≤
      ∫ x in a..c, pronicNorm T (dampedChebyshevError x) := by
  have hcont : ∀ n : ℕ, ContinuousOn (fun x => dampedChebyshevError x n) (Icc a c) :=
    fun n => (continuousOn_dampedChebyshevError n).mono fun x hx =>
      mem_Ioi.mpr (lt_of_lt_of_le ha hx.1)
  have heq : (fun n => pmPowerDampedCenteredDivisorPrefix c n -
      pmPowerDampedCenteredDivisorPrefix a n) =
      fun n => ∫ x in a..c, dampedChebyshevError x n :=
    funext fun n => pmPowerDampedCenteredDivisorPrefix_sub_eq_integral ha hac n
  rw [heq]
  exact pronicNorm_integral_le T hac (fun x n => dampedChebyshevError x n) hcont

/-- **The out-and-back bound.**  An interior excursion of the curve is paid twice. -/
theorem integral_pronicNorm_tangent_ge {a c ε : ℝ} (ha : 0 < a) (hae : a ≤ ε) (hec : ε ≤ c)
    (T : ℕ) :
    2 * Real.sqrt (dampedMobiusEnergy ε T) - Real.sqrt (dampedMobiusEnergy a T) -
        Real.sqrt (dampedMobiusEnergy c T) ≤
      ∫ x in a..c, pronicNorm T (dampedChebyshevError x) := by
  have hεpos : 0 < ε := lt_of_lt_of_le ha hae
  have hout := pronicNorm_centeredPrefix_sub_le ha hae T
  have hback := pronicNorm_centeredPrefix_sub_le hεpos hec T
  -- the two legs add up to the whole interval
  have hcontnorm : ContinuousOn (fun x => pronicNorm T (dampedChebyshevError x)) (Icc a c) :=
    (continuousOn_pronicNorm_dampedChebyshevError T).mono fun x hx =>
      mem_Ioi.mpr (lt_of_lt_of_le ha hx.1)
  have hint1 : IntervalIntegrable (fun x => pronicNorm T (dampedChebyshevError x)) volume a ε := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hae]
    exact hcontnorm.mono (Icc_subset_Icc le_rfl hec)
  have hint2 : IntervalIntegrable (fun x => pronicNorm T (dampedChebyshevError x)) volume ε c := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hec]
    exact hcontnorm.mono (Icc_subset_Icc hae le_rfl)
  have hadd : (∫ x in a..ε, pronicNorm T (dampedChebyshevError x)) +
      (∫ x in ε..c, pronicNorm T (dampedChebyshevError x)) =
      ∫ x in a..c, pronicNorm T (dampedChebyshevError x) :=
    intervalIntegral.integral_add_adjacent_intervals hint1 hint2
  -- the triangle inequality on each leg
  have htri : ∀ x y : ℝ, 0 < x → x ≤ y →
      Real.sqrt (dampedMobiusEnergy y T) ≤ Real.sqrt (dampedMobiusEnergy x T) +
        ∫ z in x..y, pronicNorm T (dampedChebyshevError z) := by
    intro x y hx hxy
    have hsub := pronicNorm_centeredPrefix_sub_le hx hxy T
    have hdecomp : pmPowerDampedCenteredDivisorPrefix y =
        fun n => pmPowerDampedCenteredDivisorPrefix x n +
          (pmPowerDampedCenteredDivisorPrefix y n - pmPowerDampedCenteredDivisorPrefix x n) :=
      funext fun n => by ring
    have htriangle := pronicNorm_add_le T (pmPowerDampedCenteredDivisorPrefix x)
      (fun n => pmPowerDampedCenteredDivisorPrefix y n -
        pmPowerDampedCenteredDivisorPrefix x n)
    rw [← hdecomp, pronicNorm_centeredPrefix, pronicNorm_centeredPrefix] at htriangle
    linarith
  have h1 : Real.sqrt (dampedMobiusEnergy ε T) ≤ Real.sqrt (dampedMobiusEnergy a T) +
      ∫ x in a..ε, pronicNorm T (dampedChebyshevError x) := htri a ε ha hae
  have h2 : Real.sqrt (dampedMobiusEnergy ε T) ≤ Real.sqrt (dampedMobiusEnergy c T) +
      ∫ x in ε..c, pronicNorm T (dampedChebyshevError x) := by
    have hsub := pronicNorm_centeredPrefix_sub_le hεpos hec T
    have hdecomp : pmPowerDampedCenteredDivisorPrefix ε =
        fun n => pmPowerDampedCenteredDivisorPrefix c n -
          (pmPowerDampedCenteredDivisorPrefix c n - pmPowerDampedCenteredDivisorPrefix ε n) :=
      funext fun n => by ring
    have htriangle := pronicNorm_add_le T (pmPowerDampedCenteredDivisorPrefix c)
      (fun n => -(pmPowerDampedCenteredDivisorPrefix c n -
        pmPowerDampedCenteredDivisorPrefix ε n))
    have hfun : (fun n => pmPowerDampedCenteredDivisorPrefix c n +
        -(pmPowerDampedCenteredDivisorPrefix c n -
          pmPowerDampedCenteredDivisorPrefix ε n)) =
        pmPowerDampedCenteredDivisorPrefix ε := funext fun n => by ring
    rw [hfun, pronicNorm_centeredPrefix, pronicNorm_centeredPrefix, pronicNorm_neg] at htriangle
    linarith
  linarith

/-- **The escape forces a large integrated tangent norm.**  With the right end admitted and the
left end near zero damping, where the energy returns below one, the integral is at least twice the
square root of the energy at the interior damping, less the two paid ends. -/
theorem integral_pronicNorm_tangent_ge_of_admitted_end {a ε : ℝ} (ha : 0 < a) (hae : a ≤ ε)
    (hε2 : ε ≤ 1 / 2) {B : ℝ} (hB : ∀ T : ℕ, dampedMobiusEnergy (1 / 2) T ≤ B) (T : ℕ) :
    2 * Real.sqrt (dampedMobiusEnergy ε T) - Real.sqrt (dampedMobiusEnergy a T) -
        Real.sqrt (max B 0) ≤
      ∫ x in a..(1 / 2 : ℝ), pronicNorm T (dampedChebyshevError x) := by
  have hmain := integral_pronicNorm_tangent_ge ha hae hε2 T
  have hmono : Real.sqrt (dampedMobiusEnergy (1 / 2) T) ≤ Real.sqrt (max B 0) :=
    Real.sqrt_le_sqrt ((hB T).trans (le_max_left B 0))
  linarith

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
