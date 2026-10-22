import GaloisForLFunctions.RHTower.LogarithmicDilationPrimitiveQuadrature
import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitDilationSourceBounds

/-!
# The exact floor work in the centered divisor source

The dilation of the actual centered source is an exponentially weighted
force integral minus a fractional-part work. The complete floor work has
a polynomial bound; the signed short Möbius quadratic form retains it.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RHTower

def ccmPrimeDeficitCenteredDilationForce (t : ℝ) : ℝ :=
  ccmPrimeDeficitDilationForce t - (Real.eulerMascheroniConstant + 1) * Real.exp t +
    Real.log (2 * Real.pi) / 2

def ccmPrimeDeficitDivisorMainCoefficient (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, Real.exp (-t) * ccmPrimeDeficitCenteredDilationForce t

def ccmPrimeDeficitDivisorFloorWork (T : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..T, ccmPrimeDeficitCenteredDilationForce (T - s) *
    Int.fract (Real.exp s)

theorem intervalIntegrable_ccmPrimeDeficitCenteredDilationForce {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable ccmPrimeDeficitCenteredDilationForce volume 0 T :=
  ((intervalIntegrable_ccmPrimeDeficitDilationForce hT).sub
    ((Real.continuous_exp.const_mul _).intervalIntegrable 0 T)).add intervalIntegrable_const

theorem ccmPrimeDeficitDilationRemainder_dilation_quadrature {T : ℝ} (hT : 0 ≤ T) :
    logarithmicDilationSum ccmPrimeDeficitDilationRemainder T =
      Real.exp T * ccmPrimeDeficitDivisorMainCoefficient T -
        ccmPrimeDeficitDivisorFloorWork T := by
  have heq : logarithmicDilationSum ccmPrimeDeficitDilationRemainder T =
      logarithmicDilationSum
        (fun u => ∫ t in (0 : ℝ)..u, ccmPrimeDeficitCenteredDilationForce t) T := by
    unfold logarithmicDilationSum logarithmicWeightedDilation
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hlog : Real.log n ≤ T := (Real.log_le_iff_le_exp hnpos).mpr
      ((Nat.le_floor_iff (Real.exp_pos T).le).mp (Finset.mem_Icc.mp hn).2)
    rw [ccmPrimeDeficitDilationRemainder_eq_integral (sub_nonneg.mpr hlog)]
    rfl
  rw [heq]
  exact logarithmicDilationSum_primitive_quadrature _
    (intervalIntegrable_ccmPrimeDeficitCenteredDilationForce hT) hT

theorem abs_ccmPrimeDeficitDivisorFloorWork_le {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeDeficitDivisorFloorWork T| ≤ T ^ 2 / 4 + 2 * T := by
  have hi := intervalIntegrable_reverse_mul_fract_exp _
    (intervalIntegrable_ccmPrimeDeficitCenteredDilationForce hT) hT
  have hb : IntervalIntegrable (fun s : ℝ => (T - s) / 2 + 2) volume 0 T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hp (s : ℝ) (hs : s ∈ Icc 0 T) :
      |ccmPrimeDeficitCenteredDilationForce (T - s) * Int.fract (Real.exp s)| ≤
        (T - s) / 2 + 2 := by
    rw [abs_mul, abs_of_nonneg (Int.fract_nonneg (Real.exp s))]
    calc
      _ ≤ |ccmPrimeDeficitCenteredDilationForce (T - s)| * 1 :=
        mul_le_mul_of_nonneg_left (Int.fract_lt_one _).le (abs_nonneg _)
      _ ≤ _ := by
        rw [mul_one]
        exact abs_ccmPrimeDeficitDilationForce_centered_le (sub_nonneg.mpr hs.2)
  have hd (s : ℝ) : HasDerivAt
      (fun s : ℝ => (T / 2 + 2) * s - s ^ 2 / 4) ((T - s) / 2 + 2) s := by
    convert! ((hasDerivAt_id s).const_mul (T / 2 + 2)).sub
      (((hasDerivAt_id s).pow 2).div_const 4) using 1
    simp only [id_eq]
    ring
  calc
    _ ≤ ∫ s in (0 : ℝ)..T,
        |ccmPrimeDeficitCenteredDilationForce (T - s) * Int.fract (Real.exp s)| :=
      intervalIntegral.abs_integral_le_integral_abs hT
    _ ≤ ∫ s in (0 : ℝ)..T, ((T - s) / 2 + 2) :=
      intervalIntegral.integral_mono_on hT hi.abs hb hp
    _ = _ := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hb]
      ring

theorem abs_ccmPrimeDeficitDilationRemainder_dilation_centered_le {T : ℝ} (hT : 0 ≤ T) :
    |logarithmicDilationSum ccmPrimeDeficitDilationRemainder T -
      Real.exp T * ccmPrimeDeficitDivisorMainCoefficient T| ≤ T ^ 2 / 4 + 2 * T := by
  rw [ccmPrimeDeficitDilationRemainder_dilation_quadrature hT, sub_sub_cancel_left, abs_neg]
  exact abs_ccmPrimeDeficitDivisorFloorWork_le hT

end RHTower
