import GaloisForLFunctions.RHTower.Suzuki.SuzukiPrimeClockAtomVelocity

/-!
# The prime clock-atom velocity is the truncated critical sine transform

Each prime step contributes a half-shifted two-sided phase to the free-clock pole velocity.  At the
free clock node `x_(a,k) = (k + 1/2) pi / a` the half phase and the `k`-th power of the full phase
combine into `exp (I x_(a,k) log m)`, so the two-sided packet collapses to `sin (x_(a,k) log m)`.
Hence `a` times the velocity is exactly the truncated critical von Mangoldt sine transform sampled
on the half-integer clock.
-/

open Complex Finset

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The free clock node `x_(a,k) = (k + 1/2) pi / a`. -/
def suzukiFreeClockNode (a : ℝ) (k : ℕ) : ℝ := ((k : ℝ) + 1 / 2) * Real.pi / a

/-- The truncated critical von Mangoldt sine transform. -/
def suzukiPhysicalPrimeSine (s : Finset ℕ) (t : ℝ) : ℝ :=
  ∑ m ∈ s, ArithmeticFunction.vonMangoldt m / Real.sqrt m * Real.sin (t * Real.log m)

private theorem halfShiftPhase_eq (a : ℝ) (m k : ℕ) :
    suzukiPrimeClockHalfPhase a m * suzukiPrimeTangentPhase a m ^ k =
      Complex.exp ((((suzukiFreeClockNode a k * Real.log m : ℝ)) : ℂ) * I) := by
  rw [suzukiPrimeClockHalfPhase, suzukiPrimeTangentPhase, ← Complex.exp_nat_mul,
    ← Complex.exp_add]
  congr 1
  rw [suzukiFreeClockNode]
  push_cast
  ring

private theorem halfShiftPhase_inv_eq (a : ℝ) (m k : ℕ) :
    (suzukiPrimeClockHalfPhase a m)⁻¹ * (suzukiPrimeTangentPhase a m)⁻¹ ^ k =
      Complex.exp (-((((suzukiFreeClockNode a k * Real.log m : ℝ)) : ℂ) * I)) := by
  rw [inv_pow, ← mul_inv, halfShiftPhase_eq, ← Complex.exp_neg]

private theorem exp_sub_exp_div (θ : ℝ) :
    (Complex.exp ((θ : ℂ) * I) - Complex.exp (-((θ : ℂ) * I))) / (2 * I) =
      ((Real.sin θ : ℝ) : ℂ) := by
  rw [Complex.exp_mul_I, show -((θ : ℂ) * I) = (-(θ : ℂ)) * I by ring, Complex.exp_mul_I,
    Complex.cos_neg, Complex.sin_neg, Complex.ofReal_sin]
  have hI : (2 : ℂ) * I ≠ 0 := by
    simp [Complex.I_ne_zero]
  field_simp
  ring

/-- **Physical form of the prime clock-atom velocity.**  At the free clock node the two-sided phase
packet collapses to a sine, so `a` times the arithmetic part of the first Donoghue-divisor velocity
is the truncated critical von Mangoldt sine transform sampled at `x_(a,k)`. -/
theorem suzukiPrimeClockAtomVelocity_eq_physicalPrimeSine (a : ℝ) (s : Finset ℕ) (k : ℕ) :
    ((a : ℝ) : ℂ) * suzukiPrimeClockAtomVelocity a s k =
      ((suzukiPhysicalPrimeSine s (suzukiFreeClockNode a k) : ℝ) : ℂ) := by
  rw [suzukiPrimeClockAtomVelocity, suzukiFiniteHalfShiftSinePhaseCarrier_eq_sum,
    suzukiPhysicalPrimeSine, Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [halfShiftPhase_eq, halfShiftPhase_inv_eq, mul_div_assoc,
    exp_sub_exp_div (suzukiFreeClockNode a k * Real.log m),
    suzukiPrimeClockAtomAmplitude]
  by_cases ha : a = 0
  · simp [ha, suzukiFreeClockNode]
  · rcases em' (Real.sqrt (m : ℝ) = 0) with hm | hm
    · have ha' : ((a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
      have hm' : ((Real.sqrt (m : ℝ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm
      push_cast
      field_simp
    · simp [hm]

end

end GaloisForLFunctions.RHTower
