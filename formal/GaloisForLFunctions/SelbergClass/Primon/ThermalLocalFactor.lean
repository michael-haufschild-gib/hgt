import GaloisForLFunctions.SelbergClass.Primon.LogarithmicAverage

/-!
# Thermal specialization of the logarithmic phase average

At inverse temperature `exp β`, the prime Boltzmann ratio is
`exp (-exp β * log p)`. Its disk bounds and the full phase integral are proved
for every real `β`. Averaging the logarithmic charged-boson factor produces
the fermionic factor at inverse temperature `2 exp β + 1`, with degeneracy
`(p-1)/2`. The averaged bosonic logarithm is strictly negative; the reciprocal
fermionic logarithm is strictly positive.
-/

open MeasureTheory Set
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Prime Boltzmann ratio at positive inverse temperature `exp β`. -/
def thermalRatio (p : Nat.Primes) (β : ℝ) : ℝ :=
  Real.exp (-Real.exp β * Real.log (p : ℝ))

theorem thermalRatio_pos (p : Nat.Primes) (β : ℝ) : 0 < thermalRatio p β :=
  Real.exp_pos _

theorem thermalRatio_lt_one (p : Nat.Primes) (β : ℝ) : thermalRatio p β < 1 := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.one_lt
  unfold thermalRatio
  apply Real.exp_lt_one_iff.mpr
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (Real.exp_pos β)) (Real.log_pos hp)

/-- Explicit cavity parameter realizing the physical Boltzmann ratio. -/
def thermalDiskParameter (p : Nat.Primes) (β : ℝ) : ℝ :=
  thermalRatio p β / (1 - thermalRatio p β)

/-- The analytic disk coordinate agrees with the original thermal fugacity. -/
theorem cavityDiskCoordinate_thermal (p : Nat.Primes) (β : ℝ) :
    cavityDiskCoordinate (thermalDiskParameter p β) = thermalRatio p β := by
  have hr := thermalRatio_pos p β
  have h1 := thermalRatio_lt_one p β
  have hd : 0 < 1 - thermalRatio p β := sub_pos.mpr h1
  unfold cavityDiskCoordinate thermalDiskParameter
  rw [abs_of_pos (div_pos hr hd)]
  field_simp [hd.ne']
  ring

/-- The square of the bosonic fugacity divided by the prime is the shifted
fermionic fugacity, with inverse temperature `2 exp β + 1`. -/
theorem thermalRatio_square_div_prime (p : Nat.Primes) (β : ℝ) :
    thermalRatio p β ^ 2 / (p : ℝ) =
      Real.exp (-(2 * Real.exp β + 1) * Real.log (p : ℝ)) := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  have hi : (p : ℝ)⁻¹ = Real.exp (-Real.log (p : ℝ)) := by
    rw [Real.exp_neg, Real.exp_log hp]
  rw [thermalRatio, pow_two, div_eq_mul_inv, hi, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The thermal local factor's logarithm with its two opposite charges. -/
def thermalLocalLog (p : Nat.Primes) (β t : ℝ) : ℝ :=
  -Real.log (1 - 2 * thermalRatio p β * Real.cos (Real.pi * t) + thermalRatio p β ^ 2)

/-- The full thermal integral in the charged-primon logarithmic averaging law. -/
theorem integral_kesten_thermalLocalLog (p : Nat.Primes) (β : ℝ) :
    (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * thermalLocalLog p β t) =
      ((p : ℝ) - 1) / 2 *
        Real.log (1 - Real.exp (-(2 * Real.exp β + 1) * Real.log (p : ℝ))) := by
  have h := integral_kesten_log_local_factor p (thermalDiskParameter p β)
  simp only [phaseLogDenominator, cavityDiskCoordinate_thermal] at h
  rw [thermalRatio_square_div_prime] at h
  exact h

/-- Averaging produces a strictly negative bosonic logarithm at every positive temperature. -/
theorem integral_kesten_thermalLocalLog_neg (p : Nat.Primes) (β : ℝ) :
    (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * thermalLocalLog p β t) < 0 := by
  rw [integral_kesten_thermalLocalLog]
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hr0 : 0 < Real.exp (-(2 * Real.exp β + 1) * Real.log (p : ℝ)) := Real.exp_pos _
  have hr1 : Real.exp (-(2 * Real.exp β + 1) * Real.log (p : ℝ)) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    exact mul_neg_of_neg_of_pos (by have := Real.exp_pos β; linarith) (Real.log_pos hp)
  exact mul_neg_of_pos_of_neg (by linarith) (Real.log_neg (by linarith) (by linarith))

/-- The reciprocal fermionic local factor has strictly positive averaged logarithm. -/
theorem integral_kesten_fermionicLog_pos (p : Nat.Primes) (β : ℝ) :
    0 < ∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t * (-thermalLocalLog p β t) := by
  simp_rw [mul_neg]
  rw [integral_neg]
  exact neg_pos.mpr (integral_kesten_thermalLocalLog_neg p β)

end
end GaloisForLFunctions.SelbergClass.Primon
