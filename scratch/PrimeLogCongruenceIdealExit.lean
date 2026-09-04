import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesApertureResidueTransport

/-!
# Prime-log congruence ideal exit

Inverse prime heat multiplies the literal transported Stokes density at aperture `d` by
`p^(2u)`.  The resulting diagonal is summable exactly before `u=d`; at `u=d` its first clock is
the universal `log(p)^2 / p` completion-anomaly ray.
-/

namespace RHTower

noncomputable section

/-- Prime diagonal after inverse prime-heat congruence by time `u`. -/
def primeLogCongruenceWeight (d u : ℝ) (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ (2 * u) *
    routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p

theorem primeLogCongruenceWeight_eq
    {d : ℝ} (hd : 0 < d) (u : ℝ) (p : Nat.Primes) :
    primeLogCongruenceWeight d u p =
      8 * d * Real.log (p : ℝ) *
        (p : ℝ) ^ (-(1 + 2 * (d - u))) := by
  rw [primeLogCongruenceWeight,
    routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_eq hd,
    gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm,
    abs_of_pos hd, xiMassPrimeSquareEulerWeight_eq]
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  rw [← Real.rpow_add hp]
  congr 1
  ring

theorem primeLogCongruenceWeight_nonneg
    {d u : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    0 ≤ primeLogCongruenceWeight d u p := by
  rw [primeLogCongruenceWeight]
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_nonneg hd p)

/-- Before ideal exit, inverse heat merely changes the positive aperture and a global scalar. -/
theorem primeLogCongruenceWeight_eq_rescaled_transport
    {d u : ℝ} (hd : 0 < d) (hu : u < d) (p : Nat.Primes) :
    primeLogCongruenceWeight d u p =
      (d / (d - u)) *
        routePPrimitiveGammaJuliaStokesTransportedPrimeWeight (d - u) p := by
  have hdu : 0 < d - u := sub_pos.mpr hu
  rw [primeLogCongruenceWeight_eq hd,
    routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_eq hdu,
    gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm,
    abs_of_pos hdu, xiMassPrimeSquareEulerWeight_eq]
  field_simp [hdu.ne']
  ring

theorem summable_primeLogCongruenceWeight_of_lt
    {d u : ℝ} (hu0 : 0 ≤ u) (hu : u < d) :
    Summable (primeLogCongruenceWeight d u) := by
  have hdu : 0 < d - u := sub_pos.mpr hu
  have hsum :=
    (summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hdu).mul_left
      (d / (d - u))
  exact hsum.congr fun p =>
    (primeLogCongruenceWeight_eq_rescaled_transport
      (lt_of_le_of_lt hu0 hu) hu p).symm

/-- Exact trace-ideal wall density. -/
theorem primeLogCongruenceWeight_exit_eq
    {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    primeLogCongruenceWeight d d p =
      8 * d * Real.log (p : ℝ) / (p : ℝ) := by
  rw [primeLogCongruenceWeight_eq hd]
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  rw [show -(1 + 2 * (d - d)) = (-1 : ℝ) by ring, Real.rpow_neg_one]
  ring

theorem not_summable_primeLogCongruenceWeight_of_le
    {d u : ℝ} (hd : 0 < d) (hdu : d ≤ u) :
    ¬ Summable (primeLogCongruenceWeight d u) := by
  intro hsum
  let c : ℝ := 8 * d * Real.log 2
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hlower : ∀ p : Nat.Primes,
      c * (1 / (p : ℝ)) ≤ primeLogCongruenceWeight d u p := by
    intro p
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.one_lt.le
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
    have hpow : (p : ℝ) ^ (2 * d) ≤ (p : ℝ) ^ (2 * u) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    have htransport := routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_pos hd p
    have hmono : primeLogCongruenceWeight d d p ≤
        primeLogCongruenceWeight d u p := by
      rw [primeLogCongruenceWeight, primeLogCongruenceWeight]
      exact mul_le_mul_of_nonneg_right hpow htransport.le
    have hlog : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by norm_num) hp2
    calc
      c * (1 / (p : ℝ)) ≤
          (8 * d * Real.log (p : ℝ)) * (1 / (p : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog (by positivity)) (by positivity)
      _ = primeLogCongruenceWeight d d p := by
        rw [primeLogCongruenceWeight_exit_eq hd]
        ring
      _ ≤ primeLogCongruenceWeight d u p := hmono
  have hscaled : Summable (fun p : Nat.Primes => c * (1 / (p : ℝ))) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hlower hsum
  have hharmonic : Summable (fun p : Nat.Primes => 1 / (p : ℝ)) :=
    (summable_mul_left_iff hc.ne').mp hscaled
  exact Nat.Primes.not_summable_one_div hharmonic

/-- Literal source-flow classification: inverse prime heat remains in the trace ideal exactly
until the formation aperture. -/
theorem summable_primeLogCongruenceWeight_iff
    {d u : ℝ} (hd : 0 < d) (hu0 : 0 ≤ u) :
    Summable (primeLogCongruenceWeight d u) ↔ u < d := by
  constructor
  · intro hsum
    exact lt_of_not_ge fun hdu =>
      not_summable_primeLogCongruenceWeight_of_le hd hdu hsum
  · exact summable_primeLogCongruenceWeight_of_lt hu0

/-- First prime clock at ideal exit is exactly the universal `log^2(p)/p` anomaly ray. -/
theorem log_mul_primeLogCongruenceWeight_exit_eq
    {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    Real.log (p : ℝ) * primeLogCongruenceWeight d d p =
      8 * d * Real.log (p : ℝ) ^ 2 / (p : ℝ) := by
  rw [primeLogCongruenceWeight_exit_eq hd]
  ring

end

end RHTower
