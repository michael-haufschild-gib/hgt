import GaloisForLFunctions.BiScaleUncertainty.WindowEnergyArithmeticQuadrature

/-!
# The zero frequency: net signed mass and the Mertens-type Chebyshev integral

At `ξ = 0` the spectral density of the field reads the net signed mass of `ν_N`,

`ν̂_N(0) = pairing N 1 = Σ_{n ≤ N+2} Λ(n)/√n − 4 sinh(L/2)`,

and the discrepancy transform law turns it into the Chebyshev-error integral

`Σ_{n ≤ N+2} Λ(n)/√n − 4 sinh(L/2) = ½ ∫_0^L Ẽ + Ẽ(L) − 1 + 2e^{−L/2}`,

the classical identity `Σ_{n≤x} Λ(n)/√n = √x + ψ(x)/√x − 1 + ½∫_1^x (ψ(u)−u) u^{−3/2} du` in the
field's coordinates.  The spectral density at the origin is `S_N(0) = 4 (pairing N 1)²`.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators CompactlySupported Real

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar

noncomputable section
set_option autoImplicit false

theorem frequencyCharacter_zero (t : ℝ) : frequencyCharacter 0 t = 1 := by
  unfold frequencyCharacter; simp

theorem criticalPoint_zero : criticalPoint 0 = (1 / 2 : ℂ) := by
  apply Complex.ext <;> simp [criticalPoint]

/-- `ν̂_N(0) = pairing N 1`: the zero frequency is the net signed mass. -/
theorem fourierPairing_zero_eq_pairing_one (N : ℕ) :
    fourierPairing N 0 = (pairing N (fun _ => (1 : ℝ)) : ℂ) := by
  unfold fourierPairing
  rw [← pairingC_ofReal]
  exact congrArg (pairingC N) (funext fun t => by rw [frequencyCharacter_zero]; push_cast; rfl)

theorem integral_polarDensity_Icc (L : ℝ) (hL : 0 ≤ L) :
    (∫ t in Icc 0 L, polarDensity t) = 4 * Real.sinh (L / 2) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t => 4 * Real.sinh (t / 2)) (polarDensity t) t := by
    intro t
    have h := ((hasDerivAt_id t).div_const 2).sinh.const_mul 4
    refine h.congr_deriv ?_
    unfold polarDensity
    simp only [id]; ring
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      (continuous_polarDensity.intervalIntegrable _ _)]
  simp

/-- The net signed mass: `pairing N 1 = Σ_{n≤N+2} Λ(n)/√n − 4 sinh(L/2)`. -/
theorem pairing_one_eq (N : ℕ) :
    pairing N (fun _ => (1 : ℝ)) =
      (∑ n ∈ Finset.Icc 1 (N + 2), primeWeight n) - 4 * Real.sinh (cutoff N / 2) := by
  unfold pairing
  simp only [mul_one]
  rw [integral_polarDensity_Icc (cutoff N) (cutoff_nonneg N)]

/-- **The Mertens-type identity of the field:**
`Σ_{n≤N+2} Λ(n)/√n − 4 sinh(L/2) = ½∫_0^L Ẽ + Ẽ(L) − 1 + 2 e^{−L/2}`. -/
theorem netSignedMass_eq_chebyshev_integral (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 (N + 2), primeWeight n) - 4 * Real.sinh (cutoff N / 2) =
      (1 / 2) * (∫ t in Icc 0 (cutoff N), normalizedLogError t) + normalizedLogError (cutoff N) -
        1 + 2 * Real.exp (-cutoff N / 2) := by
  rw [← pairing_one_eq, pairing_eq_stieltjes_gauge (fun _ => (1 : ℝ)) contDiff_const N]
  have hg : ∀ t, gaugeDerivative (fun _ : ℝ => (1 : ℝ)) t = -(1 / 2) := by
    intro t; unfold gaugeDerivative; simp
  have h1 : (∫ t in Icc 0 (cutoff N), normalizedLogError t * gaugeDerivative (fun _ : ℝ => (1 : ℝ)) t) =
      -(1 / 2) * ∫ t in Icc 0 (cutoff N), normalizedLogError t := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Icc fun t _ => by rw [hg]; ring
  have h2 : (∫ t in Icc 0 (cutoff N), Real.exp (-t / 2) * (1 : ℝ)) =
      2 - 2 * Real.exp (-cutoff N / 2) := by
    have hd : ∀ t : ℝ, HasDerivAt (fun t => -2 * Real.exp (-t / 2)) (Real.exp (-t / 2) * 1) t := by
      intro t
      have h := (((hasDerivAt_neg t).div_const 2).exp).const_mul (-2)
      exact h.congr_deriv (by ring)
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (cutoff_nonneg N),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
        ((Real.continuous_exp.comp (continuous_id.neg.div_const 2)).mul continuous_const
          |>.intervalIntegrable _ _)]
    simp only [neg_zero, zero_div, Real.exp_zero]
    ring
  rw [h1, h2]
  ring

/-- The spectral density at the origin is the squared net signed mass. -/
theorem spectralDensity_zero (N : ℕ) :
    spectralDensity N 0 = 4 * pairing N (fun _ => (1 : ℝ)) ^ 2 := by
  unfold spectralDensity
  rw [fourierPairing_zero_eq_pairing_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  norm_num
  ring

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
