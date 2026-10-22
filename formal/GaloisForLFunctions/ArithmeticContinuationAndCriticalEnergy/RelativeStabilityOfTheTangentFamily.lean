import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheSignedWorkIsTheTangentAutocorrelation

/-!
# Relative stability of the tangent family

The damping autocorrelation is a Gram kernel, so polarisation turns its sign into an angle:

`K_T(η, ε) = (‖E_η‖_T² + ‖E_ε‖_T² − ‖E_η − E_ε‖_T²)/2`,

and `K_T(η, ε) ≥ 0` is exactly the statement that the tangents at the two dampings make a
non-obtuse angle in the pronic metric
(`tangentCorrelation_eq_half_energy_sub_difference`, `nonneg_tangentCorrelation_iff`).  So the
continuation obstruction is not a size problem at all: arbitrarily large tangents are harmless, and
only an *anti-aligned* pair of dampings can obstruct backward continuation.

One sufficient condition is then immediate and has the same shape as the aperture face's
no-crossing law: if, between any two dampings below one half, the tangent changes by no more than
its own size at the outer damping, the angle is non-obtuse and the Riemann hypothesis follows
(`riemannHypothesis_of_relative_tangent_stability`).  Where the floor transport asks for bounded
*relative decay* of a positive ground energy, the damping transport asks for bounded *relative
variation* of the tangent — both are scale-free conditions, and neither needs a bound on the
quantity itself.
-/

open Finset RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. Polarisation in the pronic metric -/

/-- The pronic norm of a difference, expanded: no term is an error term. -/
theorem pronicNorm_sub_sq (T : ℕ) (u v : ℕ → ℝ) :
    pronicNorm T (fun n => u n - v n) ^ 2 =
      pronicNorm T u ^ 2 + pronicNorm T v ^ 2 - 2 * pronicPairing T u v := by
  simp only [pronicNorm_sq, pronicPairing, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- **Polarisation of the damping autocorrelation.**  Its sign is the cosine of the angle between
the tangents at the two dampings. -/
theorem tangentCorrelation_eq_half_energy_sub_difference (T : ℕ) (η ε : ℝ) :
    tangentCorrelation T η ε =
      (pronicNorm T (dampedChebyshevError η) ^ 2 + pronicNorm T (dampedChebyshevError ε) ^ 2 -
        pronicNorm T (fun n => dampedChebyshevError η n - dampedChebyshevError ε n) ^ 2) / 2 := by
  rw [pronicNorm_sub_sq, tangentCorrelation]
  ring

/-- **The sign is an angle condition.**  The autocorrelation is nonnegative exactly when the
difference energy of the two tangents does not exceed the sum of their energies. -/
theorem nonneg_tangentCorrelation_iff (T : ℕ) (η ε : ℝ) :
    0 ≤ tangentCorrelation T η ε ↔
      pronicNorm T (fun n => dampedChebyshevError η n - dampedChebyshevError ε n) ^ 2 ≤
        pronicNorm T (dampedChebyshevError η) ^ 2 +
          pronicNorm T (dampedChebyshevError ε) ^ 2 := by
  rw [tangentCorrelation_eq_half_energy_sub_difference]
  constructor <;> intro h <;> linarith

/-! ## §2. Relative stability of the tangent in the damping -/

/-- **Relative stability gives the angle.**  If the tangent changes by at most its own size at the
outer damping, the autocorrelation is nonnegative. -/
theorem nonneg_tangentCorrelation_of_relative_stability (T : ℕ) (η ε : ℝ)
    (h : pronicNorm T (fun n => dampedChebyshevError η n - dampedChebyshevError ε n) ≤
      pronicNorm T (dampedChebyshevError ε)) :
    0 ≤ tangentCorrelation T η ε := by
  rw [nonneg_tangentCorrelation_iff]
  have hsq : pronicNorm T (fun n => dampedChebyshevError η n - dampedChebyshevError ε n) ^ 2 ≤
      pronicNorm T (dampedChebyshevError ε) ^ 2 :=
    pow_le_pow_left₀ (pronicNorm_nonneg _ _) h 2
  have hη : 0 ≤ pronicNorm T (dampedChebyshevError η) ^ 2 := by positivity
  linarith

/-- **Relative stability of the tangent family implies the Riemann hypothesis.**  A scale-free
condition: between any two dampings below one half the centred damped Chebyshev function moves by
no more than its own pronic size.  No bound on the tangent itself is required, and the budget is
the already paid scalar constant. -/
theorem riemannHypothesis_of_relative_tangent_stability
    (h : ∀ (T : ℕ) (η ε : ℝ), 0 < η → η ≤ ε → ε ≤ 1 / 2 →
      pronicNorm T (fun n => dampedChebyshevError η n - dampedChebyshevError ε n) ≤
        pronicNorm T (dampedChebyshevError ε)) :
    RiemannHypothesis :=
  riemannHypothesis_of_nonneg_tangentCorrelation fun T η ε hη hηε hε =>
    nonneg_tangentCorrelation_of_relative_stability T η ε (h T η ε hη hηε hε)

/-- **Anti-alignment is the only obstruction.**  If the autocorrelation is negative at some pair of
dampings, the tangents there differ by strictly more than the quadratic mean of their sizes: a
large tangent is never by itself an obstruction. -/
theorem difference_energy_gt_of_tangentCorrelation_neg (T : ℕ) (η ε : ℝ)
    (h : tangentCorrelation T η ε < 0) :
    pronicNorm T (dampedChebyshevError η) ^ 2 + pronicNorm T (dampedChebyshevError ε) ^ 2 <
      pronicNorm T (fun n => dampedChebyshevError η n - dampedChebyshevError ε n) ^ 2 := by
  rw [tangentCorrelation_eq_half_energy_sub_difference] at h
  linarith

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
