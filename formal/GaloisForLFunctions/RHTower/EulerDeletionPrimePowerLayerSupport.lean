import GaloisForLFunctions.RHTower.EulerDeletionNestedProjectionCovariance
import GaloisForLFunctions.RHTower.EulerDeletionPrimePowerClockSupport

/-!
# Prime-power support of Euler-deletion history energy

Chronological EDQ history layers can change only when their next modulus is a
prime power. This is an exact support reduction of the literal physical
energy: every surviving layer retains its complete signed reverse Möbius tail.
-/

noncomputable section

open Finset

namespace RHTower.DeletionResidueMartingale

/-- A non-prime-power step introduces no new physical chronological layer. -/
theorem historyLayer_eq_zero_of_not_isPrimePow (l : ℕ)
    (hl : ¬ IsPrimePow (l + 1)) : historyLayer l = 0 :=
  historyLayer_eq_zero_of_dvd_clock l (successor_dvd_clock_of_not_isPrimePow l hl)

/-- A non-prime-power layer makes no contribution to the complete predictable
drift, independently of its later Möbius tail. -/
theorem historyLayer_predictableDrift_eq_zero_of_not_isPrimePow (l N : ℕ)
    (hl : ¬ IsPrimePow (l + 1)) : historyLayer l (predictableDrift N) = 0 := by
  rw [historyLayer_eq_zero_of_not_isPrimePow l hl]
  rfl

/-- The literal EDQ layer energy is supported exactly on prime-power clock
steps. No term in a surviving square has been separated or estimated. -/
theorem predictableDrift_historyLayer_energy_eq_primePower_filter (N : ℕ) :
    ∑ l ∈ range N, ‖historyLayer l (predictableDrift N)‖ ^ 2 =
      ∑ l ∈ (range N).filter (fun l => IsPrimePow (l + 1)),
        ‖historyLayer l (predictableDrift N)‖ ^ 2 := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hp : IsPrimePow (l + 1)
  · simp [hp]
  · rw [historyLayer_predictableDrift_eq_zero_of_not_isPrimePow l N hp]
    simp [hp]

/-- Fully source-faithful prime-power support reduction for EDQ drift energy.
Every retained summand is the exact complete reverse Möbius tail of that
prime-power history layer. -/
theorem predictableDrift_norm_sq_eq_primePower_reverse_tail_layer_energy (N : ℕ) :
    ‖predictableDrift N‖ ^ 2 =
      ‖(historySpace 0).starProjection (predictableDrift N)‖ ^ 2 +
        ∑ l ∈ (range N).filter (fun l => IsPrimePow (l + 1)),
          ‖∑ i ∈ range N, if l < i then
            ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) •
              historyLayer l (residueVec (i + 1)) else 0‖ ^ 2 := by
  rw [predictableDrift_norm_sq_eq_historyLayer_sum,
    predictableDrift_historyLayer_energy_eq_primePower_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [historyLayer_predictableDrift_eq_reverse_tail]

end RHTower.DeletionResidueMartingale
