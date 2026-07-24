import GaloisForLFunctions.RHTower.CCMPhysicalPrimeApertureCharacterTomography
import GaloisForLFunctions.RHTower.TentDivisorRecovery

/-!
# CCM bulk-character tent-pole detection universality

The physical CCM character decomposition and the moving-tent divisor theorem use the same
rectangular amplitude.  A nonzero edge-free character channel therefore certifies that the
amplitude cannot erase a zeta zero at the matching character rate, forcing a genuine tent pole.
-/

open Filter Topology Complex

namespace RHTower

noncomputable section

/-- **CCM bulk-character tent-pole detection universality law.**  If a nonconstant physical
aperture character lands on a zeta zero and its edge-free prime channel is nonzero, the
corresponding moving-tent observable has no finite limit at that shifted zero. -/
theorem ccmBulkCharacter_nonzero_forces_tentPoleUniversality
    (P : Finset Nat.Primes) {A m k : ℝ} {n : ℤ}
    (hA : 0 < A) (hn : n ≠ 0)
    (hbulk : ∀ p ∈ P,
      0 ≤ m - Real.log (p : ℝ) ∧
        k - Real.log (p : ℝ) ≤ A)
    (hmk : m ≤ k)
    (hzero :
      riemannZeta
        (1 / 2 + xiPhysicalApertureCharacterRate A n) = 0)
    (hchannel :
      xiPhysicalPrimeLogCharacterAmplitude P A n m k ≠ 0) :
    ¬ ∃ M : ℂ,
      Tendsto (PcalObservable (k - m))
        (𝓝[≠]
          ((1 / 2 + xiPhysicalApertureCharacterRate A n) + 1 / 2))
        (𝓝 M) := by
  let ρ : ℂ := 1 / 2 + xiPhysicalApertureCharacterRate A n
  have hfactor :=
    xiPhysicalPrimeLogCharacterAmplitude_eq_bulk_twistedSum
      P n hbulk hmk
  have hrect :
      rectangularWindowAmplitude (k - m)
        (xiPhysicalApertureCharacterRate A n) ≠ 0 := by
    intro hvanish
    apply hchannel
    rw [hfactor, hvanish]
    simp
  have hrate :
      xiPhysicalApertureCharacterRate A n ≠ 0 :=
    xiPhysicalApertureCharacterRate_ne_zero hA hn
  have hρre : ρ.re = 1 / 2 := by
    simp [ρ, xiPhysicalApertureCharacterRate]
  have hρ0 : 0 < ρ.re := by
    rw [hρre]
    norm_num
  have hρ1 : ρ ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [hρre] at hre
    norm_num at hre
  have hρhalf : ρ ≠ 1 / 2 := by
    intro h
    apply hrate
    dsimp [ρ] at h
    linear_combination h
  have hρzero : riemannZeta ρ = 0 := by
    simpa [ρ, add_comm] using hzero
  have hρamp :
      rectangularWindowAmplitude (k - m) (ρ - 1 / 2) ≠ 0 := by
    simpa [ρ] using hrect
  exact PcalObservable_no_limit_of_amplitude_ne
    (k - m) (sub_nonneg.mpr hmk) hρzero hρ1 hρ0 hρhalf hρamp

end

end RHTower
