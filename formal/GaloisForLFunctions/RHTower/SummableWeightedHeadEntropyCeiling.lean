import GaloisForLFunctions.RHTower.SummableWeightedHeadReduction
import GaloisForLFunctions.RHTower.ProjectiveCanonicalWaterEntropy

/-!
# Countable weighted recurrence ceiling from finite-head water entropy

This file supplies the constructive half of the countable recurrence clock.
A recurrence of a positive-mass normalized finite head forces recurrence of
the complete countable packet. The exact amplitude defect is

`headMass * headDefect + 2 * tailMass`.

Combining that analytic reduction with the finite anisotropic water-filling
deadline yields a countable return clock whose logarithmic cost is canonical
water entropy plus only a linear active-coordinate implementation term.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/--
Coherence of a positive-mass normalized head forces coherence of the
complete countable packet. The exact loss is head defect times head mass
plus twice the discarded tail mass.
-/
theorem normalized_head_coherence_implies_full_coherence
    (p : ℕ → ℝ) (z : ℕ → ℂ)
    (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (htotal : ∑' k, p k = 1)
    (hz : ∀ k, ‖z k‖ = 1)
    (M : ℕ) (hmass : 0 < summableWeightedHeadMass p M)
    {η : ℝ}
    (hhead :
      1 - η ≤ ‖normalizedWeightedHeadPhaseAmplitude p z M‖) :
    1 - (summableWeightedHeadMass p M * η +
        2 * ∑' j, p (M + j)) ≤
      ‖summableWeightedPhaseAmplitude p z‖ := by
  let m : ℝ := summableWeightedHeadMass p M
  let r : ℝ := ∑' j, p (M + j)
  let H : ℂ := ∑ k ∈ Finset.range M, (p k : ℂ) * z k
  let T : ℂ := ∑' j, (p (M + j) : ℂ) * z (M + j)
  have hsplit :
      summableWeightedPhaseAmplitude p z = H + T := by
    simpa only [H, T] using
      summableWeightedPhaseAmplitude_eq_head_add_tail
        p z hp hsum hz M
  have hmassTail : m + r = 1 := by
    simpa only [m, r] using
      summableWeightedHeadMass_add_tail p hsum htotal M
  have htail : ‖T‖ ≤ r := by
    simpa only [T, r] using
      norm_summableWeightedPhaseTail_le p z hp hsum hz M
  have hheadExact :
      H = (m : ℂ) * normalizedWeightedHeadPhaseAmplitude p z M := by
    simpa only [H, m] using
      unnormalizedHeadAmplitude_eq_mass_mul_normalized p z M hmass
  have hheadNorm :
      m * (1 - η) ≤ ‖H‖ := by
    rw [hheadExact, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by simpa only [m] using hmass)]
    exact mul_le_mul_of_nonneg_left hhead hmass.le
  have hreverse : ‖H‖ - ‖T‖ ≤ ‖H + T‖ := by
    simpa only [norm_neg, sub_neg_eq_add] using
      (norm_sub_norm_le H (-T))
  rw [hsplit]
  change 1 - (m * η + 2 * r) ≤ ‖H + T‖
  calc
    1 - (m * η + 2 * r) = m * (1 - η) - r := by
      linarith
    _ ≤ ‖H‖ - ‖T‖ := sub_le_sub hheadNorm htail
    _ ≤ ‖H + T‖ := hreverse

/--
Any universal recurrence deadline for a normalized finite head is a
deadline for the full countable packet at the exact head-plus-tail defect.
-/
theorem countableWeightedCoherence_of_normalizedHeadDeadline
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (M T : ℕ) (hmass : 0 < summableWeightedHeadMass p M)
    {η : ℝ}
    (hdeadline :
      IsUniversalProjectiveWeightedCoherenceDeadline
        (normalizedWeightedHeadWeight p M) η T)
    (omega : ℕ → ℝ) :
    ∃ n : ℕ, 0 < n ∧ n ≤ T ∧
      1 - (summableWeightedHeadMass p M * η +
          2 * ∑' j, p (M + j)) ≤
        ‖summableWeightedPhaseAmplitude p (fun k =>
          Complex.exp
            (Complex.I * ((((n : ℝ) * omega k : ℝ) : ℂ))))‖ := by
  obtain ⟨n, hn0, hnT, hncoh⟩ :=
    hdeadline (fun i => omega i)
  refine ⟨n, hn0, hnT, ?_⟩
  apply normalized_head_coherence_implies_full_coherence
    p
    (fun k => Complex.exp
      (Complex.I * ((((n : ℝ) * omega k : ℝ) : ℂ))))
    hp hsum htotal
    (fun k => by
      rw [show Complex.I * ((((n : ℝ) * omega k : ℝ) : ℂ)) =
        ((((n : ℝ) * omega k : ℝ) : ℂ)) * Complex.I by ring,
        Complex.norm_exp_ofReal_mul_I])
    M hmass
  · simpa only [normalizedWeightedHeadPhaseAmplitude] using hncoh

/--
Countable water-entropy recurrence ceiling. A finite positive-mass head
supplies a universal return deadline for every countable frequency packet;
its logarithmic cost is the canonical projective water entropy plus only
the finite active-coordinate implementation cost.
-/
theorem exists_countableWeightedCoherenceDeadline_headEntropyCeiling
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (M : ℕ) (hM : 2 ≤ M)
    (hmass : 0 < summableWeightedHeadMass p M)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) :
    ∃ T : ℕ,
      (∀ omega : ℕ → ℝ, ∃ n : ℕ,
        0 < n ∧ n ≤ T ∧
        1 - (summableWeightedHeadMass p M * η +
            2 * ∑' j, p (M + j)) ≤
          ‖summableWeightedPhaseAmplitude p (fun k =>
            Complex.exp
              (Complex.I * ((((n : ℝ) * omega k : ℝ) : ℂ))))‖) ∧
      Real.log (T : ℝ) ≤
        projectiveCanonicalWaterEntropyMinimum
            (by omega : 0 < M)
            (normalizedWeightedHeadWeight p M) η +
          (M - 1 : ℕ) *
            Real.log projectivePhaseResolutionConstant := by
  obtain ⟨T, hdeadline, _hlower, hupper⟩ :=
    exists_universalProjectiveWeightedCoherenceDeadline_entropySandwich
      hM
      (normalizedWeightedHeadWeight p M)
      (fun i => normalizedWeightedHeadWeight_nonneg p hp M hmass i)
      (sum_normalizedWeightedHeadWeight p M hmass)
      hη0 hη1
  exact ⟨T,
    fun omega =>
      countableWeightedCoherence_of_normalizedHeadDeadline
        p hp hsum htotal M T hmass hdeadline omega,
    hupper⟩

end RHTower
