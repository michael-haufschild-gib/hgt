import GaloisForLFunctions.RHTower.SummablePurePointSurvivalEscapeReturnLaw
import GaloisForLFunctions.RHTower.ProjectiveWeightedBoundedDensityQuantile

/-!
# Countable weighted-phase reduction to a normalized finite head

An almost-return of a normalized countable phase packet forces an
almost-return of every positive-mass normalized finite head. The defect is
amplified by exactly the reciprocal head mass.

This is the deterministic bridge needed to apply a finite-dimensional
small-target probability bound to an actual countably infinite return
event. No independence or probability hypothesis is used here.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Countable weighted phase amplitude. -/
def summableWeightedPhaseAmplitude
    (p : ℕ → ℝ) (z : ℕ → ℂ) : ℂ :=
  ∑' k, (p k : ℂ) * z k

/-- Mass of the first `M` coordinates. -/
def summableWeightedHeadMass (p : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range M, p k

/-- Weight of a normalized finite head. -/
def normalizedWeightedHeadWeight
    (p : ℕ → ℝ) (M : ℕ) (i : Fin M) : ℝ :=
  p i / summableWeightedHeadMass p M

/-- Phase amplitude of a normalized finite head. -/
def normalizedWeightedHeadPhaseAmplitude
    (p : ℕ → ℝ) (z : ℕ → ℂ) (M : ℕ) : ℂ :=
  ∑ i : Fin M, (normalizedWeightedHeadWeight p M i : ℂ) * z i

theorem normalizedWeightedHeadWeight_nonneg
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (M : ℕ) (hmass : 0 < summableWeightedHeadMass p M)
    (i : Fin M) :
    0 ≤ normalizedWeightedHeadWeight p M i := by
  exact div_nonneg (hp i) hmass.le

/-- Positive-mass normalized head weights sum exactly to one. -/
theorem sum_normalizedWeightedHeadWeight
    (p : ℕ → ℝ) (M : ℕ)
    (hmass : 0 < summableWeightedHeadMass p M) :
    ∑ i : Fin M, normalizedWeightedHeadWeight p M i = 1 := by
  change ∑ i : Fin M, p i / summableWeightedHeadMass p M = 1
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => p k / summableWeightedHeadMass p M) M,
    ← Finset.sum_div]
  exact div_self hmass.ne'

/-- Every nonnegative normalized head weight is at most one. -/
theorem normalizedWeightedHeadWeight_le_one
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (M : ℕ) (hmass : 0 < summableWeightedHeadMass p M)
    (i : Fin M) :
    normalizedWeightedHeadWeight p M i ≤ 1 := by
  have hsingle :
      normalizedWeightedHeadWeight p M i ≤
        ∑ j : Fin M, normalizedWeightedHeadWeight p M j :=
    Finset.single_le_sum
      (fun j _hj =>
        normalizedWeightedHeadWeight_nonneg p hp M hmass j)
      (Finset.mem_univ i)
  simpa only [sum_normalizedWeightedHeadWeight p M hmass] using hsingle

/--
Rescaling the normalized head water level by its mass exactly recovers the
water entropy of the original unnormalized head coordinates.
-/
theorem projectiveFullWaterEntropyAt_normalizedHead_rescale
    (p : ℕ → ℝ) (M : ℕ)
    (hmass : 0 < summableWeightedHeadMass p M) (lam : ℝ) :
    projectiveFullWaterEntropyAt
        (normalizedWeightedHeadWeight p M)
        (summableWeightedHeadMass p M * lam) =
      (1 / 2 : ℝ) *
        ∑ i : Fin M, Real.log (max 1 (lam * p i)) := by
  rw [projectiveFullWaterEntropyAt]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  congr 2
  rw [normalizedWeightedHeadWeight]
  field_simp [hmass.ne']

/-- Exact head-plus-tail mass split. -/
theorem summableWeightedHeadMass_add_tail
    (p : ℕ → ℝ) (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (M : ℕ) :
    summableWeightedHeadMass p M + ∑' j, p (M + j) = 1 := by
  have hsplit := (hsum.sum_add_tsum_nat_add M).trans htotal
  rw [summableWeightedHeadMass]
  calc
    (∑ k ∈ Finset.range M, p k) + ∑' j, p (M + j) =
        (∑ k ∈ Finset.range M, p k) + ∑' j, p (j + M) := by
          congr 1
          apply tsum_congr
          intro j
          rw [Nat.add_comm]
    _ = 1 := hsplit

/-- Exact finite-head plus countable-tail phase-amplitude split. -/
theorem summableWeightedPhaseAmplitude_eq_head_add_tail
    (p : ℕ → ℝ) (z : ℕ → ℂ)
    (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (hz : ∀ k, ‖z k‖ = 1) (M : ℕ) :
    summableWeightedPhaseAmplitude p z =
      (∑ k ∈ Finset.range M, (p k : ℂ) * z k) +
        ∑' j, (p (M + j) : ℂ) * z (M + j) := by
  have hterm :
      Summable (fun k => (p k : ℂ) * z k) := by
    apply Summable.of_norm
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hp _), hz, mul_one] using hsum
  rw [summableWeightedPhaseAmplitude]
  calc
    (∑' k, (p k : ℂ) * z k) =
        (∑ k ∈ Finset.range M, (p k : ℂ) * z k) +
          ∑' j, (p (j + M) : ℂ) * z (j + M) :=
      (hterm.sum_add_tsum_nat_add M).symm
    _ = (∑ k ∈ Finset.range M, (p k : ℂ) * z k) +
          ∑' j, (p (M + j) : ℂ) * z (M + j) := by
      congr 1
      apply tsum_congr
      intro j
      rw [Nat.add_comm]

/-- Norm of the discarded phase tail is bounded by its exact probability
mass. -/
theorem norm_summableWeightedPhaseTail_le
    (p : ℕ → ℝ) (z : ℕ → ℂ)
    (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (hz : ∀ k, ‖z k‖ = 1) (M : ℕ) :
    ‖∑' j, (p (M + j) : ℂ) * z (M + j)‖ ≤
      ∑' j, p (M + j) := by
  have hterm :
      Summable (fun k => (p k : ℂ) * z k) := by
    apply Summable.of_norm
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hp _), hz, mul_one] using hsum
  have htail :
      Summable (fun j => (p (M + j) : ℂ) * z (M + j)) := by
    have hshift :
        Summable (fun j => (p (j + M) : ℂ) * z (j + M)) :=
      (summable_nat_add_iff M).mpr hterm
    exact hshift.congr (fun j => by rw [Nat.add_comm])
  calc
    ‖∑' j, (p (M + j) : ℂ) * z (M + j)‖ ≤
        ∑' j, ‖(p (M + j) : ℂ) * z (M + j)‖ :=
      norm_tsum_le_tsum_norm htail.norm
    _ = ∑' j, p (M + j) := by
      apply tsum_congr
      intro j
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hp _), hz, mul_one]

/-- The unnormalized head amplitude is head mass times normalized-head
amplitude. -/
theorem unnormalizedHeadAmplitude_eq_mass_mul_normalized
    (p : ℕ → ℝ) (z : ℕ → ℂ) (M : ℕ)
    (hmass : 0 < summableWeightedHeadMass p M) :
    (∑ k ∈ Finset.range M, (p k : ℂ) * z k) =
      (summableWeightedHeadMass p M : ℂ) *
        normalizedWeightedHeadPhaseAmplitude p z M := by
  rw [normalizedWeightedHeadPhaseAmplitude]
  simp_rw [normalizedWeightedHeadWeight]
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ =>
      ((p k / summableWeightedHeadMass p M : ℝ) : ℂ) * z k) M,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  push_cast
  field_simp [hmass.ne']

/--
An amplitude return of the complete countable packet forces return of its
normalized finite head, with exact defect `η / headMass`.
-/
theorem full_coherence_implies_normalized_head_coherence
    (p : ℕ → ℝ) (z : ℕ → ℂ)
    (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (htotal : ∑' k, p k = 1)
    (hz : ∀ k, ‖z k‖ = 1)
    (M : ℕ) (hmass : 0 < summableWeightedHeadMass p M)
    {η : ℝ}
    (hreturn : 1 - η ≤ ‖summableWeightedPhaseAmplitude p z‖) :
    1 - η / summableWeightedHeadMass p M ≤
      ‖normalizedWeightedHeadPhaseAmplitude p z M‖ := by
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
  have hhead :
      H = (m : ℂ) * normalizedWeightedHeadPhaseAmplitude p z M := by
    simpa only [H, m] using
      unnormalizedHeadAmplitude_eq_mass_mul_normalized p z M hmass
  have hfull :
      ‖summableWeightedPhaseAmplitude p z‖ ≤
        m * ‖normalizedWeightedHeadPhaseAmplitude p z M‖ + r := by
    rw [hsplit]
    calc
      ‖H + T‖ ≤ ‖H‖ + ‖T‖ := norm_add_le _ _
      _ ≤ ‖H‖ + r := by
        simpa [add_comm] using add_le_add_right htail ‖H‖
      _ = m * ‖normalizedWeightedHeadPhaseAmplitude p z M‖ + r := by
        rw [hhead, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hmass]
  have hraw :
      1 - η ≤
        m * ‖normalizedWeightedHeadPhaseAmplitude p z M‖ + r :=
    hreturn.trans hfull
  have hm : 0 < m := by simpa only [m] using hmass
  change 1 - η / m ≤
    ‖normalizedWeightedHeadPhaseAmplitude p z M‖
  have hrearrange : 1 - η / m = (m - η) / m := by
    field_simp [hm.ne']
  rw [hrearrange]
  apply (div_le_iff₀ hm).2
  nlinarith

end RHTower
