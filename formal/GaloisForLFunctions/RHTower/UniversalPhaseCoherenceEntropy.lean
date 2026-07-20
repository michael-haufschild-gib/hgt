import GaloisForLFunctions.HilbertMetric.CentroidGauge
import GaloisForLFunctions.RHTower.CCMPrimePoleFiniteCoherence

/-!
# Universal high-dimensional phase-coherence entropy

This file begins the unconditional formalization of the universal half-entropy
law for near-perfect phase recurrence.  It isolates the algebraic target
geometry: a nearly coherent unit phase packet has a pivot whose total squared
phase distance is small.
-/

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace RHTower

open GaloisForLFunctions.HilbertMetric

variable {d : Type*} [Fintype d] [Nonempty d]

/-- The normalized equal-weight phase amplitude. -/
def equalPhaseAmplitude (phase : d → ℂ) : ℂ :=
  hilbertCentroid phase

/-- The ordered pairwise squared-distance energy of a finite phase packet. -/
def phasePairwiseSqEnergy (phase : d → ℂ) : ℝ :=
  ∑ i, ∑ j, ‖phase i - phase j‖ ^ 2

/-- For unit phases, ordered pairwise energy is exactly twice the square of
the cardinality times the fidelity deficit of the normalized amplitude. -/
theorem phasePairwiseSqEnergy_eq_two_card_sq_mul_fidelityDeficit
    (phase : d → ℂ) (hphase : ∀ i, ‖phase i‖ = 1) :
    phasePairwiseSqEnergy phase =
      2 * (Fintype.card d : ℝ) ^ 2 *
        (1 - ‖equalPhaseAmplitude phase‖ ^ 2) := by
  let D : ℝ := Fintype.card d
  have hDpos : 0 < D := by
    have hcard : 0 < Fintype.card d := Fintype.card_pos
    dsimp only [D]
    exact_mod_cast hcard
  have hcenter := sum_norm_sub_sq_eq_centered_add_card_mul phase (0 : ℂ)
  have hcentered :
      ∑ i, ‖phase i - hilbertCentroid phase‖ ^ 2 =
        D * (1 - ‖hilbertCentroid phase‖ ^ 2) := by
    simp only [sub_zero, hphase, one_pow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at hcenter
    nlinarith
  rw [phasePairwiseSqEnergy,
    sum_pairwise_norm_sub_sq_eq_two_card_mul_centered, hcentered]
  simp only [equalPhaseAmplitude, D]
  ring

/-- **Pairwise-variance pivot.**  If an equal-weight unit phase packet has
coherence at least `1 - η`, then some phase sees total squared distance at
most `4 η d` from the whole packet. -/
theorem exists_phasePivot_sum_norm_sub_sq_le
    (phase : d → ℂ) (hphase : ∀ i, ‖phase i‖ = 1)
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hcoh : 1 - η ≤ ‖equalPhaseAmplitude phase‖) :
    ∃ k, ∑ j, ‖phase j - phase k‖ ^ 2 ≤
      4 * η * (Fintype.card d : ℝ) := by
  let D : ℝ := Fintype.card d
  have hDpos : 0 < D := by
    have hcard : 0 < Fintype.card d := Fintype.card_pos
    dsimp only [D]
    exact_mod_cast hcard
  have hsq : (1 - η) ^ 2 ≤ ‖equalPhaseAmplitude phase‖ ^ 2 := by
    exact (sq_le_sq₀ (sub_nonneg.mpr hη1) (norm_nonneg _)).2 hcoh
  have hpair : phasePairwiseSqEnergy phase ≤ 4 * η * D ^ 2 := by
    rw [phasePairwiseSqEnergy_eq_two_card_sq_mul_fidelityDeficit phase hphase]
    nlinarith [sq_nonneg η]
  by_contra h
  push Not at h
  have hstrict :
      ∑ _k : d, (4 * η * D) < ∑ k, ∑ j, ‖phase j - phase k‖ ^ 2 := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro k hk
    simpa only [D] using h k
  have hleft : ∑ _k : d, (4 * η * D) = 4 * η * D ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, D]
    ring
  have hright :
      (∑ k, ∑ j, ‖phase j - phase k‖ ^ 2) =
        phasePairwiseSqEnergy phase := by
    rw [phasePairwiseSqEnergy, Finset.sum_comm]
  rw [hleft, hright] at hstrict
  exact (not_lt_of_ge hpair) hstrict

/-- The normalized amplitude of a `d`-frequency phase clock. -/
def phaseClockAmplitude {d : ℕ} (ω : Fin d → ℝ) (n : ℕ) : ℂ :=
  ∑ i, (((d : ℝ)⁻¹ : ℂ) *
    Complex.exp (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ)))

/-- The phase-clock amplitude is the Hilbert centroid of its unit phases. -/
theorem phaseClockAmplitude_eq_equalPhaseAmplitude
    {d : ℕ} [NeZero d] (ω : Fin d → ℝ) (n : ℕ) :
    phaseClockAmplitude ω n = equalPhaseAmplitude
      (fun i ↦ Complex.exp (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))) := by
  rw [phaseClockAmplitude, equalPhaseAmplitude, hilbertCentroid]
  rw [Fintype.card_fin, Complex.real_smul, Complex.ofReal_inv, Finset.mul_sum]

/-- **Universal finite coherence ceiling.**  Every packet of `d` real
frequencies has a positive clock no larger than `(Q+1)^d` at which its
normalized amplitude loses at most `2π²/(Q+1)²` from perfect coherence. -/
theorem exists_phaseClockAmplitude_coherence_quantitative
    {d Q : ℕ} (hd : 0 < d) (ω : Fin d → ℝ) :
    ∃ n : ℕ, 0 < n ∧ n ≤ (Q + 1) ^ d ∧
      1 - (2 * Real.pi / (Q + 1 : ℝ)) ^ 2 / 2 ≤
        ‖phaseClockAmplitude ω n‖ := by
  letI : NeZero d := ⟨hd.ne'⟩
  obtain ⟨n, hnpos, hnTop, r, hr⟩ :=
    exists_fin_simultaneous_two_pi_phase_approximation_quantitative
      (Q := Q) ω
  refine ⟨n, hnpos, hnTop, ?_⟩
  have hweight : ∑ _i : Fin d, (1 / (d : ℝ)) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hfloor :=
    nonnegative_weighted_phaseSum_norm_floor_of_phase_approximation
      n ω (fun _i : Fin d ↦ 1 / (d : ℝ)) r
        (2 * Real.pi / (Q + 1 : ℝ)) (by positivity)
        (fun _i ↦ by positivity) hr
  rw [hweight, mul_one] at hfloor
  simpa only [phaseClockAmplitude, one_div, Complex.ofReal_inv,
    Complex.ofReal_natCast] using hfloor

end RHTower
