import GaloisForLFunctions.HTGeometry.UniversalProjectiveRecurrencePhaseDiagramLaw
import GaloisForLFunctions.HTGeometry.FiniteSpectralHaarRecurrenceLaw

/-!
# Replica phase-cycling tomography of recurrence walls

Independent spectral phase cycling turns an actual survival-fidelity replica
measurement into an exact Fourier tomography protocol. Haar demodulation by
one selected character returns precisely its collected positive replica
coefficient. Multiplying that scalar readout by the controlled-time reporter
therefore isolates the resolved recurrence-wall signal: every lower replica
layer vanishes, while the first allowed layer has positive weight and the
exact inverse-time sinc normal profile.
-/

open MeasureTheory
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem fourier_one_pow
    (z : UnitAddCircle) (n : ℕ) :
    fourier 1 z ^ n = fourier (n : ℤ) z := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [pow_succ, hn, ← fourier_add]
      norm_num

theorem fourier_neg_one_pow
    (z : UnitAddCircle) (n : ℕ) :
    fourier (-1) z ^ n = fourier (-(n : ℤ)) z := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [pow_succ, hn, ← fourier_add]
      push_cast
      congr 2
      omega

theorem replicaPhaseProduct_eq_mFourier
    {I : Type*} [Fintype I]
    (p q : I → ℕ) (x : UnitAddTorus I) :
    (∏ i, fourier 1 (x i) ^ p i) *
        (∏ i, fourier (-1) (x i) ^ q i) =
      UnitAddTorus.mFourier (replicaMultiplicityCharacter p q) x := by
  rw [← Finset.prod_mul_distrib]
  unfold UnitAddTorus.mFourier replicaMultiplicityCharacter
  simp only [ContinuousMap.coe_mk]
  apply Finset.prod_congr rfl
  intro i hi
  rw [fourier_one_pow, fourier_neg_one_pow, ← fourier_add]
  congr 2

/-- Survival-fidelity replica measured after independently cycling all spectral phases. -/
def phaseCycledSurvivalFidelityReplica
    {I : Type*} [Fintype I]
    (weight : I → ℝ) (n : ℕ) (x : UnitAddTorus I) : ℂ :=
  ((∑ i, (weight i : ℂ) * fourier 1 (x i)) ^ n) *
    ((∑ i, (weight i : ℂ) * fourier (-1) (x i)) ^ n)

theorem phaseCycledSurvivalFidelityReplica_eq_characterExpansion
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight : I → ℝ) (n : ℕ) (x : UnitAddTorus I) :
    phaseCycledSurvivalFidelityReplica weight n x =
      ∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
            UnitAddTorus.mFourier (replicaMultiplicityCharacter p q) x := by
  rw [phaseCycledSurvivalFidelityReplica,
    complexFidelityReplicaMultiplicityExpansion]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [mul_assoc, replicaPhaseProduct_eq_mFourier]

/-- Scalar phase-cycling readout selecting one replica character. -/
def phaseCycledReplicaCharacterReadout
    {I : Type*} [Fintype I]
    (weight : I → ℝ) (n : ℕ) (k : I → ℤ) : ℂ :=
  ∫ x, phaseCycledSurvivalFidelityReplica weight n x *
      UnitAddTorus.mFourier (-k) x
    ∂(finiteTorusHaarProbabilityMeasure I : Measure (UnitAddTorus I))

/-- Exact phase-cycling tomography: the scalar Haar-demodulated readout is
the collected survival-fidelity coefficient of the selected character. -/
theorem phaseCycledReplicaCharacterReadout_eq_coefficient
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight : I → ℝ) (n : ℕ) (k : I → ℤ) :
    phaseCycledReplicaCharacterReadout weight n k =
      fidelityReplicaCharacterCoefficient weight n k := by
  unfold phaseCycledReplicaCharacterReadout
    fidelityReplicaCharacterCoefficient
  push_cast
  simp_rw [phaseCycledSurvivalFidelityReplica_eq_characterExpansion]
  simp_rw [Finset.sum_mul]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro q hq
      simp_rw [mul_assoc, ← UnitAddTorus.mFourier_add]
      rw [MeasureTheory.integral_const_mul,
        finiteTorusHaarProbabilityMeasure_mFourier_integral]
      by_cases hchar : replicaMultiplicityCharacter p q = k
      · subst k
        simp
      · have hsum : replicaMultiplicityCharacter p q + -k ≠ 0 := by
          simpa [sub_eq_add_neg] using (sub_ne_zero.mpr hchar)
        simp [hchar, hsum]
    · intro q hq
      exact (by fun_prop : Continuous (fun x : UnitAddTorus I =>
        (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
          UnitAddTorus.mFourier (replicaMultiplicityCharacter p q) x *
            UnitAddTorus.mFourier (-k) x)).integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _)
  · intro p hp
    exact (by fun_prop : Continuous (fun x : UnitAddTorus I =>
      ∑ q ∈ Finset.univ.piAntidiag n,
        (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
          UnitAddTorus.mFourier (replicaMultiplicityCharacter p q) x *
            UnitAddTorus.mFourier (-k) x)).integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _)

/-- Phase-cycled scalar readout of one controlled recurrence wall. -/
def phaseCycledControlledWallReadout
    {I X : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (weight : I → ℝ) (n : ℕ) (k : ProjectiveCharacter I)
    (energy : I → ℝ) (response : I → X →L[ℝ] ℝ)
    (T : ℝ) (x : X) : ℂ :=
  phaseCycledReplicaCharacterReadout weight n
      (finiteCharacterOfProjective k) *
    controlledRecurrenceWallReporter k energy response T x

/-- The scalar phase-cycling protocol isolates exactly the resolved wall
contribution used by the arithmetic phase diagram. -/
theorem phaseCycledControlledWallReadout_eq_resolvedSignal
    {I X : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (weight : I → ℝ) (n : ℕ) (k : ProjectiveCharacter I)
    (energy : I → ℝ) (response : I → X →L[ℝ] ℝ)
    (T : ℝ) (x : X) :
    phaseCycledControlledWallReadout weight n k energy response T x =
      resolvedControlledReplicaWallSignal weight n k energy response T x := by
  rw [phaseCycledControlledWallReadout,
    resolvedControlledReplicaWallSignal,
    phaseCycledReplicaCharacterReadout_eq_coefficient]

/-- The phase-cycled scalar wall readout is identically zero below the
character's exact minimum replica height. -/
theorem phaseCycledControlledWallReadout_eq_zero_of_lt_height
    {I X : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {weight : I → ℝ} (hweight : ∀ i, 0 < weight i)
    (n : ℕ) (k : ProjectiveCharacter I)
    (hlt : n < projectiveCharacterReplicaHeight k)
    (energy : I → ℝ) (response : I → X →L[ℝ] ℝ)
    (T : ℝ) (x : X) :
    phaseCycledControlledWallReadout weight n k energy response T x = 0 := by
  rw [phaseCycledControlledWallReadout_eq_resolvedSignal]
  exact resolvedControlledReplicaWallSignal_eq_zero_of_lt_height
    hweight n k hlt energy response T x

/-- At the first allowed replica height, the phase-cycled scalar protocol
has positive coefficient and the exact sinc normal profile. -/
theorem phaseCycledControlledWallReadout_scaled_profile_at_height
    {I X : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {weight : I → ℝ} (hweight : ∀ i, 0 < weight i)
    (k : ProjectiveCharacter I) (energy : I → ℝ)
    (response : I → X →L[ℝ] ℝ) (x₀ v : X) (T ξ : ℝ)
    (hwall : x₀ ∈ projectiveControlRecurrenceWall energy response k)
    (hT : T ≠ 0) :
    phaseCycledControlledWallReadout weight
        (projectiveCharacterReplicaHeight k) k energy response T
        (x₀ + (ξ / T) • v) =
      (fidelityReplicaCharacterCoefficient weight
          (projectiveCharacterReplicaHeight k)
          (finiteCharacterOfProjective k) : ℂ) *
        Real.sinc (ξ * projectiveControlDetuning k response v) ∧
      0 < fidelityReplicaCharacterCoefficient weight
        (projectiveCharacterReplicaHeight k)
        (finiteCharacterOfProjective k) := by
  rw [phaseCycledControlledWallReadout_eq_resolvedSignal]
  exact resolvedControlledReplicaWallSignal_scaled_profile_at_height
    hweight k energy response x₀ v T ξ hwall hT

end

end GaloisForLFunctions.HTGeometry
