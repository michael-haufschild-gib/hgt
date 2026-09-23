import GaloisForLFunctions.RHTower.CountableSpectralRelationMetricEntropyLaw
import GaloisForLFunctions.HTGeometry.ValuatedSpectralCharacterLaw

/-!
# Projective relation-metric entropy for countable quantum recurrence

Quantum recurrence is invariant under a common energy shift. For every
countable pure-point spectrum, anchoring all frequencies at one level
removes exactly this global phase. Every finite-support relation of the
anchored packet is then exactly a balanced projective relation of the
original energy spectrum.

The anchored relation lattice determines the exact compact projective orbit
hull. Spectral weights pull Hilbert distance back to that hull, and its
minimal finite cover bounds the actual first survival-coherence return.
Thus the relation--metric recurrence law is projective, countably infinite,
and independent of ambient Hilbert dimension.
-/

open scoped BigOperators InnerProductSpace
open Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Countable energy gaps relative to the zeroth reference level. -/
def anchoredCountableFrequency (omega : ℕ → ℝ) : ℕ → ℝ :=
  fun k => omega k - omega 0

/-- Remove the common phase of a countable torus point. -/
def projectivizeCountablePhase
    (x : ℕ → UnitAddCircle) : ℕ → UnitAddCircle :=
  fun k => x k - x 0

/-- Projectivizing a spectral screw line is exactly anchoring its frequency
packet. -/
theorem projectivizeCountablePhase_screwPhase
    (omega : ℕ → ℝ) (t : ℝ) :
    projectivizeCountablePhase (screwPhase omega t) =
      screwPhase (anchoredCountableFrequency omega) t := by
  funext k
  change
    ((omega k * t / (2 * Real.pi) : ℝ) : UnitAddCircle) -
        ((omega 0 * t / (2 * Real.pi) : ℝ) : UnitAddCircle) =
      (((omega k - omega 0) * t / (2 * Real.pi) : ℝ) :
        UnitAddCircle)
  rw [← QuotientAddGroup.mk_sub]
  congr 1
  ring

/-- Convert an arbitrary finite-support integer character into the balanced
projective character obtained by moving its total charge to the anchor. -/
def balanceCountableCharacterAtZero
    (n : ℕ →₀ ℤ) : ProjectiveCharacter ℕ := by
  refine ⟨n - Finsupp.single 0 (integerCharacterCharge ℕ n), ?_⟩
  change integerCharacterCharge ℕ
      (n - Finsupp.single 0 (integerCharacterCharge ℕ n)) = 0
  rw [map_sub]
  simp [integerCharacterCharge]

/-- Balancing fixes every already-projective character. -/
theorem balanceCountableCharacterAtZero_projective
    (k : ProjectiveCharacter ℕ) :
    (balanceCountableCharacterAtZero k.1).1 = k.1 := by
  change
    k.1 - Finsupp.single 0 (integerCharacterCharge ℕ k.1) = k.1
  rw [show integerCharacterCharge ℕ k.1 = 0 from k.property]
  simp

/-- Anchored detuning is exactly original-energy detuning of the associated
balanced projective character. -/
theorem infiniteTorusCharacterDetuning_anchored
    (n : ℕ →₀ ℤ) (omega : ℕ → ℝ) :
    infiniteTorusCharacterDetuning n
        (anchoredCountableFrequency omega) =
      infiniteTorusCharacterDetuning
        (balanceCountableCharacterAtZero n) omega := by
  classical
  unfold infiniteTorusCharacterDetuning anchoredCountableFrequency
  change
    n.sum (fun i m => (m : ℝ) * (omega i - omega 0)) =
      (n - Finsupp.single 0 (integerCharacterCharge ℕ n)).sum
        (fun i m => (m : ℝ) * omega i)
  rw [Finsupp.sum_sub_index]
  · rw [Finsupp.sum_single_index]
    · have hcharge :
          ((integerCharacterCharge ℕ n : ℤ) : ℝ) =
            n.sum (fun _ m => (m : ℝ)) := by
          change ((n.sum fun _ m => m : ℤ) : ℝ) =
            n.sum (fun _ m => (m : ℝ))
          simp only [Finsupp.sum]
          push_cast
          rfl
      rw [hcharge]
      simp only [Finsupp.sum]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, Finset.sum_mul]
    · norm_num
  · intro i b₁ b₂
    push_cast
    ring

/-- The complete relation lattice of anchored countable frequencies is
precisely the original spectrum's balanced projective relation lattice,
written in anchored coordinates. -/
theorem mem_anchoredScrewRelationLattice_iff_balancedRelation
    (n : ℕ →₀ ℤ) (omega : ℕ → ℝ) :
    n ∈ screwRelationLattice (anchoredCountableFrequency omega) ↔
      infiniteTorusCharacterDetuning
        (balanceCountableCharacterAtZero n) omega = 0 := by
  change
    infiniteTorusCharacterDetuning n
        (anchoredCountableFrequency omega) = 0 ↔
      infiniteTorusCharacterDetuning
        (balanceCountableCharacterAtZero n) omega = 0
  rw [infiniteTorusCharacterDetuning_anchored]

/-- Removing a common phase leaves every countable weighted survival
amplitude norm unchanged. -/
theorem norm_summableWeightedPhaseAmplitude_projectivize
    (p : ℕ → ℝ) (x : ℕ → UnitAddCircle) (n : ℤ) :
    ‖RHTower.summableWeightedPhaseAmplitude p (fun k =>
        fourier 1 (n • projectivizeCountablePhase x k))‖ =
      ‖RHTower.summableWeightedPhaseAmplitude p (fun k =>
        fourier 1 (n • x k))‖ := by
  have hterm (k : ℕ) :
      fourier 1 (n • projectivizeCountablePhase x k) =
        fourier 1 (-(n • x 0)) * fourier 1 (n • x k) := by
    simp [projectivizeCountablePhase, sub_eq_add_neg,
      AddCircle.toCircle_add]
    ring
  unfold RHTower.summableWeightedPhaseAmplitude
  simp_rw [hterm]
  have hfactor :
      (∑' k : ℕ,
          (p k : ℂ) *
            (fourier 1 (-(n • x 0)) * fourier 1 (n • x k))) =
        fourier 1 (-(n • x 0)) *
          ∑' k : ℕ, (p k : ℂ) * fourier 1 (n • x k) := by
    calc
      _ = ∑' k : ℕ,
          fourier 1 (-(n • x 0)) *
            ((p k : ℂ) * fourier 1 (n • x k)) := by
              apply tsum_congr
              intro k
              ring
      _ = _ := tsum_mul_left
  rw [hfactor, norm_mul]
  have hunit : ‖fourier 1 (-(n • x 0))‖ = 1 := by
    rw [fourier_apply]
    exact Circle.norm_coe _
  rw [hunit, one_mul]

/-- Positive-clock survival coherence is exactly projective. -/
theorem countableTorusWeightedCoherenceAt_projectivize_iff
    (p : ℕ → ℝ) (x : ℕ → UnitAddCircle) (η : ℝ) (n : ℕ) :
    RHTower.CountableTorusWeightedCoherenceAt p
        (projectivizeCountablePhase x) η n ↔
      RHTower.CountableTorusWeightedCoherenceAt p x η n := by
  unfold RHTower.CountableTorusWeightedCoherenceAt
  rw [norm_summableWeightedPhaseAmplitude_projectivize]

/-- Actual first survival-coherence time is invariant under removal of
common phase. -/
theorem countableTorusWeightedFirstCoherenceTime_projectivize
    (p : ℕ → ℝ) (x : ℕ → UnitAddCircle) (η : ℝ) :
    RHTower.countableTorusWeightedFirstCoherenceTime p
        (projectivizeCountablePhase x) η =
      RHTower.countableTorusWeightedFirstCoherenceTime p x η := by
  classical
  have hiff (n : ℕ) :
      RHTower.CountableTorusWeightedCoherenceAt p
          (projectivizeCountablePhase x) η n ↔
        RHTower.CountableTorusWeightedCoherenceAt p x η n :=
    countableTorusWeightedCoherenceAt_projectivize_iff p x η n
  have hexists :
      (∃ n, RHTower.CountableTorusWeightedCoherenceAt p
          (projectivizeCountablePhase x) η n) ↔
        ∃ n, RHTower.CountableTorusWeightedCoherenceAt p x η n :=
    exists_congr hiff
  unfold RHTower.countableTorusWeightedFirstCoherenceTime
  by_cases hx :
      ∃ n, RHTower.CountableTorusWeightedCoherenceAt p x η n
  · have hp :
        ∃ n, RHTower.CountableTorusWeightedCoherenceAt p
          (projectivizeCountablePhase x) η n :=
      hexists.mpr hx
    rw [dif_pos hx, dif_pos hp]
    congr 1
    apply le_antisymm
    · exact Nat.find_min' hp
        ((hiff (Nat.find hx)).mpr (Nat.find_spec hx))
    · exact Nat.find_min' hx
        ((hiff (Nat.find hp)).mp (Nat.find_spec hp))
  · have hp :
        ¬ ∃ n, RHTower.CountableTorusWeightedCoherenceAt p
          (projectivizeCountablePhase x) η n := by
      exact fun h => hx (hexists.mp h)
    rw [dif_neg hx, dif_neg hp]

/-- Anchoring the spectral packet leaves actual first survival recurrence
unchanged. -/
theorem countableSpectralFirstCoherenceTime_anchored
    (p : ℕ → ℝ) (omega : ℕ → ℝ) (η : ℝ) :
    RHTower.countableTorusWeightedFirstCoherenceTime p
        (screwPhase (anchoredCountableFrequency omega) 1) η =
      RHTower.countableTorusWeightedFirstCoherenceTime p
        (screwPhase omega 1) η := by
  rw [← projectivizeCountablePhase_screwPhase]
  exact
    countableTorusWeightedFirstCoherenceTime_projectivize
      p (screwPhase omega 1) η

end GaloisForLFunctions.HTGeometry

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Minimal weighted cover cardinality of the exact projective relation
hull, after removing the physically irrelevant common energy phase. -/
noncomputable def countableSpectralProjectiveRelationHullCoveringNumber
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : Summable p)
    (omega : ℕ → ℝ) (r : ℝ) : ℕ :=
  countableSpectralRelationHullCoveringNumber
    p hp hsum (anchoredCountableFrequency omega) r

/-- **Countably infinite projective relation-metric entropy law.** For
every normalized countable pure-point spectral packet and every positive
resolution, actual first survival recurrence is no later than the minimal
weighted covering number of the exact projective relation hull. -/
theorem
    countableSpectralFirstCoherenceTime_le_projectiveRelationHullCoveringNumber
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (omega : ℕ → ℝ) {r : ℝ} (hr : 0 < r) :
    countableTorusWeightedFirstCoherenceTime p
        (screwPhase omega 1) (2 * r ^ (2 : ℕ)) ≤
      countableSpectralProjectiveRelationHullCoveringNumber
        p hp hsum omega r := by
  rw [countableSpectralProjectiveRelationHullCoveringNumber,
    ← countableSpectralFirstCoherenceTime_anchored]
  exact
    countableSpectralFirstCoherenceTime_le_relationHullCoveringNumber
      p hp hsum htotal (anchoredCountableFrequency omega) hr

/-- Relation-lattice form of the projective countable return law. The
covering carrier is the exact annihilator of all finite relations among
anchored energy gaps. -/
theorem exists_countableSpectralProjectiveRelationLatticeFirstReturnBound
    (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k)
    (hsum : Summable p) (htotal : ∑' k, p k = 1)
    (omega : ℕ → ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ C : Finset CountableSpectralPhaseSpace,
      (∀ z ∈ screwAnnihilator (anchoredCountableFrequency omega),
        ∃ c ∈ C,
          ‖countableSpectralPhaseState p hp hsum z - c‖ ≤ r) ∧
      countableTorusWeightedFirstCoherenceTime p
          (screwPhase omega 1) (2 * r ^ (2 : ℕ)) ≤ C.card := by
  obtain ⟨C, hcover, htime⟩ :=
    exists_countableSpectralRelationLatticeFirstReturnBound
      p hp hsum htotal (anchoredCountableFrequency omega) hr
  refine ⟨C, hcover, ?_⟩
  rw [← countableSpectralFirstCoherenceTime_anchored]
  exact htime

end RHTower
