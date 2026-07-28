import GaloisForLFunctions.RHTower.EndpointKrylovNearestNeighborRealization
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum

open scoped BigOperators InnerProductSpace
open Complex

noncomputable section

namespace RHTower.ParityForecast

/-- Computational basis of `n` qubits, indexed by occupied sites. -/
abbrev QubitOccupationSpace (n : ℕ) :=
  FiniteIndexClockSpace (Finset (Fin n))

/-- Hamming weight as an index in the symmetric energy ladder. -/
def occupationCardIndex (n : ℕ) (S : Finset (Fin n)) : Fin (n + 1) :=
  ⟨S.card, by
    have h := Finset.card_le_univ S
    simpa using Nat.lt_succ_of_le h⟩

@[simp] theorem occupationCardIndex_val
    (n : ℕ) (S : Finset (Fin n)) :
    (occupationCardIndex n S : ℕ) = S.card := rfl

/--
Distribute one spectral weight uniformly over all computational states in
the corresponding Hamming-weight shell.
-/
def symmetricOccupationWeight
    (n : ℕ) (weight : Fin (n + 1) → ℝ)
    (S : Finset (Fin n)) : ℝ :=
  weight (occupationCardIndex n S) /
    Nat.choose n S.card

def symmetricShellWeight
    (n : ℕ) (weight : Fin (n + 1) → ℝ) (m : ℕ) : ℝ :=
  if h : m < n + 1 then weight ⟨m, h⟩ / Nat.choose n m else 0

theorem symmetricOccupationWeight_eq_shell
    (n : ℕ) (weight : Fin (n + 1) → ℝ)
    (S : Finset (Fin n)) :
    symmetricOccupationWeight n weight S =
      symmetricShellWeight n weight S.card := by
  have hcard : S.card < n + 1 := by
    apply Nat.lt_succ_of_le
    simpa using Finset.card_le_univ S
  simp [symmetricOccupationWeight, symmetricShellWeight,
    hcard, occupationCardIndex]

theorem symmetricOccupationWeight_nonneg
    (n : ℕ) {weight : Fin (n + 1) → ℝ}
    (hweight : ∀ j, 0 ≤ weight j)
    (S : Finset (Fin n)) :
    0 ≤ symmetricOccupationWeight n weight S := by
  exact div_nonneg (hweight _) (Nat.cast_nonneg _)

theorem symmetricOccupationWeight_permutation_invariant
    (n : ℕ) (weight : Fin (n + 1) → ℝ)
    (e : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    symmetricOccupationWeight n weight (S.map e.toEmbedding) =
      symmetricOccupationWeight n weight S := by
  simp [symmetricOccupationWeight, occupationCardIndex]

theorem symmetricOccupationWeight_sum
    (n : ℕ) (weight : Fin (n + 1) → ℝ) :
    ∑ S : Finset (Fin n), symmetricOccupationWeight n weight S =
      ∑ j : Fin (n + 1), weight j := by
  rw [← Finset.powerset_univ]
  rw [show
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        symmetricOccupationWeight n weight S) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        symmetricShellWeight n weight S.card by
    apply Finset.sum_congr rfl
    intro S _hS
    exact symmetricOccupationWeight_eq_shell n weight S]
  rw [Finset.sum_powerset_apply_card]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => Nat.choose n j •
      symmetricShellWeight n weight j) (n + 1)]
  apply Finset.sum_congr rfl
  intro j _hj
  have hj : (j : ℕ) < n + 1 := j.isLt
  simp only [nsmul_eq_mul]
  change
    (Nat.choose n (j : ℕ) : ℝ) *
        symmetricShellWeight n weight (j : ℕ) =
      weight j
  rw [symmetricShellWeight, dif_pos hj]
  have hchoose : (Nat.choose n (j : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  field_simp

/-- Symmetric pure `n`-qubit state with prescribed energy-shell weights. -/
def symmetricOccupationKet
    (n : ℕ) (weight : Fin (n + 1) → ℝ) :
    QubitOccupationSpace n :=
  finiteIndexWeightKet (symmetricOccupationWeight n weight)

theorem symmetricOccupationKet_permutation_invariant
    (n : ℕ) (weight : Fin (n + 1) → ℝ)
    (e : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    symmetricOccupationKet n weight (S.map e.toEmbedding) =
      symmetricOccupationKet n weight S := by
  simp [symmetricOccupationKet,
    symmetricOccupationWeight_permutation_invariant]

@[simp] theorem symmetricOccupationKet_norm
    {n : ℕ} {weight : Fin (n + 1) → ℝ}
    (hweight : ∀ j, 0 ≤ weight j)
    (hweightSum : ∑ j, weight j = 1) :
    ‖symmetricOccupationKet n weight‖ = 1 := by
  apply finiteIndexWeightKet_norm_eq_one
    (symmetricOccupationWeight n weight)
    (symmetricOccupationWeight_nonneg n hweight)
  rw [symmetricOccupationWeight_sum, hweightSum]

/-- Uniform onsite field: energy depends only on excitation number. -/
def uniformQubitFieldEnergy
    (T : ℝ) (n : ℕ) (S : Finset (Fin n)) : ℝ :=
  Real.pi * S.card / T

/-- Uniform-field Hamiltonian on the full `2^n`-dimensional qubit space. -/
def uniformQubitFieldHamiltonian
    (T : ℝ) (n : ℕ) :
    QubitOccupationSpace n →L[ℂ] QubitOccupationSpace n :=
  finiteIndexDiagonalHamiltonian (uniformQubitFieldEnergy T n)

theorem uniformQubitFieldHamiltonian_selfAdjoint
    (T : ℝ) (n : ℕ) :
    ContinuousLinearMap.adjoint
        (uniformQubitFieldHamiltonian T n) =
      uniformQubitFieldHamiltonian T n :=
  finiteIndexDiagonalHamiltonian_selfAdjoint _

theorem uniformQubitFieldEnergy_eq_sum_onsite
    (T : ℝ) (n : ℕ) (S : Finset (Fin n)) :
    uniformQubitFieldEnergy T n S =
      ∑ _i ∈ S, Real.pi / T := by
  simp [uniformQubitFieldEnergy, Finset.sum_const,
    nsmul_eq_mul]
  ring

theorem uniformQubitFieldEnergy_permutation_invariant
    (T : ℝ) (n : ℕ) (e : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) :
    uniformQubitFieldEnergy T n (S.map e.toEmbedding) =
      uniformQubitFieldEnergy T n S := by
  simp [uniformQubitFieldEnergy]

theorem uniformQubitFieldEnergy_eq_angular
    (T : ℝ) (n : ℕ) (S : Finset (Fin n)) :
    uniformQubitFieldEnergy T n S =
      angularEnergy T n (occupationCardIndex n S) := by
  rw [uniformQubitFieldEnergy, angularEnergy_eq]
  rfl

theorem uniformQubitFieldEnergy_nonneg
    {T : ℝ} (hT : 0 < T) (n : ℕ) (S : Finset (Fin n)) :
    0 ≤ uniformQubitFieldEnergy T n S := by
  exact div_nonneg
    (mul_nonneg Real.pi_pos.le (Nat.cast_nonneg _)) hT.le

/-- Uniform-field evolution phase of a computational occupation. -/
def uniformQubitFieldPhase
    (T t : ℝ) (n : ℕ) (S : Finset (Fin n)) : ℂ :=
  Complex.exp
    (((uniformQubitFieldEnergy T n S * t : ℝ) : ℂ) * I)

def symmetricOccupationKetAt
    (T : ℝ) (n : ℕ) (weight : Fin (n + 1) → ℝ)
    (t : ℝ) : QubitOccupationSpace n :=
  finiteIndexPhasedWeightKet
    (symmetricOccupationWeight n weight)
    (uniformQubitFieldPhase T t n)

def symmetricShellWeightedPhase
    (T t : ℝ) (n : ℕ) (weight : Fin (n + 1) → ℝ)
    (m : ℕ) : ℂ :=
  if h : m < n + 1 then
    ((weight ⟨m, h⟩ : ℂ) / Nat.choose n m) *
      Complex.exp
        ((((Real.pi * m / T) * t : ℝ) : ℂ) * I)
  else 0

theorem symmetricOccupation_weighted_phase_sum
    (T : ℝ) (n : ℕ) (weight : Fin (n + 1) → ℝ)
    (t : ℝ) :
    ∑ S : Finset (Fin n),
        (symmetricOccupationWeight n weight S : ℂ) *
          uniformQubitFieldPhase T t n S =
      ∑ j : Fin (n + 1),
        (weight j : ℂ) * scaledPhase T n t j := by
  rw [← Finset.powerset_univ]
  rw [show
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        (symmetricOccupationWeight n weight S : ℂ) *
          uniformQubitFieldPhase T t n S) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        symmetricShellWeightedPhase T t n weight S.card by
    apply Finset.sum_congr rfl
    intro S _hS
    have hcard : S.card < n + 1 :=
      Nat.lt_succ_of_le (by
        simpa using Finset.card_le_univ S)
    rw [symmetricOccupationWeight_eq_shell]
    simp [symmetricShellWeight, symmetricShellWeightedPhase,
      hcard, uniformQubitFieldPhase, uniformQubitFieldEnergy]]
  rw [Finset.sum_powerset_apply_card]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => Nat.choose n j •
      symmetricShellWeightedPhase T t n weight j) (n + 1)]
  apply Finset.sum_congr rfl
  intro j _hj
  have hj : (j : ℕ) < n + 1 := j.isLt
  simp only [nsmul_eq_mul]
  change
    (Nat.choose n (j : ℕ) : ℂ) *
        symmetricShellWeightedPhase T t n weight (j : ℕ) =
      (weight j : ℂ) * scaledPhase T n t j
  rw [symmetricShellWeightedPhase, dif_pos hj]
  have hchoose : (Nat.choose n (j : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  rw [show scaledPhase T n t j =
      Complex.exp
        ((((Real.pi * (j : ℕ) / T) * t : ℝ) : ℂ) * I) by
    rw [scaledPhase_eq_angular, angularEnergy_eq]]
  field_simp

theorem symmetricOccupationKet_survivalAmplitude
    (T : ℝ) (n : ℕ) {weight : Fin (n + 1) → ℝ}
    (hweight : ∀ j, 0 ≤ weight j) (t : ℝ) :
    inner ℂ (symmetricOccupationKet n weight)
        (symmetricOccupationKetAt T n weight t) =
      ∑ j : Fin (n + 1),
        (weight j : ℂ) * scaledPhase T n t j := by
  rw [symmetricOccupationKet, symmetricOccupationKetAt,
    finiteIndexWeightKet_inner_phasedWeightKet
      _ _ (symmetricOccupationWeight_nonneg n hweight)]
  exact symmetricOccupation_weighted_phase_sum T n weight t

@[simp] theorem symmetricOccupationKetAt_norm
    {T : ℝ} {n : ℕ}
    {weight : Fin (n + 1) → ℝ}
    (hweight : ∀ j, 0 ≤ weight j)
    (hweightSum : ∑ j, weight j = 1) (t : ℝ) :
    ‖symmetricOccupationKetAt T n weight t‖ = 1 := by
  have hphase :
      ∀ S : Finset (Fin n),
        ‖uniformQubitFieldPhase T t n S‖ = 1 := by
    intro S
    rw [uniformQubitFieldPhase, Complex.norm_exp]
    simp [Complex.mul_re]
  have hsq :=
    finiteIndexPhasedWeightKet_norm_sq
      (symmetricOccupationWeight n weight)
      (uniformQubitFieldPhase T t n)
      (symmetricOccupationWeight_nonneg n hweight)
      hphase
  rw [symmetricOccupationWeight_sum, hweightSum] at hsq
  change
    ‖finiteIndexPhasedWeightKet
      (symmetricOccupationWeight n weight)
      (uniformQubitFieldPhase T t n)‖ = 1
  nlinarith
    [norm_nonneg
      (finiteIndexPhasedWeightKet
        (symmetricOccupationWeight n weight)
        (uniformQubitFieldPhase T t n))]

theorem symmetricOccupation_weighted_energyMoment
    (T : ℝ) (n k : ℕ) (weight : Fin (n + 1) → ℝ) :
    ∑ S : Finset (Fin n),
        symmetricOccupationWeight n weight S *
          uniformQubitFieldEnergy T n S ^ k =
      ∑ j : Fin (n + 1),
        weight j * angularEnergy T n j ^ k := by
  rw [show
      (∑ S : Finset (Fin n),
        symmetricOccupationWeight n weight S *
          uniformQubitFieldEnergy T n S ^ k) =
      ∑ S : Finset (Fin n),
        symmetricOccupationWeight n
          (fun j => weight j * angularEnergy T n j ^ k) S by
    apply Finset.sum_congr rfl
    intro S _hS
    rw [symmetricOccupationWeight,
      symmetricOccupationWeight, uniformQubitFieldEnergy_eq_angular]
    ring]
  exact symmetricOccupationWeight_sum n
    (fun j => weight j * angularEnergy T n j ^ k)

theorem symmetricOccupationKet_energyMoment
    (T : ℝ) (n k : ℕ) {weight : Fin (n + 1) → ℝ}
    (hweight : ∀ j, 0 ≤ weight j) :
    inner ℂ (symmetricOccupationKet n weight)
        (((uniformQubitFieldHamiltonian T n) ^ k)
          (symmetricOccupationKet n weight)) =
      (∑ j : Fin (n + 1),
        weight j * angularEnergy T n j ^ k : ℝ) := by
  rw [symmetricOccupationKet,
    uniformQubitFieldHamiltonian,
    finiteIndexWeightKet_diagonal_moment
      (uniformQubitFieldEnergy T n)
      (symmetricOccupationWeight n weight)
      (symmetricOccupationWeight_nonneg n hweight) k]
  exact_mod_cast
    symmetricOccupation_weighted_energyMoment T n k weight

theorem symmetricInterpolatedQubit_survivalAmplitude
    {T : ℝ} (hT : 0 < T) (n : ℕ) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (t : ℝ) :
    inner ℂ
        (symmetricOccupationKet n (interpolatedWeight n θ))
        (symmetricOccupationKetAt
          T n (interpolatedWeight n θ) t) =
      scaledInterpolatedAmplitude T n θ t := by
  rw [symmetricOccupationKet_survivalAmplitude
    T n (interpolatedWeight_nonneg n hθ0 hθ1) t]
  rw [scaledInterpolatedAmplitude, ←
    interpolated_weighted_phase_sum n θ (t / T)]
  apply Finset.sum_congr rfl
  intro j _hj
  congr 1
  rw [scaledPhase_eq_angular, angularEnergy_eq,
    halfLatticePhase, halfLatticeEnergy]
  congr 1
  push_cast
  field_simp [hT.ne']

/-- Return probability of the symmetric qubit preparation in one uniform field. -/
def symmetricInterpolatedQubitProbability
    (T : ℝ) (n : ℕ) (θ t : ℝ) : ℝ :=
  ‖inner ℂ
      (symmetricOccupationKet n (interpolatedWeight n θ))
      (symmetricOccupationKetAt
        T n (interpolatedWeight n θ) t)‖ ^ 2

theorem symmetricInterpolatedQubitProbability_eq
    {T : ℝ} (hT : 0 < T) {n : ℕ}
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (t : ℝ) :
    symmetricInterpolatedQubitProbability T n θ t =
      scaledInterpolatedProbability T n θ t := by
  rw [symmetricInterpolatedQubitProbability,
    symmetricInterpolatedQubit_survivalAmplitude
      hT n hθ0 hθ1 t]
  rfl

/--
One permutation-invariant noninteracting `n`-qubit Hamiltonian supports
pure symmetric preparations with every terminal return probability in
`[0,1]`, common finite moments, and a common arbitrarily accurate earlier
return record.
-/
theorem one_uniform_qubit_field_every_future_probability
    (m : ℕ) (T H : ℝ) (hT : 0 < T) (hH0 : 0 ≤ H)
    (hHT : H < T) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ,
      m < n ∧
      ContinuousLinearMap.adjoint
          (uniformQubitFieldHamiltonian T n) =
        uniformQubitFieldHamiltonian T n ∧
      (∀ e : Equiv.Perm (Fin n), ∀ S : Finset (Fin n),
        uniformQubitFieldEnergy T n (S.map e.toEmbedding) =
          uniformQubitFieldEnergy T n S) ∧
      ∀ p : ℝ, p ∈ Set.Icc (0 : ℝ) 1 →
        (∀ e : Equiv.Perm (Fin n), ∀ S : Finset (Fin n),
          symmetricOccupationKet n
              (interpolatedWeight n (Real.sqrt p))
              (S.map e.toEmbedding) =
            symmetricOccupationKet n
              (interpolatedWeight n (Real.sqrt p)) S) ∧
        ‖symmetricOccupationKet n
            (interpolatedWeight n (Real.sqrt p))‖ = 1 ∧
        (∀ t : ℝ,
          ‖symmetricOccupationKetAt
              T n (interpolatedWeight n (Real.sqrt p)) t‖ = 1) ∧
        (∀ k : ℕ, k ≤ m →
          inner ℂ
              (symmetricOccupationKet n
                (interpolatedWeight n (Real.sqrt p)))
              (((uniformQubitFieldHamiltonian T n) ^ k)
                (symmetricOccupationKet n
                  (interpolatedWeight n (Real.sqrt p)))) =
            (∑ j : Fin (n + 1),
              fullWeight n j * angularEnergy T n j ^ k : ℝ)) ∧
        (∀ t : ℝ, |t| ≤ H →
          |symmetricInterpolatedQubitProbability
              T n (Real.sqrt p) t -
            scaledFullProbability T n t| < δ) ∧
        symmetricInterpolatedQubitProbability
            T n (Real.sqrt p) T = p := by
  obtain ⟨n, hmn, hall⟩ :=
    one_record_compatible_with_every_future_probability
      m T H hT hH0 hHT hδ
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le m) hmn
  refine ⟨n, hmn,
    uniformQubitFieldHamiltonian_selfAdjoint T n,
    uniformQubitFieldEnergy_permutation_invariant T n, ?_⟩
  intro p hp
  obtain ⟨_hmom, hwindow, htarget⟩ := hall p hp
  have hθ0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have hθ1 : Real.sqrt p ≤ 1 := Real.sqrt_le_one.mpr hp.2
  refine ⟨symmetricOccupationKet_permutation_invariant
      n (interpolatedWeight n (Real.sqrt p)),
    symmetricOccupationKet_norm
      (interpolatedWeight_nonneg n hθ0 hθ1)
      (interpolatedWeight_sum hn (Real.sqrt p)),
    ?_, ?_, ?_, ?_⟩
  · intro t
    exact symmetricOccupationKetAt_norm
      (interpolatedWeight_nonneg n hθ0 hθ1)
      (interpolatedWeight_sum hn (Real.sqrt p)) t
  · intro k hk
    rw [symmetricOccupationKet_energyMoment
      T n k (interpolatedWeight_nonneg n hθ0 hθ1)]
    exact_mod_cast angular_interpolated_energyMoment_eq_full
      (lt_of_le_of_lt hk hmn) (Real.sqrt p)
  · intro t ht
    rw [symmetricInterpolatedQubitProbability_eq
      hT hθ0 hθ1 t]
    exact hwindow t ht
  · rw [symmetricInterpolatedQubitProbability_eq
      hT hθ0 hθ1 T]
    exact htarget

end RHTower.ParityForecast
