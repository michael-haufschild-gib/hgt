import GaloisForLFunctions.HTGeometry.LocalMobiusReplicaHeightLaw

/-!
# Faithful fidelity coefficients of projective spectral characters

The multiplicity condition defining replica occurrence is not merely
combinatorial.  After collecting the multinomial expansion of a survival-
fidelity moment, it is exactly the condition for the corresponding phase
character to have nonzero coefficient.  With full-support positive spectral
weights, every such coefficient is strictly positive, so cancellation cannot
hide a realizable character.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Character carried by positive and negative replica multiplicities. -/
def replicaMultiplicityCharacter
    {I : Type*} (p q : I → ℕ) : I → ℤ :=
  fun i => (p i : ℤ) - (q i : ℤ)

/-- Positive real coefficient attached to one pair of replica
multiplicities. -/
def fidelityReplicaMultiplicityWeight
    {I : Type*} [Fintype I]
    (weight : I → ℝ) (p q : I → ℕ) : ℝ :=
  (Nat.multinomial Finset.univ p : ℝ) *
    (∏ i, weight i ^ p i) *
    (Nat.multinomial Finset.univ q : ℝ) *
    (∏ i, weight i ^ q i)

/-- Coefficient of one integer phase character in the `n`th survival-
fidelity replica expansion, after collecting all positive/negative
multiplicity pairs with that character. -/
def fidelityReplicaCharacterCoefficient
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight : I → ℝ) (n : ℕ) (k : I → ℤ) : ℝ :=
  ∑ p ∈ Finset.univ.piAntidiag n,
    ∑ q ∈ Finset.univ.piAntidiag n,
      if replicaMultiplicityCharacter p q = k then
        fidelityReplicaMultiplicityWeight weight p q
      else 0

/-- Full-support positive spectral weights make every multiplicity
coefficient strictly positive. -/
theorem fidelityReplicaMultiplicityWeight_pos
    {I : Type*} [Fintype I]
    {weight : I → ℝ} (hweight : ∀ i, 0 < weight i)
    (p q : I → ℕ) :
    0 < fidelityReplicaMultiplicityWeight weight p q := by
  unfold fidelityReplicaMultiplicityWeight
  have hpMult : 0 < (Nat.multinomial Finset.univ p : ℝ) := by
    exact_mod_cast Nat.multinomial_pos (Finset.univ : Finset I) p
  have hqMult : 0 < (Nat.multinomial Finset.univ q : ℝ) := by
    exact_mod_cast Nat.multinomial_pos (Finset.univ : Finset I) q
  have hpWeight : 0 < ∏ i, weight i ^ p i := by
    exact Finset.prod_pos fun i _ => pow_pos (hweight i) _
  have hqWeight : 0 < ∏ i, weight i ^ q i := by
    exact Finset.prod_pos fun i _ => pow_pos (hweight i) _
  positivity

/-- Every collected character coefficient is nonnegative for positive
spectral weights. -/
theorem fidelityReplicaCharacterCoefficient_nonneg
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight : I → ℝ} (hweight : ∀ i, 0 < weight i)
    (n : ℕ) (k : I → ℤ) :
    0 ≤ fidelityReplicaCharacterCoefficient weight n k := by
  classical
  unfold fidelityReplicaCharacterCoefficient
  apply Finset.sum_nonneg
  intro p hp
  apply Finset.sum_nonneg
  intro q hq
  split_ifs
  · exact le_of_lt
      (fidelityReplicaMultiplicityWeight_pos hweight p q)
  · exact le_rfl

/-- **Faithful fidelity-replica occurrence law.** With full-support positive
spectral weights, a character has a strictly positive coefficient in the
`n`th survival-fidelity replica expansion exactly when it is realizable by
`n` positive and `n` negative spectral labels. -/
theorem fidelityReplicaCharacterCoefficient_pos_iff_realizes
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight : I → ℝ} (hweight : ∀ i, 0 < weight i)
    (n : ℕ) (k : I → ℤ) :
    0 < fidelityReplicaCharacterCoefficient weight n k ↔
      SpectralCharacterReplicaRealizes n k := by
  classical
  constructor
  · intro hpos
    by_contra hnot
    have hzero :
        fidelityReplicaCharacterCoefficient weight n k = 0 := by
      unfold fidelityReplicaCharacterCoefficient
      apply Finset.sum_eq_zero
      intro p hp
      apply Finset.sum_eq_zero
      intro q hq
      have hne : replicaMultiplicityCharacter p q ≠ k := by
        intro heq
        apply hnot
        refine ⟨p, q, ?_, ?_, ?_⟩
        · exact (Finset.mem_piAntidiag.mp hp).1
        · exact (Finset.mem_piAntidiag.mp hq).1
        · intro i
          simpa [replicaMultiplicityCharacter] using
            (congrFun heq i).symm
      simp [hne]
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  · rintro ⟨p, q, hp, hq, hk⟩
    have hpmem : p ∈ Finset.univ.piAntidiag n := by
      rw [Finset.mem_piAntidiag]
      exact ⟨hp, fun i hi => Finset.mem_univ i⟩
    have hqmem : q ∈ Finset.univ.piAntidiag n := by
      rw [Finset.mem_piAntidiag]
      exact ⟨hq, fun i hi => Finset.mem_univ i⟩
    unfold fidelityReplicaCharacterCoefficient
    apply Finset.sum_pos'
    · intro p' hp'
      apply Finset.sum_nonneg
      intro q' hq'
      split_ifs
      · exact le_of_lt
          (fidelityReplicaMultiplicityWeight_pos hweight p' q')
      · exact le_rfl
    · refine ⟨p, hpmem, ?_⟩
      apply Finset.sum_pos'
      · intro q' hq'
        split_ifs
        · exact le_of_lt
            (fidelityReplicaMultiplicityWeight_pos hweight p q')
        · exact le_rfl
      · refine ⟨q, hqmem, ?_⟩
        rw [if_pos]
        · exact fidelityReplicaMultiplicityWeight_pos hweight p q
        · funext i
          simpa [replicaMultiplicityCharacter] using (hk i).symm

/-- Exact character threshold in an actual full-support fidelity moment. -/
theorem fidelityReplicaCharacterCoefficient_pos_iff_positiveMass_le
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {weight : I → ℝ} (hweight : ∀ i, 0 < weight i)
    {k : I → ℤ} (hbalanced : SpectralCharacterBalanced k)
    (n : ℕ) :
    0 < fidelityReplicaCharacterCoefficient weight n k ↔
      spectralCharacterPositiveMass k ≤ n := by
  rw [fidelityReplicaCharacterCoefficient_pos_iff_realizes hweight]
  constructor
  · exact spectralCharacterPositiveMass_le_of_replicaRealizes
  · exact fun hmass =>
      spectralCharacterReplicaRealizes_of_balanced_of_positiveMass_le
        hbalanced hmass

/-- Bivariate multinomial expansion underlying the coefficient law.
Substituting opposite phase variables gives the `n`th power of survival
fidelity, and `replicaMultiplicityCharacter p q` is its phase character. -/
theorem complexFidelityReplicaMultiplicityExpansion
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight : I → ℝ) (positivePhase negativePhase : I → ℂ)
    (n : ℕ) :
    ((∑ i, (weight i : ℂ) * positivePhase i) ^ n) *
        ((∑ i, (weight i : ℂ) * negativePhase i) ^ n) =
      ∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
            (∏ i, positivePhase i ^ p i) *
            (∏ i, negativePhase i ^ q i) := by
  classical
  rw [Finset.sum_pow_eq_sum_piAntidiag,
    Finset.sum_pow_eq_sum_piAntidiag, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  simp_rw [mul_pow, Finset.prod_mul_distrib]
  unfold fidelityReplicaMultiplicityWeight
  push_cast
  ring

end

end GaloisForLFunctions.HTGeometry
