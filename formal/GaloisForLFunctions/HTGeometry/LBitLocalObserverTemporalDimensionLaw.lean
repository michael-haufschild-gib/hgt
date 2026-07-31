import GaloisForLFunctions.HTGeometry.LBitTemporalDimensionLaw
import GaloisForLFunctions.HTGeometry.RationalIndependentWeights

/-!
# Temporal dimension of one localized l-bit flip

A distinguished diagonal two-level degree of freedom has one conditional
flip frequency for every configuration of its environment.  The packet of
those frequencies is the Walsh transform of exactly the interaction
coefficients incident on that degree of freedom.

This file proves that the rational span, and hence the temporal dimension, of
the local flip-frequency packet is exactly the rational span of the incident
coefficients.  A noninteracting local flip has dimension at most one, while
one exactly localized flip can have the full `2 ^ |I|` temporal dimension
when its environment-dependent interaction coefficients are rationally
independent.
-/

open Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

noncomputable local instance lbitLocalObserverFintypeForallBool
    {I : Type*} [Fintype I] :
    Fintype (I → Bool) :=
  Fintype.ofFinite _

/-- Conditional frequency of flipping one distinguished l-bit.  The
coefficient indexed by `S` is the interaction between the distinguished
l-bit and the environment support `S`; `S = ∅` is its one-body field. -/
def lbitLocalFlipFrequency
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) (x : I → Bool) : ℝ :=
  (2 : ℚ) • lbitEnergy J x

/-- Rational span of every interaction coefficient incident on the
distinguished l-bit. -/
def lbitIncidentCoefficientSubspace
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) : Submodule ℚ ℝ :=
  Submodule.span ℚ (Set.range J)

/-- Rational span of the distinguished l-bit's complete conditional
flip-frequency packet. -/
def lbitLocalFlipFrequencySubspace
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) : Submodule ℚ ℝ :=
  Submodule.span ℚ (Set.range (lbitLocalFlipFrequency J))

/-- Partial Walsh inversion: each incident coefficient is recovered from the
local flip-frequency packet. -/
theorem lbitLocalFlipFrequency_walshCoefficient
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) (S : Finset I) :
    (∑ x : I → Bool,
      lbitWalshCharacter S x • lbitLocalFlipFrequency J x) =
      ((2 : ℚ) ^ (Fintype.card I + 1)) • J S := by
  classical
  calc
    (∑ x : I → Bool,
        lbitWalshCharacter S x • lbitLocalFlipFrequency J x) =
        (2 : ℚ) •
          (∑ x : I → Bool,
            lbitWalshCharacter S x • lbitEnergy J x) := by
              simp_rw [lbitLocalFlipFrequency, smul_smul]
              rw [Finset.smul_sum]
              apply Finset.sum_congr rfl
              intro x hx
              simpa [mul_comm] using
                mul_smul (2 : ℚ)
                  (lbitWalshCharacter S x) (lbitEnergy J x)
    _ = (2 : ℚ) • (((2 : ℚ) ^ Fintype.card I) • J S) := by
      rw [lbitEnergy_walshCoefficient]
    _ = ((2 : ℚ) ^ (Fintype.card I + 1)) • J S := by
      rw [smul_smul, pow_succ]
      congr 1
      ring

theorem lbitLocalFlipFrequencySubspace_le_incident
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) :
    lbitLocalFlipFrequencySubspace J ≤
      lbitIncidentCoefficientSubspace J := by
  apply Submodule.span_le.2
  rintro z ⟨x, rfl⟩
  unfold lbitLocalFlipFrequency lbitEnergy
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro S hS
  exact Submodule.smul_mem _
    (lbitWalshCharacter S x)
    (Submodule.subset_span (Set.mem_range_self S))

theorem lbitIncidentCoefficientSubspace_le_localFlip
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) :
    lbitIncidentCoefficientSubspace J ≤
      lbitLocalFlipFrequencySubspace J := by
  apply Submodule.span_le.2
  rintro z ⟨S, rfl⟩
  have hcoefficient :=
    lbitLocalFlipFrequency_walshCoefficient J S
  have htwo : (2 : ℚ) ^ (Fintype.card I + 1) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have hsum :
      (∑ x : I → Bool,
        lbitWalshCharacter S x • lbitLocalFlipFrequency J x) ∈
          lbitLocalFlipFrequencySubspace J := by
    apply Submodule.sum_mem
    intro x hx
    exact Submodule.smul_mem _
      (lbitWalshCharacter S x)
      (Submodule.subset_span ⟨x, rfl⟩)
  have hinv :=
    Submodule.smul_mem
      (lbitLocalFlipFrequencySubspace J)
      (((2 : ℚ) ^ (Fintype.card I + 1))⁻¹)
      hsum
  rw [hcoefficient, inv_smul_smul₀ htwo] at hinv
  exact hinv

/-- **Local-observer interaction law.**  One local flip sees exactly the
rational span of all interaction coefficients incident on that degree of
freedom. -/
theorem lbitLocalFlipFrequencySubspace_eq_incident
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) :
    lbitLocalFlipFrequencySubspace J =
      lbitIncidentCoefficientSubspace J :=
  le_antisymm
    (lbitLocalFlipFrequencySubspace_le_incident J)
    (lbitIncidentCoefficientSubspace_le_localFlip J)

/-- Arithmetic temporal dimension carried by one localized flip. -/
def lbitLocalFlipTemporalRank
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) : ℕ :=
  Module.finrank ℚ (lbitLocalFlipFrequencySubspace J)

theorem lbitLocalFlipTemporalRank_eq
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) :
    lbitLocalFlipTemporalRank J =
      Module.finrank ℚ (lbitIncidentCoefficientSubspace J) := by
  rw [lbitLocalFlipTemporalRank,
    lbitLocalFlipFrequencySubspace_eq_incident]

/-- Rational independence of all incident coefficients makes one local flip
carry the full `2 ^ |I|` temporal dimension. -/
theorem lbitLocalFlipTemporalRank_eq_maximal
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ)
    (hJ : LinearIndependent ℚ J) :
    lbitLocalFlipTemporalRank J = 2 ^ Fintype.card I := by
  rw [lbitLocalFlipTemporalRank_eq]
  unfold lbitIncidentCoefficientSubspace
  rw [finrank_span_eq_card hJ]
  simp

/-- Diagonal energy of one distinguished two-level degree of freedom
conditionally coupled to a Boolean environment. -/
def lbitConditionalTwoLevelEnergy
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) (z : Bool × (I → Bool)) : ℝ :=
  if z.1 then -lbitEnergy J z.2 else lbitEnergy J z.2

/-- The distinguished local flip has exactly the conditional frequency
defined above. -/
theorem lbitConditionalTwoLevelEnergy_flipGap
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) (x : I → Bool) :
    lbitConditionalTwoLevelEnergy J (false, x) -
        lbitConditionalTwoLevelEnergy J (true, x) =
      lbitLocalFlipFrequency J x := by
  simpa [lbitConditionalTwoLevelEnergy, lbitLocalFlipFrequency] using
    (two_smul ℚ (lbitEnergy J x)).symm

/-- Matrix Hamiltonian for the distinguished l-bit and its Boolean
environment. -/
def lbitConditionalTwoLevelHamiltonianMatrix
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) :
    Matrix (Bool × (I → Bool)) (Bool × (I → Bool)) ℝ :=
  Matrix.diagonal (lbitConditionalTwoLevelEnergy J)

/-- The conditional interacting Hamiltonian has no transport between
distinct configurations. -/
theorem lbitConditionalTwoLevelHamiltonianMatrix_offDiagonal
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ)
    {x y : Bool × (I → Bool)} (hxy : x ≠ y) :
    lbitConditionalTwoLevelHamiltonianMatrix J x y = 0 := by
  simp [lbitConditionalTwoLevelHamiltonianMatrix, Matrix.diagonal, hxy]

/-- Without interactions with the environment, one local flip has at most
one temporal direction. -/
theorem lbitLocalFlipTemporalRank_le_one_of_noninteracting
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ)
    (hJ : ∀ S, S.Nonempty → J S = 0) :
    lbitLocalFlipTemporalRank J ≤ 1 := by
  let line : Submodule ℚ ℝ := ℚ ∙ J ∅
  have hle :
      lbitIncidentCoefficientSubspace J ≤ line := by
    apply Submodule.span_le.2
    rintro z ⟨S, rfl⟩
    by_cases hS : S.Nonempty
    · rw [hJ S hS]
      exact line.zero_mem
    · have hSempt : S = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      exact Submodule.subset_span (Set.mem_singleton _)
  rw [lbitLocalFlipTemporalRank_eq]
  calc
    Module.finrank ℚ (lbitIncidentCoefficientSubspace J) ≤
        Module.finrank ℚ line :=
      Submodule.finrank_mono hle
    _ ≤ 1 := by
      by_cases hzero : J ∅ = 0
      · rw [show line = ⊥ by simp [line, hzero]]
        simp
      · rw [show line = ℚ ∙ J ∅ by rfl,
          finrank_span_singleton hzero]

/-- One explicit coefficient family makes one localized flip carry all
`2 ^ |I|` temporal directions. -/
theorem explicitMaximalLocalFlipTemporalRank
    (I : Type*) [Fintype I] [DecidableEq I] :
    lbitLocalFlipTemporalRank (rationalIndependentWeights (Finset I)) =
      2 ^ Fintype.card I := by
  apply lbitLocalFlipTemporalRank_eq_maximal
  exact rationalIndependentWeights_linearIndependent (Finset I)

end

end GaloisForLFunctions.HTGeometry
