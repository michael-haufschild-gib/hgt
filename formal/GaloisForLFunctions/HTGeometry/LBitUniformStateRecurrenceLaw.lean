import GaloisForLFunctions.HTGeometry.LBitRecurrenceConstraintLaw

/-!
# Uniform-product-state visibility of the full l-bit recurrence law

For a finite binary l-bit Hamiltonian, the uniform product state assigns the
same strictly positive Born weight to every configuration.  Consequently its
visible anchored-gap space is the complete l-bit gap space: no spectral
direction is lost by state preparation.

The concrete survival amplitude of this state is the equal-weight finite
spectral phase sum.  Maximal l-bit temporal rank is therefore equivalent to
all long-time moments of this single state's survival fidelity attaining the
unavoidable permutation floor.

This is an exact ideal l-bit statement.  It does not assert that the l-bit
basis is known in microscopic physical-spin coordinates or that measuring
all replica moments is experimentally scalable.
-/

open Set Filter MeasureTheory Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

noncomputable local instance lbitUniformStateFintypeForallBool
    {I : Type*} [Fintype I] :
    Fintype (I → Bool) :=
  Fintype.ofFinite _

/-- Equal Born weight of every configuration in the uniform l-bit product
state. -/
def lbitUniformSpectralWeight
    {I : Type*} [Fintype I] (_x : I → Bool) : ℝ :=
  (((2 ^ Fintype.card I : ℕ) : ℝ))⁻¹

/-- Every configuration has strictly positive weight in the uniform l-bit
product state. -/
theorem lbitUniformSpectralWeight_pos
    {I : Type*} [Fintype I] (x : I → Bool) :
    0 < lbitUniformSpectralWeight x := by
  unfold lbitUniformSpectralWeight
  positivity

/-- The uniform l-bit spectral weights are normalized. -/
theorem sum_lbitUniformSpectralWeight_eq_one
    {I : Type*} [Fintype I] :
    (∑ x : I → Bool, lbitUniformSpectralWeight x) = 1 := by
  classical
  simp only [lbitUniformSpectralWeight, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  rw [show Fintype.card (I → Bool) = 2 ^ Fintype.card I by
    rw [Fintype.card_eq_nat_card, Nat.card_fun]
    norm_num [Nat.card_eq_fintype_card]]
  field_simp

/-- Configuration-basis wavefunction of `|+⟩ ^ ⊗ I`: every amplitude is the
positive square root of the uniform Born weight. -/
def lbitUniformProductState
    {I : Type*} [Fintype I] (x : I → Bool) : ℂ :=
  Real.sqrt (lbitUniformSpectralWeight x)

/-- The uniform product state is normalized in the finite configuration
Hilbert space. -/
theorem sum_normSq_lbitUniformProductState_eq_one
    {I : Type*} [Fintype I] :
    (∑ x : I → Bool, ‖lbitUniformProductState x‖ ^ 2) = 1 := by
  rw [← sum_lbitUniformSpectralWeight_eq_one (I := I)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [lbitUniformProductState, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (le_of_lt (lbitUniformSpectralWeight_pos x))]

/-- Every configuration amplitude of the uniform product state is nonzero. -/
theorem lbitUniformProductState_ne_zero
    {I : Type*} [Fintype I] (x : I → Bool) :
    lbitUniformProductState x ≠ 0 := by
  unfold lbitUniformProductState
  exact_mod_cast
    (Real.sqrt_ne_zero'.mpr (lbitUniformSpectralWeight_pos x))

/-- Uniform product state evolved by the diagonal l-bit energy. -/
def lbitDiagonalEvolvedUniformProductState
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) (t : ℝ) (x : I → Bool) : ℂ :=
  lbitUniformProductState x *
    Complex.exp
      (((lbitEnergy J x * t : ℝ) : ℂ) * Complex.I)

/-- Hilbert-space overlap of the uniform product state with its diagonal
l-bit evolution. -/
def lbitUniformProductStateSurvivalAmplitude
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) (t : ℝ) : ℂ :=
  ∑ x : I → Bool,
    star (lbitUniformProductState x) *
      lbitDiagonalEvolvedUniformProductState J t x

/-- The concrete product-state overlap is exactly the equal-weight spectral
survival amplitude. -/
theorem lbitUniformProductStateSurvivalAmplitude_eq
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) (t : ℝ) :
    lbitUniformProductStateSurvivalAmplitude J t =
      finiteSpectralSurvivalAmplitude
        (lbitUniformSpectralWeight (I := I)) (lbitEnergy J) t := by
  classical
  unfold lbitUniformProductStateSurvivalAmplitude
    lbitDiagonalEvolvedUniformProductState
    finiteSpectralSurvivalAmplitude
  apply Finset.sum_congr rfl
  intro x hx
  rw [lbitUniformProductState]
  rw [Complex.star_def, Complex.conj_ofReal]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← pow_two,
    Real.sq_sqrt (le_of_lt (lbitUniformSpectralWeight_pos x))]

/-- Gap space visible to the uniform product state.  The subtype records
exactly the configuration energies carrying nonzero Born weight. -/
def lbitUniformStateVisibleGapSubspace
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) : Submodule ℚ ℝ :=
  Submodule.span ℚ
    (Set.range
      (fun x : {x : I → Bool //
          lbitUniformSpectralWeight x ≠ 0} =>
        lbitGap J x.1))

/-- Full support of the uniform product state makes its visible gap space
equal to the complete l-bit gap space. -/
theorem lbitUniformStateVisibleGapSubspace_eq
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) :
    lbitUniformStateVisibleGapSubspace J = lbitGapSubspace J := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro z ⟨x, rfl⟩
    exact Submodule.subset_span ⟨x.1, rfl⟩
  · apply Submodule.span_le.2
    rintro z ⟨x, rfl⟩
    apply Submodule.subset_span
    exact
      ⟨⟨x, ne_of_gt (lbitUniformSpectralWeight_pos x)⟩, rfl⟩

/-- Rational dimension of the gap space seen by the uniform product state. -/
def lbitUniformStateVisibleTemporalRank
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) : ℕ :=
  Module.finrank ℚ (lbitUniformStateVisibleGapSubspace J)

/-- The uniform product state sees every l-bit temporal direction. -/
theorem lbitUniformStateVisibleTemporalRank_eq
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) :
    lbitUniformStateVisibleTemporalRank J = lbitTemporalRank J := by
  rw [lbitUniformStateVisibleTemporalRank,
    lbitUniformStateVisibleGapSubspace_eq, lbitTemporalRank]

/-- Maximal l-bit temporal rank is exactly maximal projective energy
arithmetic for the complete configuration spectrum. -/
theorem lbitTemporalRank_eq_maximal_iff_maximallyProjectiveEnergy
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) :
    lbitTemporalRank J = 2 ^ Fintype.card I - 1 ↔
      MaximallyProjectiveEnergy (lbitEnergy J) := by
  constructor
  · intro hfull
    have hrelation :
        projectiveSpectralRelationRationalSpace
            (lbitEnergy J) = ⊥ :=
      lbitFullTemporalRank_relationSpace_eq_bot J hfull
    intro k hbalanced henergy
    let q : ProjectiveRationalCharacter (I → Bool) :=
      ⟨fun x => (k x : ℚ), by
        change (∑ x, (k x : ℚ)) = 0
        unfold SpectralCharacterBalanced at hbalanced
        exact_mod_cast hbalanced⟩
    have hqmem :
        q ∈
          projectiveSpectralRelationRationalSpace
            (lbitEnergy J) :=
      (projectiveEnergyDetuning_ker_eq_relationSpace
        (lbitEnergy J)) ▸ (by
          change (∑ x, (k x : ℝ) * lbitEnergy J x) = 0
          exact henergy)
    rw [hrelation] at hqmem
    have hqzero : q = 0 :=
      hqmem
    funext x
    have hx := congrArg
      (fun r : ProjectiveRationalCharacter (I → Bool) => r.1 x)
      hqzero
    change ((k x : ℤ) : ℚ) = 0 at hx
    exact_mod_cast hx
  · intro hmax
    have hrelation :
        projectiveSpectralRelationRationalSpace
            (lbitEnergy J) = ⊥ := by
      apply le_antisymm
      · apply Submodule.span_le.2
        rintro r ⟨q, hq, rfl⟩
        have hdata :=
          (mem_projectiveSpectralRelationLattice_iff
            (lbitEnergy J) (finiteCharacterOfProjective q)).1 hq
        have hqzero :
            finiteCharacterOfProjective q = 0 :=
          hmax (finiteCharacterOfProjective q) hdata.1 hdata.2
        have qzero : q = 0 := by
          apply Subtype.ext
          apply Finsupp.ext
          intro x
          exact congrFun hqzero x
        have hzero : projectiveCharacterToRational q = 0 := by
          rw [qzero]
          rfl
        rw [hzero]
        exact Submodule.zero_mem _
      · exact bot_le
    have hrankzero :
        Module.finrank ℚ
            (projectiveSpectralRelationRationalSpace
              (lbitEnergy J)) = 0 :=
      Submodule.finrank_eq_zero.mpr hrelation
    have hconservation := lbitTemporalRank_add_relationRank J
    rw [hrankzero, add_zero] at hconservation
    exact hconservation

/-- **Uniform-state recurrence visibility law.**  For one normalized,
full-support uniform product state, the exact maximal l-bit temporal-rank
condition is equivalent to every long-time survival-fidelity moment
attaining its unavoidable permutation collision floor. -/
theorem
    lbitUniformState_all_survivalFidelityMoments_extremal_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) :
    (∀ n : ℕ,
      Tendsto
        (finiteSpectralSurvivalFidelityMean
          (lbitUniformSpectralWeight (I := I))
          (lbitEnergy J) n)
        atTop
        (𝓝
          (fidelityReplicaPermutationFloor
            (lbitUniformSpectralWeight (I := I)) n : ℂ))) ↔
      lbitTemporalRank J = 2 ^ Fintype.card I - 1 := by
  rw [
    all_finiteSpectralSurvivalFidelityMean_tendsto_floor_iff
      (fun x : I → Bool => lbitUniformSpectralWeight_pos x)
      (lbitEnergy J),
    ← lbitTemporalRank_eq_maximal_iff_maximallyProjectiveEnergy J]

end

end GaloisForLFunctions.HTGeometry
