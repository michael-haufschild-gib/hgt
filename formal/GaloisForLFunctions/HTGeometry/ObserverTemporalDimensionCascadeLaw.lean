import Mathlib

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Total coefficient of a rational phase character. -/
def rationalCharacterCharge
    (I : Type*) [Fintype I] : (I → ℚ) →ₗ[ℚ] ℚ where
  toFun k := ∑ i, k i
  map_add' k l := by simp [Finset.sum_add_distrib]
  map_smul' q k := by
    simp [Finset.mul_sum]

/-- Rational projective characters, i.e. coefficient vectors with zero
total charge. -/
def projectiveRationalCharacterSpace
    (I : Type*) [Fintype I] : Submodule ℚ (I → ℚ) :=
  (rationalCharacterCharge I).ker

abbrev ProjectiveRationalCharacter
    (I : Type*) [Fintype I] :=
  projectiveRationalCharacterSpace I

/-- Truncated spectral-jet evaluation of a projective rational character. -/
def projectiveJetMap
    {I : Type*} [Fintype I]
    (jet : ℕ → I → ℂ) (r : ℕ) :
    ProjectiveRationalCharacter I →ₗ[ℚ] (Fin r → ℂ) where
  toFun k := fun n => ∑ i, (k.1 i : ℂ) * jet n i
  map_add' k l := by
    ext n
    change
      (∑ i, ((k.1 i + l.1 i : ℚ) : ℂ) * jet n i) =
        (∑ i, (k.1 i : ℂ) * jet n i) +
          ∑ i, (l.1 i : ℂ) * jet n i
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    push_cast
    ring_nf
  map_smul' q k := by
    ext n
    change
      (∑ i, ((q * k.1 i : ℚ) : ℂ) * jet n i) =
        q • ∑ i, (k.1 i : ℂ) * jet n i
    simp only [Algebra.smul_def]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    push_cast
    change
      (q : ℂ) * (k.1 i : ℂ) * jet n i =
        (q : ℂ) * ((k.1 i : ℂ) * jet n i)
    ring_nf

/-- Rational spectral relations invisible through every jet below `r`. -/
def rationalSpectralConstraintSpace
    {I : Type*} [Fintype I]
    (jet : ℕ → I → ℂ) (r : ℕ) :
    Submodule ℚ (ProjectiveRationalCharacter I) :=
  (projectiveJetMap jet r).ker

/-- Temporal directions exposed by spectral jets below `r`. -/
def temporalDirectionSpace
    {I : Type*} [Fintype I]
    (jet : ℕ → I → ℂ) (r : ℕ) :
    Submodule ℚ (Fin r → ℂ) :=
  (projectiveJetMap jet r).range

/-- Observer-time dimension resolved through jet order `r - 1`. -/
noncomputable def temporalDimension
    {I : Type*} [Fintype I]
    (jet : ℕ → I → ℂ) (r : ℕ) : ℕ :=
  Module.finrank ℚ (temporalDirectionSpace jet r)

/-- **Exact rank-nullity law of observer time.** Resolved temporal
dimension plus persistent relation rank equals total projective character
rank at every resolution order. -/
theorem temporalDimension_add_constraintFinrank
    {I : Type*} [Fintype I]
    (jet : ℕ → I → ℂ) (r : ℕ) :
    temporalDimension jet r +
        Module.finrank ℚ (rationalSpectralConstraintSpace jet r) =
      Module.finrank ℚ (ProjectiveRationalCharacter I) := by
  exact (projectiveJetMap jet r).finrank_range_add_finrank_ker

/-- Higher jet resolution can only remove rational spectral relations. -/
theorem rationalSpectralConstraintSpace_antitone
    {I : Type*} [Fintype I]
    (jet : ℕ → I → ℂ) :
    Antitone (rationalSpectralConstraintSpace jet) := by
  intro r s hrs k hk
  change projectiveJetMap jet s k = 0 at hk
  change projectiveJetMap jet r k = 0
  ext n
  let m : Fin s := ⟨n, n.isLt.trans_le hrs⟩
  have hm := congrFun hk m
  simpa [projectiveJetMap, m] using hm

/-- **Observer-time dimension is monotone.** Longer perturbative
resolution cannot erase an already exposed temporal direction. -/
theorem temporalDimension_mono
    {I : Type*} [Fintype I]
    (jet : ℕ → I → ℂ) :
    Monotone (temporalDimension jet) := by
  intro r s hrs
  have hker :
      rationalSpectralConstraintSpace jet s ≤
        rationalSpectralConstraintSpace jet r :=
    rationalSpectralConstraintSpace_antitone jet hrs
  have hfin :
      Module.finrank ℚ (rationalSpectralConstraintSpace jet s) ≤
        Module.finrank ℚ (rationalSpectralConstraintSpace jet r) :=
    Submodule.finrank_mono hker
  have hrankR :=
    temporalDimension_add_constraintFinrank jet r
  have hrankS :=
    temporalDimension_add_constraintFinrank jet s
  omega

/-- The rational projective character space on a nonempty finite spectrum
has the expected dimension: number of labels minus global phase. -/
theorem finrank_projectiveRationalCharacter
    (I : Type*) [Fintype I] [Nonempty I] :
    Module.finrank ℚ (ProjectiveRationalCharacter I) =
      Fintype.card I - 1 := by
  classical
  let i : I := Classical.choice ‹Nonempty I›
  have hsurj : Function.Surjective (rationalCharacterCharge I) := by
    intro q
    refine ⟨Pi.single i q, ?_⟩
    simp [rationalCharacterCharge]
  have hrange :
      (rationalCharacterCharge I).range = ⊤ :=
    LinearMap.range_eq_top_of_surjective _ hsurj
  have hrank :=
    (rationalCharacterCharge I).finrank_range_add_finrank_ker
  rw [hrange] at hrank
  have hcard : 0 < Fintype.card I := Fintype.card_pos
  change Module.finrank ℚ (rationalCharacterCharge I).ker =
    Fintype.card I - 1
  have hrank' :
      1 + Module.finrank ℚ (rationalCharacterCharge I).ker =
        Fintype.card I := by
    simpa [Module.finrank_pi_fintype] using hrank
  omega

/-- Observer-time dimension can never exceed projective spectral
cardinality. -/
theorem temporalDimension_le_card_sub_one
    {I : Type*} [Fintype I] [Nonempty I]
    (jet : ℕ → I → ℂ) (r : ℕ) :
    temporalDimension jet r ≤ Fintype.card I - 1 := by
  calc
    temporalDimension jet r ≤
        Module.finrank ℚ (ProjectiveRationalCharacter I) :=
      (projectiveJetMap jet r).finrank_range_le
    _ = Fintype.card I - 1 :=
      finrank_projectiveRationalCharacter I

/-- **Dimension/constraint conservation.** Between any two resolution
orders, temporal dimension gained is exactly persistent relation rank lost. -/
theorem temporalDimension_sub_eq_constraintFinrank_sub
    {I : Type*} [Fintype I]
    (jet : ℕ → I → ℂ) {r s : ℕ} (hrs : r ≤ s) :
    temporalDimension jet s - temporalDimension jet r =
      Module.finrank ℚ (rationalSpectralConstraintSpace jet r) -
        Module.finrank ℚ (rationalSpectralConstraintSpace jet s) := by
  have hdim := temporalDimension_mono jet hrs
  have hker :
      rationalSpectralConstraintSpace jet s ≤
        rationalSpectralConstraintSpace jet r :=
    rationalSpectralConstraintSpace_antitone jet hrs
  have hfin :
      Module.finrank ℚ (rationalSpectralConstraintSpace jet s) ≤
        Module.finrank ℚ (rationalSpectralConstraintSpace jet r) :=
    Submodule.finrank_mono hker
  have hrankR :=
    temporalDimension_add_constraintFinrank jet r
  have hrankS :=
    temporalDimension_add_constraintFinrank jet s
  omega

/-- No temporal direction is visible before any spectral coefficient is
included. -/
theorem temporalDimension_zero
    {I : Type*} [Fintype I]
    (jet : ℕ → I → ℂ) :
    temporalDimension jet 0 = 0 := by
  unfold temporalDimension temporalDirectionSpace
  have hrange : (projectiveJetMap jet 0).range = ⊥ := by
    ext x
    constructor
    · intro hx
      exact Subsingleton.elim _ _
    · intro hx
      rw [hx]
      exact Submodule.zero_mem _
  rw [hrange]
  simp

end

end GaloisForLFunctions.HTGeometry
