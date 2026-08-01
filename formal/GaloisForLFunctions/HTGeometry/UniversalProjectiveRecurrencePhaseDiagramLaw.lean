import GaloisForLFunctions.HTGeometry.BaireGenericAvoidance
import GaloisForLFunctions.HTGeometry.ResolvedReplicaRecurrenceWallLaw

/-!
# Universal projective-recurrence phase diagram

Every real linear control family induces one affine functional for each
finitely supported projective spectral character.  This gives an exhaustive
trichotomy: a recurrence character is protected throughout control space,
absent throughout control space, or confined to a nowhere-dense affine wall.

For countable spectra and controls transverse to every nonzero character,
maximal projective freedom is comeager and dense in any Baire control space.
The one-parameter recurrence-wall law is therefore a line section of a
control-space phase diagram.  Each wall retains the exact inverse-time sinc
normal profile, and on finite carriers its first nonzero survival-fidelity
replica layer is exactly the positive character mass.
-/

open Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Linear response of one projective character to an arbitrary real control space. -/
def projectiveControlDetuning
    {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (k : ProjectiveCharacter I) (response : I → X →L[ℝ] ℝ) :
    X →L[ℝ] ℝ :=
  ∑ i ∈ k.1.support, (k.1 i : ℝ) • response i

theorem projectiveControlDetuning_apply
    {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (k : ProjectiveCharacter I) (response : I → X →L[ℝ] ℝ)
    (x : X) :
    projectiveControlDetuning k response x =
      projectiveCharacterDetuning k (fun i => response i x) := by
  simp [projectiveControlDetuning, projectiveCharacterDetuning]

/-- Spectrum at a point of an arbitrary linear control space. -/
def controlledProjectiveEnergy
    {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (energy : I → ℝ) (response : I → X →L[ℝ] ℝ) (x : X) (i : I) : ℝ :=
  energy i + response i x

theorem projectiveCharacterDetuning_controlledEnergy
    {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (k : ProjectiveCharacter I) (energy : I → ℝ)
    (response : I → X →L[ℝ] ℝ) (x : X) :
    projectiveCharacterDetuning k
        (controlledProjectiveEnergy energy response x) =
      projectiveCharacterDetuning k energy +
        projectiveControlDetuning k response x := by
  change projectiveCharacterDetuning k (fun i => energy i + response i x) = _
  rw [projectiveCharacterDetuning_add,
    projectiveControlDetuning_apply]

/-- Exact recurrence wall cut out by one projective character. -/
def projectiveControlRecurrenceWall
    {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (energy : I → ℝ) (response : I → X →L[ℝ] ℝ)
    (k : ProjectiveCharacter I) : Set X :=
  {x | projectiveCharacterDetuning k
      (controlledProjectiveEnergy energy response x) = 0}

theorem mem_projectiveControlRecurrenceWall_iff
    {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (energy : I → ℝ) (response : I → X →L[ℝ] ℝ)
    (k : ProjectiveCharacter I) (x : X) :
    x ∈ projectiveControlRecurrenceWall energy response k ↔
      projectiveControlDetuning k response x =
        -projectiveCharacterDetuning k energy := by
  change projectiveCharacterDetuning k
    (controlledProjectiveEnergy energy response x) = 0 ↔ _
  rw [projectiveCharacterDetuning_controlledEnergy]
  constructor <;> intro h <;> linarith

theorem affineLevelSet_isNowhereDense
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X →L[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) :
    IsNowhereDense {x | f x = c} := by
  apply GaloisForLFunctions.isNowhereDense_of_isClosed_of_interior_eq_empty
  · exact isClosed_singleton.preimage f.continuous
  · by_contra hne
    obtain ⟨x, hx⟩ : (interior {x | f x = c}).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hne
    have hxlevel : f x = c := by
      have hxmem : x ∈ {y : X | f y = c} :=
        (interior_subset : interior {y : X | f y = c} ⊆ {y : X | f y = c}) hx
      exact hxmem
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
    have hfnonzero : ∃ v : X, f v ≠ 0 := by
      simpa [ContinuousLinearMap.ext_iff] using hf
    obtain ⟨v, hv⟩ := hfnonzero
    let t : ℝ := ε / (2 * (norm v + 1))
    have hden : 0 < 2 * (norm v + 1) := by positivity
    have ht : 0 < t := div_pos hε hden
    have hdist : dist (x + t • v) x < ε := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht]
      dsimp [t]
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ hden).2
      nlinarith [norm_nonneg v]
    have hyinterior : x + t • v ∈ interior {x | f x = c} :=
      hball hdist
    have hylevel : f (x + t • v) = c := by
      have hymem : x + t • v ∈ {y : X | f y = c} :=
        (interior_subset : interior {y : X | f y = c} ⊆ {y : X | f y = c})
          hyinterior
      exact hymem
    rw [map_add, map_smul, hxlevel] at hylevel
    have hprod : t * f v = 0 := by
      have hz : t • f v = 0 := by linarith
      simpa [smul_eq_mul] using hz
    exact hv ((mul_eq_zero.mp hprod).resolve_left ht.ne')

/-- Every unprotected recurrence wall is nowhere dense in control space. -/
theorem projectiveControlRecurrenceWall_isNowhereDense
    {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (energy : I → ℝ) (response : I → X →L[ℝ] ℝ)
    (k : ProjectiveCharacter I)
    (htransverse : projectiveControlDetuning k response ≠ 0) :
    IsNowhereDense (projectiveControlRecurrenceWall energy response k) := by
  rw [show projectiveControlRecurrenceWall energy response k =
      {x | projectiveControlDetuning k response x =
        -projectiveCharacterDetuning k energy} by
    ext x
    exact mem_projectiveControlRecurrenceWall_iff energy response k x]
  exact affineLevelSet_isNowhereDense _ htransverse _

/-- Tangent characters have either a wall filling all control space or no wall at all. -/
theorem projectiveControlRecurrenceWall_eq_univ_or_empty_of_tangent
    {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (energy : I → ℝ) (response : I → X →L[ℝ] ℝ)
    (k : ProjectiveCharacter I)
    (htangent : projectiveControlDetuning k response = 0) :
    (projectiveCharacterDetuning k energy = 0 ∧
        projectiveControlRecurrenceWall energy response k = Set.univ) ∨
      (projectiveCharacterDetuning k energy ≠ 0 ∧
        projectiveControlRecurrenceWall energy response k = ∅) := by
  by_cases hbase : projectiveCharacterDetuning k energy = 0
  · left
    refine ⟨hbase, ?_⟩
    ext x
    rw [mem_projectiveControlRecurrenceWall_iff, htangent]
    simp [hbase]
  · right
    refine ⟨hbase, ?_⟩
    ext x
    rw [mem_projectiveControlRecurrenceWall_iff, htangent]
    simp [hbase]

/-- Every nonzero projective character is moved by at least one declared control direction. -/
def ProjectivelyTransverseControl
    {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (response : I → X →L[ℝ] ℝ) : Prop :=
  ∀ k : ProjectiveCharacter I, k ≠ 0 →
    projectiveControlDetuning k response ≠ 0

/-- For a countable spectrum, maximal projective freedom under a transverse
control family is comeager in every Baire control space. -/
theorem maximallyProjective_controlParameters_mem_residual
    {I X : Type*} [Countable I]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [BaireSpace X]
    (energy : I → ℝ) (response : I → X →L[ℝ] ℝ)
    (htransverse : ProjectivelyTransverseControl response) :
    {x | FinitelySupportedMaximallyProjectiveEnergy
      (controlledProjectiveEnergy energy response x)} ∈ residual X := by
  classical
  by_cases hnontrivial : ∃ k : ProjectiveCharacter I, k ≠ 0
  · let K := {k : ProjectiveCharacter I // k ≠ 0}
    letI : Nonempty K := ⟨⟨Classical.choose hnontrivial,
      Classical.choose_spec hnontrivial⟩⟩
    let enumerate : ℕ → K := Classical.choose (exists_surjective_nat K)
    have henumerate : Function.Surjective enumerate :=
      Classical.choose_spec (exists_surjective_nat K)
    let S : ℕ → Set X := fun n =>
      projectiveControlRecurrenceWall energy response (enumerate n).1
    have hnowhere : ∀ n, IsNowhereDense (S n) := by
      intro n
      exact projectiveControlRecurrenceWall_isNowhereDense
        energy response (enumerate n).1
        (htransverse (enumerate n).1 (enumerate n).2)
    have havoid : {x | ∀ n, x ∉ S n} = ⋂ n, (S n)ᶜ := by
      ext x
      simp
    have hresidual : {x | ∀ n, x ∉ S n} ∈ residual X := by
      rw [havoid]
      exact countable_iInter_mem.mpr fun n => (hnowhere n).isMeagre
    have hset :
        {x | FinitelySupportedMaximallyProjectiveEnergy
          (controlledProjectiveEnergy energy response x)} =
        {x | ∀ n, x ∉ S n} := by
      ext x
      constructor
      · intro hx n hxn
        have hdetuning : projectiveCharacterDetuning (enumerate n).1
            (controlledProjectiveEnergy energy response x) = 0 := hxn
        exact (enumerate n).2 (hx (enumerate n).1 hdetuning)
      · intro hx k hk
        by_contra hkzero
        let kK : K := ⟨k, hkzero⟩
        obtain ⟨n, hn⟩ := henumerate kK
        apply hx n
        change projectiveCharacterDetuning (enumerate n).1
          (controlledProjectiveEnergy energy response x) = 0
        have hnk : (enumerate n).1 = k := congrArg Subtype.val hn
        rw [hnk]
        exact hk
    rw [hset]
    exact hresidual
  · have hset :
        {x | FinitelySupportedMaximallyProjectiveEnergy
          (controlledProjectiveEnergy energy response x)} = Set.univ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro k hk
      by_contra hkzero
      exact hnontrivial ⟨k, hkzero⟩
    rw [hset]
    exact Filter.univ_mem

/-- For a countable spectrum, a transverse control family makes maximal
projective freedom dense in every Baire control space. -/
theorem dense_maximallyProjective_controlParameters
    {I X : Type*} [Countable I]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [BaireSpace X]
    (energy : I → ℝ) (response : I → X →L[ℝ] ℝ)
    (htransverse : ProjectivelyTransverseControl response) :
    Dense {x | FinitelySupportedMaximallyProjectiveEnergy
      (controlledProjectiveEnergy energy response x)} :=
  dense_of_mem_residual
    (maximallyProjective_controlParameters_mem_residual
      energy response htransverse)

/-- Completed-time wall reporter for an arbitrary point in control space. -/
def controlledRecurrenceWallReporter
    {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (k : ProjectiveCharacter I) (energy : I → ℝ)
    (response : I → X →L[ℝ] ℝ) (T : ℝ) (x : X) : ℂ :=
  symmetricPhaseAverage T
    (projectiveCharacterDetuning k
      (controlledProjectiveEnergy energy response x))

theorem controlledRecurrenceWallReporter_scaled_normal_profile
    {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (k : ProjectiveCharacter I) (energy : I → ℝ)
    (response : I → X →L[ℝ] ℝ) (x₀ v : X) (T ξ : ℝ)
    (hwall : x₀ ∈ projectiveControlRecurrenceWall energy response k)
    (hT : T ≠ 0) :
    controlledRecurrenceWallReporter k energy response T
        (x₀ + (ξ / T) • v) =
      Real.sinc (ξ * projectiveControlDetuning k response v) := by
  unfold controlledRecurrenceWallReporter
  rw [symmetricPhaseAverage_eq_sinc _ _ hT]
  have hx₀ : projectiveCharacterDetuning k energy +
      projectiveControlDetuning k response x₀ = 0 := by
    have hwall' : projectiveCharacterDetuning k
        (controlledProjectiveEnergy energy response x₀) = 0 := hwall
    simpa [projectiveCharacterDetuning_controlledEnergy] using hwall'
  rw [projectiveCharacterDetuning_controlledEnergy, map_add, map_smul]
  norm_cast
  apply congrArg Real.sinc
  simp only [smul_eq_mul]
  field_simp [hT]
  linear_combination T * hx₀

/-- Resolved contribution of one character to a survival-fidelity replica
layer at an arbitrary control point. -/
def resolvedControlledReplicaWallSignal
    {I X : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (weight : I → ℝ) (n : ℕ) (k : ProjectiveCharacter I)
    (energy : I → ℝ) (response : I → X →L[ℝ] ℝ)
    (T : ℝ) (x : X) : ℂ :=
  (fidelityReplicaCharacterCoefficient weight n
      (finiteCharacterOfProjective k) : ℂ) *
    controlledRecurrenceWallReporter k energy response T x

/-- Every replica layer below a wall's positive character mass is exactly
zero at every control point and every observation time. -/
theorem resolvedControlledReplicaWallSignal_eq_zero_of_lt_height
    {I X : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {weight : I → ℝ} (hweight : ∀ i, 0 < weight i)
    (n : ℕ) (k : ProjectiveCharacter I)
    (hlt : n < projectiveCharacterReplicaHeight k)
    (energy : I → ℝ) (response : I → X →L[ℝ] ℝ)
    (T : ℝ) (x : X) :
    resolvedControlledReplicaWallSignal weight n k energy response T x = 0 := by
  have hnotpos :
      ¬ 0 < fidelityReplicaCharacterCoefficient weight n
        (finiteCharacterOfProjective k) := by
    intro hpos
    have hle :=
      (fidelityReplicaCharacterCoefficient_pos_iff_positiveMass_le
        hweight (projectiveCharacter_spectralCharacterBalanced k) n).mp hpos
    exact (not_le_of_gt hlt) hle
  have hnonneg :
      0 ≤ fidelityReplicaCharacterCoefficient weight n
        (finiteCharacterOfProjective k) :=
    fidelityReplicaCharacterCoefficient_nonneg hweight n _
  have hzero :
      fidelityReplicaCharacterCoefficient weight n
          (finiteCharacterOfProjective k) = 0 :=
    le_antisymm (le_of_not_gt hnotpos) hnonneg
  simp [resolvedControlledReplicaWallSignal, hzero]

/-- At the first allowed replica height, the resolved wall has positive
weight and the exact coefficient-weighted sinc profile along every normal
control section. -/
theorem resolvedControlledReplicaWallSignal_scaled_profile_at_height
    {I X : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {weight : I → ℝ} (hweight : ∀ i, 0 < weight i)
    (k : ProjectiveCharacter I) (energy : I → ℝ)
    (response : I → X →L[ℝ] ℝ) (x₀ v : X) (T ξ : ℝ)
    (hwall : x₀ ∈ projectiveControlRecurrenceWall energy response k)
    (hT : T ≠ 0) :
    resolvedControlledReplicaWallSignal weight
        (projectiveCharacterReplicaHeight k) k energy response T
        (x₀ + (ξ / T) • v) =
      (fidelityReplicaCharacterCoefficient weight
          (projectiveCharacterReplicaHeight k)
          (finiteCharacterOfProjective k) : ℂ) *
        Real.sinc (ξ * projectiveControlDetuning k response v) ∧
      0 < fidelityReplicaCharacterCoefficient weight
        (projectiveCharacterReplicaHeight k)
        (finiteCharacterOfProjective k) := by
  constructor
  · rw [resolvedControlledReplicaWallSignal,
      controlledRecurrenceWallReporter_scaled_normal_profile
        k energy response x₀ v T ξ hwall hT]
  · exact resolvedReplicaWallCoefficient_pos_at_height hweight k

/-- A finite-carrier wall is active exactly at its minimum resolved replica
height; no transversality or genericity premise is required. -/
theorem resolvedControlledReplicaDetects_at_height_iff_wall
    {I X : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (k : ProjectiveCharacter I) (energy : I → ℝ)
    (response : I → X →L[ℝ] ℝ) (x : X) :
    ResolvedReplicaDetects
        (controlledProjectiveEnergy energy response x)
        (projectiveCharacterReplicaHeight k)
        (finiteCharacterOfProjective k) ↔
      x ∈ projectiveControlRecurrenceWall energy response k := by
  unfold ResolvedReplicaDetects
  have hrealizes :
      SpectralCharacterReplicaRealizes
        (projectiveCharacterReplicaHeight k)
        (finiteCharacterOfProjective k) :=
    spectralCharacterReplicaRealizes_positiveMass_of_balanced
      (projectiveCharacter_spectralCharacterBalanced k)
  rw [and_iff_right hrealizes,
    finiteProjectiveDetuning_eq_projectiveCharacterDetuning]
  rfl

end

end GaloisForLFunctions.HTGeometry
