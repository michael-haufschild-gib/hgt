import GaloisForLFunctions.HTGeometry.ObserverTemporalDimensionCascadeLaw

/-!
# Observer-restricted temporal-constraint conservation

An observer is any finite-dimensional rational character carrier together
with a linear map into projective spectral characters. Restricting spectral
jets along that map gives an exact rank-nullity law: every observer-visible
temporal direction gained is one persistent spectral constraint lost.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Spectral jets pulled back to the characters accessible to one observer. -/
def observerProjectiveJetMap
    {I O : Type*} [Fintype I]
    [AddCommGroup O] [Module ℚ O]
    (jet : ℕ → I → ℂ)
    (observe : O →ₗ[ℚ] ProjectiveRationalCharacter I)
    (r : ℕ) :
    O →ₗ[ℚ] (Fin r → ℂ) :=
  (projectiveJetMap jet r).comp observe

/-- Observer-accessible spectral relations that persist through every jet
below `r`. -/
def observerSpectralConstraintSpace
    {I O : Type*} [Fintype I]
    [AddCommGroup O] [Module ℚ O]
    (jet : ℕ → I → ℂ)
    (observe : O →ₗ[ℚ] ProjectiveRationalCharacter I)
    (r : ℕ) : Submodule ℚ O :=
  (observerProjectiveJetMap jet observe r).ker

/-- Temporal directions exposed through one observer's characters. -/
def observerTemporalDirectionSpace
    {I O : Type*} [Fintype I]
    [AddCommGroup O] [Module ℚ O]
    (jet : ℕ → I → ℂ)
    (observe : O →ₗ[ℚ] ProjectiveRationalCharacter I)
    (r : ℕ) : Submodule ℚ (Fin r → ℂ) :=
  (observerProjectiveJetMap jet observe r).range

/-- Observer-visible temporal dimension through jet order `r - 1`. -/
noncomputable def observerTemporalDimension
    {I O : Type*} [Fintype I]
    [AddCommGroup O] [Module ℚ O]
    (jet : ℕ → I → ℂ)
    (observe : O →ₗ[ℚ] ProjectiveRationalCharacter I)
    (r : ℕ) : ℕ :=
  Module.finrank ℚ (observerTemporalDirectionSpace jet observe r)

/-- **Observer-restricted rank-nullity law.** Temporal direction rank plus
persistent relation rank equals the observer's complete character rank. -/
theorem observerTemporalDimension_add_constraintFinrank
    {I O : Type*} [Fintype I]
    [AddCommGroup O] [Module ℚ O] [FiniteDimensional ℚ O]
    (jet : ℕ → I → ℂ)
    (observe : O →ₗ[ℚ] ProjectiveRationalCharacter I)
    (r : ℕ) :
    observerTemporalDimension jet observe r +
        Module.finrank ℚ
          (observerSpectralConstraintSpace jet observe r) =
      Module.finrank ℚ O := by
  change
    Module.finrank ℚ (observerProjectiveJetMap jet observe r).range +
        Module.finrank ℚ (observerProjectiveJetMap jet observe r).ker =
      Module.finrank ℚ O
  exact
    (observerProjectiveJetMap jet observe r).finrank_range_add_finrank_ker

/-- Increasing resolution can only remove observer-accessible spectral
constraints. -/
theorem observerSpectralConstraintSpace_antitone
    {I O : Type*} [Fintype I]
    [AddCommGroup O] [Module ℚ O]
    (jet : ℕ → I → ℂ)
    (observe : O →ₗ[ℚ] ProjectiveRationalCharacter I) :
    Antitone (observerSpectralConstraintSpace jet observe) := by
  intro r s hrs k hk
  change observerProjectiveJetMap jet observe s k = 0 at hk
  change observerProjectiveJetMap jet observe r k = 0
  ext n
  let m : Fin s := ⟨n, n.isLt.trans_le hrs⟩
  have hm := congrFun hk m
  simpa [observerProjectiveJetMap, projectiveJetMap, m] using hm

/-- Observer-visible temporal dimension is monotone in resolution order. -/
theorem observerTemporalDimension_mono
    {I O : Type*} [Fintype I]
    [AddCommGroup O] [Module ℚ O] [FiniteDimensional ℚ O]
    (jet : ℕ → I → ℂ)
    (observe : O →ₗ[ℚ] ProjectiveRationalCharacter I) :
    Monotone (observerTemporalDimension jet observe) := by
  intro r s hrs
  have hker :
      observerSpectralConstraintSpace jet observe s ≤
        observerSpectralConstraintSpace jet observe r :=
    observerSpectralConstraintSpace_antitone jet observe hrs
  have hfin :
      Module.finrank ℚ
          (observerSpectralConstraintSpace jet observe s) ≤
        Module.finrank ℚ
          (observerSpectralConstraintSpace jet observe r) :=
    Submodule.finrank_mono hker
  have hrankR :=
    observerTemporalDimension_add_constraintFinrank jet observe r
  have hrankS :=
    observerTemporalDimension_add_constraintFinrank jet observe s
  omega

/-- **Observer temporal-constraint conservation.** Between two resolution
orders, temporal dimension gained equals persistent relation rank lost. -/
theorem observerTemporalDimension_sub_eq_constraintFinrank_sub
    {I O : Type*} [Fintype I]
    [AddCommGroup O] [Module ℚ O] [FiniteDimensional ℚ O]
    (jet : ℕ → I → ℂ)
    (observe : O →ₗ[ℚ] ProjectiveRationalCharacter I)
    {r s : ℕ} (hrs : r ≤ s) :
    observerTemporalDimension jet observe s -
        observerTemporalDimension jet observe r =
      Module.finrank ℚ
          (observerSpectralConstraintSpace jet observe r) -
        Module.finrank ℚ
          (observerSpectralConstraintSpace jet observe s) := by
  have hdim := observerTemporalDimension_mono jet observe hrs
  have hker :
      observerSpectralConstraintSpace jet observe s ≤
        observerSpectralConstraintSpace jet observe r :=
    observerSpectralConstraintSpace_antitone jet observe hrs
  have hfin :
      Module.finrank ℚ
          (observerSpectralConstraintSpace jet observe s) ≤
        Module.finrank ℚ
          (observerSpectralConstraintSpace jet observe r) :=
    Submodule.finrank_mono hker
  have hrankR :=
    observerTemporalDimension_add_constraintFinrank jet observe r
  have hrankS :=
    observerTemporalDimension_add_constraintFinrank jet observe s
  omega

/-- No observer-visible temporal direction exists before any jet
coefficient is included. -/
theorem observerTemporalDimension_zero
    {I O : Type*} [Fintype I]
    [AddCommGroup O] [Module ℚ O]
    (jet : ℕ → I → ℂ)
    (observe : O →ₗ[ℚ] ProjectiveRationalCharacter I) :
    observerTemporalDimension jet observe 0 = 0 := by
  unfold observerTemporalDimension observerTemporalDirectionSpace
  have hrange :
      (observerProjectiveJetMap jet observe 0).range = ⊥ := by
    ext x
    constructor
    · intro hx
      exact Subsingleton.elim _ _
    · intro hx
      rw [hx]
      exact Submodule.zero_mem _
  rw [hrange]
  simp

/-- Observer-visible temporal dimension cannot exceed the observer's
character rank. -/
theorem observerTemporalDimension_le_observerFinrank
    {I O : Type*} [Fintype I]
    [AddCommGroup O] [Module ℚ O] [FiniteDimensional ℚ O]
    (jet : ℕ → I → ℂ)
    (observe : O →ₗ[ℚ] ProjectiveRationalCharacter I)
    (r : ℕ) :
    observerTemporalDimension jet observe r ≤
      Module.finrank ℚ O :=
  (observerProjectiveJetMap jet observe r).finrank_range_le

/-- An injective observer carrier has at most the complete projective
spectral dimension. -/
theorem observerTemporalDimension_le_card_sub_one
    {I O : Type*} [Fintype I] [Nonempty I]
    [AddCommGroup O] [Module ℚ O] [FiniteDimensional ℚ O]
    (jet : ℕ → I → ℂ)
    (observe : O →ₗ[ℚ] ProjectiveRationalCharacter I)
    (hobserve : Function.Injective observe)
    (r : ℕ) :
    observerTemporalDimension jet observe r ≤
      Fintype.card I - 1 := by
  calc
    observerTemporalDimension jet observe r ≤
        Module.finrank ℚ O :=
      observerTemporalDimension_le_observerFinrank jet observe r
    _ ≤ Module.finrank ℚ (ProjectiveRationalCharacter I) :=
      observe.finrank_le_finrank_of_injective hobserve
    _ = Fintype.card I - 1 :=
      finrank_projectiveRationalCharacter I

end

end GaloisForLFunctions.HTGeometry
