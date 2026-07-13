import GaloisForLFunctions.HTGeometry.MinimalTypeProjectiveForbiddenSeparation

namespace GaloisForLFunctions.HTGeometry

open Complex
open scoped BigOperators Topology

noncomputable section

/-- Finite complex shift configurations with the collision-free locus built into the type. -/
abbrev InjectiveShiftConfiguration (ι : Type*) [Fintype ι] :=
  {shift : ι → ℂ // Function.Injective shift}

/-- Configurations for which one fixed base row simultaneously regularizes and separates the
target projective parameters and avoids the finite frozen packet. -/
def projectiveGoodRowSet
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (C D : ℂ → ℂ) (forbidden : κ → ℂ) (z : ℂ) :
    Set (InjectiveShiftConfiguration ι) :=
  {shift | projectiveForbiddenSeparationProduct C D shift.1 forbidden z ≠ 0}

/-- The frozen-safe separation product depends continuously on the finite shift configuration. -/
theorem continuous_projectiveForbiddenSeparationProduct_configuration
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {C D : ℂ → ℂ} (hC : Continuous C) (hD : Continuous D)
    (forbidden : κ → ℂ) (z : ℂ) :
    Continuous (fun shift : ι → ℂ =>
      projectiveForbiddenSeparationProduct C D shift forbidden z) := by
  unfold projectiveForbiddenSeparationProduct projectiveSeparationProduct
  unfold projectiveShiftCollision
  fun_prop

/-- Good configurations for a fixed row form an open set. -/
theorem projectiveGoodRowSet_isOpen
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {C D : ℂ → ℂ} (hC : Continuous C) (hD : Continuous D)
    (forbidden : κ → ℂ) (z : ℂ) :
    IsOpen (projectiveGoodRowSet (ι := ι) (κ := κ) C D forbidden z) := by
  have hcontinuous : Continuous (fun shift : InjectiveShiftConfiguration ι =>
      projectiveForbiddenSeparationProduct C D shift.1 forbidden z) :=
    (continuous_projectiveForbiddenSeparationProduct_configuration hC hD forbidden z).comp
      continuous_subtype_val
  exact hcontinuous.isOpen_preimage {w : ℂ | w ≠ 0} isOpen_ne

/-- The good-row opens indexed by arbitrarily high rows cover the entire injective configuration
space. -/
theorem injectiveShiftConfigurations_covered_by_upper_projectiveGoodRows
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {p : ℂ} (hCp : C p = 0) {c : ℂ} (hCc : C c ≠ 0)
    (forbidden : κ → ℂ) (H : ℝ) :
    Set.univ ⊆ ⋃ z : {z : ℂ // H < z.im},
      projectiveGoodRowSet (ι := ι) (κ := κ) C D forbidden z.1 := by
  intro shift hshift
  have hne := projectiveForbiddenSeparationProduct_ne_zero
    hCmin hD hnoCommon hCp hCc shift.1 shift.2 forbidden
  obtain ⟨z, hzH, hz⟩ := exists_upper_ne_zero_of_differentiable_ne_zero
    (projectiveForbiddenSeparationProduct_differentiable hCmin.1 hD shift.1 forbidden)
    hne H
  exact Set.mem_iUnion.mpr ⟨⟨z, hzH⟩, hz⟩

/-- **Compact projective separation atlas.** Every compact patch of collision-free complex shift
configurations is covered by finitely many arbitrarily high rows, each carrying an open family of
simultaneously regular, target-separated, frozen-safe Nevanlinna parameter packets. -/
theorem compact_injectiveShiftPatch_finite_projectiveGoodRow_cover
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {p : ℂ} (hCp : C p = 0) {c : ℂ} (hCc : C c ≠ 0)
    (forbidden : κ → ℂ) (H : ℝ)
    {K : Set (InjectiveShiftConfiguration ι)} (hK : IsCompact K) :
    ∃ rows : Finset {z : ℂ // H < z.im},
      K ⊆ ⋃ z ∈ rows,
        projectiveGoodRowSet (ι := ι) (κ := κ) C D forbidden z.1 := by
  apply hK.elim_finite_subcover
    (fun z : {z : ℂ // H < z.im} =>
      projectiveGoodRowSet (ι := ι) (κ := κ) C D forbidden z.1)
  · intro z
    exact projectiveGoodRowSet_isOpen (ι := ι) (κ := κ)
      hCmin.1.continuous hD.continuous forbidden z.1
  · exact Set.Subset.trans (Set.subset_univ K)
      (injectiveShiftConfigurations_covered_by_upper_projectiveGoodRows (ι := ι) (κ := κ)
        hCmin hD hnoCommon hCp hCc forbidden H)

end
end GaloisForLFunctions.HTGeometry
