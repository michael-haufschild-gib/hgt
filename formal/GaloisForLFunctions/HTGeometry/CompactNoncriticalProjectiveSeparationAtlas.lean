import GaloisForLFunctions.HTGeometry.ProjectiveDerivativeNoncritical

namespace GaloisForLFunctions.HTGeometry

open Complex
open scoped BigOperators Topology

noncomputable section

/-- The complete finite row certificate: regularity, target-target separation, frozen avoidance,
and noncriticality of the affine projective parameter. -/
def noncriticalProjectiveSeparationProduct
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (C D : ℂ → ℂ) (shift : ι → ℂ) (forbidden : κ → ℂ) (z : ℂ) : ℂ :=
  projectiveForbiddenSeparationProduct C D shift forbidden z *
    ∏ i, projectiveDerivativeNumerator C D (z + shift i)

/-- The complete row certificate is entire in the base row. -/
theorem noncriticalProjectiveSeparationProduct_differentiable
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {C D : ℂ → ℂ} (hC : Differentiable ℂ C) (hD : Differentiable ℂ D)
    (shift : ι → ℂ) (forbidden : κ → ℂ) :
    Differentiable ℂ (noncriticalProjectiveSeparationProduct C D shift forbidden) := by
  unfold noncriticalProjectiveSeparationProduct
  apply Differentiable.mul
    (projectiveForbiddenSeparationProduct_differentiable hC hD shift forbidden)
  rw [show (fun z => ∏ i, projectiveDerivativeNumerator C D (z + shift i)) =
      ∏ i, (fun z => projectiveDerivativeNumerator C D (z + shift i)) by
    funext z
    simp only [Finset.prod_apply]]
  exact Differentiable.finsetProd fun i (_hi : i ∈ (Finset.univ : Finset ι)) =>
    (projectiveDerivativeNumerator_differentiable hC hD).comp
      (differentiable_id.add_const (shift i))

/-- The complete row certificate is not the zero entire function. -/
theorem noncriticalProjectiveSeparationProduct_ne_zero
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {p : ℂ} (hCp : C p = 0) {c : ℂ} (hCc : C c ≠ 0)
    (shift : ι → ℂ) (hshift : Function.Injective shift) (forbidden : κ → ℂ) :
    noncriticalProjectiveSeparationProduct C D shift forbidden ≠ 0 := by
  unfold noncriticalProjectiveSeparationProduct
  apply differentiable_mul_ne_zero
    (projectiveForbiddenSeparationProduct_differentiable hCmin.1 hD shift forbidden)
  · rw [show (fun z => ∏ i, projectiveDerivativeNumerator C D (z + shift i)) =
        ∏ i, (fun z => projectiveDerivativeNumerator C D (z + shift i)) by
      funext z
      simp only [Finset.prod_apply]]
    exact Differentiable.finsetProd fun i (_hi : i ∈ (Finset.univ : Finset ι)) =>
      (projectiveDerivativeNumerator_differentiable hCmin.1 hD).comp
        (differentiable_id.add_const (shift i))
  · exact projectiveForbiddenSeparationProduct_ne_zero
      hCmin hD hnoCommon hCp hCc shift hshift forbidden
  · apply differentiable_finset_prod_ne_zero Finset.univ
    · intro i hi
      exact (projectiveDerivativeNumerator_differentiable hCmin.1 hD).comp
        (differentiable_id.add_const (shift i))
    · intro i hi hzero
      apply projectiveDerivativeNumerator_ne_zero hCmin.1 hD hnoCommon hCp hCc
      funext z
      have := congrFun hzero (z - shift i)
      simpa using this

/-- Complete-good configurations for one fixed row. -/
def noncriticalProjectiveGoodRowSet
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (C D : ℂ → ℂ) (forbidden : κ → ℂ) (z : ℂ) :
    Set (InjectiveShiftConfiguration ι) :=
  {shift | noncriticalProjectiveSeparationProduct C D shift.1 forbidden z ≠ 0}

/-- The complete certificate depends continuously on the shift configuration. -/
theorem continuous_noncriticalProjectiveSeparationProduct_configuration
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {C D : ℂ → ℂ} (hC : Differentiable ℂ C) (hD : Differentiable ℂ D)
    (forbidden : κ → ℂ) (z : ℂ) :
    Continuous (fun shift : ι → ℂ =>
      noncriticalProjectiveSeparationProduct C D shift forbidden z) := by
  unfold noncriticalProjectiveSeparationProduct
  apply Continuous.mul
    (continuous_projectiveForbiddenSeparationProduct_configuration
      hC.continuous hD.continuous forbidden z)
  have hWcont := (projectiveDerivativeNumerator_differentiable hC hD).continuous
  fun_prop

/-- Complete-good configurations form an open set. -/
theorem noncriticalProjectiveGoodRowSet_isOpen
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {C D : ℂ → ℂ} (hC : Differentiable ℂ C) (hD : Differentiable ℂ D)
    (forbidden : κ → ℂ) (z : ℂ) :
    IsOpen (noncriticalProjectiveGoodRowSet (ι := ι) (κ := κ) C D forbidden z) := by
  have hcontinuous : Continuous (fun shift : InjectiveShiftConfiguration ι =>
      noncriticalProjectiveSeparationProduct C D shift.1 forbidden z) :=
    (continuous_noncriticalProjectiveSeparationProduct_configuration hC hD forbidden z).comp
      continuous_subtype_val
  exact hcontinuous.isOpen_preimage {w : ℂ | w ≠ 0} isOpen_ne

/-- The arbitrarily high complete-good row opens cover all injective configurations. -/
theorem injectiveShiftConfigurations_covered_by_upper_noncriticalProjectiveGoodRows
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {p : ℂ} (hCp : C p = 0) {c : ℂ} (hCc : C c ≠ 0)
    (forbidden : κ → ℂ) (H : ℝ) :
    Set.univ ⊆ ⋃ z : {z : ℂ // H < z.im},
      noncriticalProjectiveGoodRowSet (ι := ι) (κ := κ) C D forbidden z.1 := by
  intro shift hshift
  have hne := noncriticalProjectiveSeparationProduct_ne_zero
    hCmin hD hnoCommon hCp hCc shift.1 shift.2 forbidden
  obtain ⟨z, hzH, hz⟩ := exists_upper_ne_zero_of_differentiable_ne_zero
    (noncriticalProjectiveSeparationProduct_differentiable hCmin.1 hD shift.1 forbidden)
    hne H
  exact Set.mem_iUnion.mpr ⟨⟨z, hzH⟩, hz⟩

/-- **Compact noncritical projective separation atlas.** Every compact collision-free shift patch
has a finite open row atlas whose certificates include all hypotheses needed by the triangular
Nevanlinna jet conversion. -/
theorem compact_injectiveShiftPatch_finite_noncriticalProjectiveGoodRow_cover
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {p : ℂ} (hCp : C p = 0) {c : ℂ} (hCc : C c ≠ 0)
    (forbidden : κ → ℂ) (H : ℝ)
    {K : Set (InjectiveShiftConfiguration ι)} (hK : IsCompact K) :
    ∃ rows : Finset {z : ℂ // H < z.im},
      K ⊆ ⋃ z ∈ rows,
        noncriticalProjectiveGoodRowSet (ι := ι) (κ := κ) C D forbidden z.1 := by
  apply hK.elim_finite_subcover
    (fun z : {z : ℂ // H < z.im} =>
      noncriticalProjectiveGoodRowSet (ι := ι) (κ := κ) C D forbidden z.1)
  · intro z
    exact noncriticalProjectiveGoodRowSet_isOpen (ι := ι) (κ := κ)
      hCmin.1 hD forbidden z.1
  · exact Set.Subset.trans (Set.subset_univ K)
      (injectiveShiftConfigurations_covered_by_upper_noncriticalProjectiveGoodRows
        (ι := ι) (κ := κ) hCmin hD hnoCommon hCp hCc forbidden H)

/-- A complete-good row has nonzero affine projective derivative at every shifted target node. -/
theorem noncriticalProjectiveGoodRow_deriv_ne_zero
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {C D : ℂ → ℂ} (hC : Differentiable ℂ C) (hD : Differentiable ℂ D)
    (forbidden : κ → ℂ) {z : ℂ} {shift : InjectiveShiftConfiguration ι}
    (hgood : shift ∈ noncriticalProjectiveGoodRowSet
      (ι := ι) (κ := κ) C D forbidden z) :
    ∀ i, deriv (fun w => -D w / C w) (z + shift.1 i) ≠ 0 := by
  intro i
  change noncriticalProjectiveSeparationProduct C D shift.1 forbidden z ≠ 0 at hgood
  change projectiveForbiddenSeparationProduct C D shift.1 forbidden z *
    (∏ i, projectiveDerivativeNumerator C D (z + shift.1 i)) ≠ 0 at hgood
  have hforbidden : projectiveForbiddenSeparationProduct C D shift.1 forbidden z ≠ 0 := by
    intro hzero
    exact hgood (by rw [hzero, zero_mul])
  have hWprod : (∏ i, projectiveDerivativeNumerator C D (z + shift.1 i)) ≠ 0 := by
    intro hzero
    exact hgood (by rw [hzero, mul_zero])
  change projectiveSeparationProduct C D shift.1 z *
    (∏ x : ι × κ,
      (D (z + shift.1 x.1) + forbidden x.2 * C (z + shift.1 x.1))) ≠ 0 at hforbidden
  have hsep : projectiveSeparationProduct C D shift.1 z ≠ 0 := by
    intro hzero
    exact hforbidden (by rw [hzero, zero_mul])
  change (∏ j, C (z + shift.1 j)) *
    (∏ x : {x : ι × ι // x.1 ≠ x.2},
      projectiveShiftCollision C D (shift.1 x.1.1) (shift.1 x.1.2) z) ≠ 0 at hsep
  have hCprod : (∏ j, C (z + shift.1 j)) ≠ 0 := by
    intro hzero
    exact hsep (by rw [hzero, zero_mul])
  apply deriv_neg_div_ne_zero_of_projectiveDerivativeNumerator_ne_zero hC hD
  · exact (Finset.prod_ne_zero_iff.mp hCprod) i (Finset.mem_univ i)
  · exact (Finset.prod_ne_zero_iff.mp hWprod) i (Finset.mem_univ i)

end
end GaloisForLFunctions.HTGeometry
