import GaloisForLFunctions.HTGeometry.MultipleGammaPeriodActionLawstack

open Set Topology Complex ContinuousMonoidHom QuotientAddGroup

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Largest real vector subspace contained in an additive subgroup. For a closed subgroup of a
finite-dimensional real vector group, this is its identity-component Lie algebra. -/
def addSubgroupRealVectorPart {V : Type*} [AddCommGroup V] [Module ℝ V]
    (H : AddSubgroup V) : Submodule ℝ V where
  carrier := {x | ∀ r : ℝ, r • x ∈ H}
  zero_mem' := by
    intro r
    simp
  add_mem' := by
    intro x y hx hy r
    rw [smul_add]
    exact H.add_mem (hx r) (hy r)
  smul_mem' := by
    intro a x hx r
    rw [smul_smul]
    exact hx (r * a)

/-- Real axis in `C`, as a literal real submodule. -/
abbrev complexRealAxis : Submodule ℝ ℂ := Complex.imCLM.ker

lemma half_not_mem_multipleGammaIntegerPeriods :
    (1 / 2 : ℝ) ∉ multipleGammaIntegerPeriods := by
  rintro ⟨k, hk⟩
  simp only [zsmul_eq_mul, mul_one] at hk
  have hk2 : (2 : ℝ) * k = 1 := by linarith
  have hkZ : 2 * k = 1 := by exact_mod_cast hk2
  omega

theorem realVectorPart_complexAxes_top_integer :
    addSubgroupRealVectorPart
      (complexAxisPeriodSubgroup ⊤ multipleGammaIntegerPeriods) = complexRealAxis := by
  ext z
  constructor
  · intro hz
    change ∀ r : ℝ, r • z ∈
      complexAxisPeriodSubgroup ⊤ multipleGammaIntegerPeriods at hz
    change z.im = 0
    by_contra him
    have hs := hz (1 / (2 * z.im))
    change ((1 / (2 * z.im)) • z).re ∈ (⊤ : AddSubgroup ℝ) ∧
      ((1 / (2 * z.im)) • z).im ∈ multipleGammaIntegerPeriods at hs
    have hval : ((1 / (2 * z.im)) • z).im = (1 / 2 : ℝ) := by
      simp
      field_simp [him]
    rw [hval] at hs
    exact half_not_mem_multipleGammaIntegerPeriods hs.2
  · intro hz
    change ∀ r : ℝ, r • z ∈
      complexAxisPeriodSubgroup ⊤ multipleGammaIntegerPeriods
    intro r
    change (r • z).re ∈ (⊤ : AddSubgroup ℝ) ∧
      (r • z).im ∈ multipleGammaIntegerPeriods
    change z.im = 0 at hz
    constructor
    · trivial
    · simp [hz, multipleGammaIntegerPeriods]

theorem realVectorPart_complexAxes_integer_integer :
    addSubgroupRealVectorPart
      (complexAxisPeriodSubgroup multipleGammaIntegerPeriods multipleGammaIntegerPeriods) = ⊥ := by
  ext z
  constructor
  · intro hz
    change ∀ r : ℝ, r • z ∈
      complexAxisPeriodSubgroup multipleGammaIntegerPeriods multipleGammaIntegerPeriods at hz
    rw [Submodule.mem_bot]
    apply Complex.ext
    · by_contra hre
      have hre0 : z.re ≠ 0 := by simpa using hre
      have hs := hz (1 / (2 * z.re))
      change ((1 / (2 * z.re)) • z).re ∈ multipleGammaIntegerPeriods ∧
        ((1 / (2 * z.re)) • z).im ∈ multipleGammaIntegerPeriods at hs
      have hval : ((1 / (2 * z.re)) • z).re = (1 / 2 : ℝ) := by
        simp
        field_simp [hre0]
      rw [hval] at hs
      exact half_not_mem_multipleGammaIntegerPeriods hs.1
    · by_contra him
      have him0 : z.im ≠ 0 := by simpa using him
      have hs := hz (1 / (2 * z.im))
      change ((1 / (2 * z.im)) • z).re ∈ multipleGammaIntegerPeriods ∧
        ((1 / (2 * z.im)) • z).im ∈ multipleGammaIntegerPeriods at hs
      have hval : ((1 / (2 * z.im)) • z).im = (1 / 2 : ℝ) := by
        simp
        field_simp [him0]
      rw [hval] at hs
      exact half_not_mem_multipleGammaIntegerPeriods hs.2
  · intro hz
    rw [Submodule.mem_bot] at hz
    subst z
    exact (addSubgroupRealVectorPart
      (complexAxisPeriodSubgroup multipleGammaIntegerPeriods
        multipleGammaIntegerPeriods)).zero_mem

theorem complexRealAxis_finrank : Module.finrank ℝ complexRealAxis = 1 := by
  have h := Complex.imCLM.toLinearMap.finrank_range_add_finrank_ker
  have hrange : Complex.imCLM.toLinearMap.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro x
    exact ⟨(x : ℂ) * Complex.I, by simp⟩
  rw [hrange] at h
  have h' : 1 + Module.finrank ℝ complexRealAxis = 2 := by
    simpa [complexRealAxis, Complex.finrank_real_complex] using h
  omega

/-- Lie dimension of the Hausdorff reflection `C / closure(H)`, computed from its literal
ambient Lie algebra quotient. -/
noncomputable def complexHausdorffObserverDimension (H : AddSubgroup ℂ) : ℕ :=
  Module.finrank ℝ ℂ - Module.finrank ℝ (addSubgroupRealVectorPart H.topologicalClosure)

theorem finiteMultipleGammaHausdorffObserverDimension (m : ℕ+) :
    complexHausdorffObserverDimension (finiteMultipleGammaPeriodSubgroup m) = 1 := by
  rw [complexHausdorffObserverDimension,
    finiteMultipleGammaPeriodSubgroup_topologicalClosure,
    realVectorPart_complexAxes_top_integer, complexRealAxis_finrank]
  simp [Complex.finrank_real_complex]

theorem boundaryMultipleGammaPeriodSubgroup_topologicalClosure :
    boundaryMultipleGammaPeriodSubgroup.topologicalClosure =
      boundaryMultipleGammaPeriodSubgroup := by
  apply SetLike.coe_injective
  simpa only [AddSubgroup.topologicalClosure_coe] using
    boundaryMultipleGammaPeriodSubgroup_isClosed.closure_eq

theorem boundaryMultipleGammaHausdorffObserverDimension :
    complexHausdorffObserverDimension boundaryMultipleGammaPeriodSubgroup = 2 := by
  rw [complexHausdorffObserverDimension,
    boundaryMultipleGammaPeriodSubgroup_topologicalClosure,
    boundaryMultipleGammaPeriodSubgroup_eq_axes,
    realVectorPart_complexAxes_integer_integer]
  simp [Complex.finrank_real_complex]

/-! ## Universal factorization and exact observer models -/

/-- The boundary Hausdorff reflection is the same two-torus as its already Hausdorff coarse
quotient. -/
def boundaryMultipleGammaHausdorffObserverEquivTorus :
    (ℂ ⧸ boundaryMultipleGammaPeriodSubgroup.topologicalClosure) ≃ₜ+
      (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) := by
  rw [boundaryMultipleGammaPeriodSubgroup_topologicalClosure]
  exact boundaryMultipleGammaCoarseQuotientEquivTorus

/-- Every Hausdorff-valued continuous additive observer of a finite coarse quotient factors
uniquely through its circle Hausdorff reflection. -/
theorem finiteMultipleGammaHausdorffObserver_universal
    (m : ℕ+) {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y]
    [IsTopologicalAddGroup Y] [T2Space Y]
    (f : (ℂ ⧸ finiteMultipleGammaPeriodSubgroup m) →ₜ+ Y) :
    ∃! g : finiteMultipleGammaHausdorffObserver m →ₜ+ Y,
      g.comp (hausdorffReflectionMap (finiteMultipleGammaPeriodSubgroup m)) = f := by
  exact hausdorffReflection_universal (finiteMultipleGammaPeriodSubgroup m) f

/-- Every Hausdorff-valued continuous additive observer of the boundary quotient factors uniquely
through its (unchanged) Hausdorff reflection. -/
theorem boundaryMultipleGammaHausdorffObserver_universal
    {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y]
    [IsTopologicalAddGroup Y] [T2Space Y]
    (f : boundaryMultipleGammaCoarseQuotient →ₜ+ Y) :
    ∃! g : (ℂ ⧸ boundaryMultipleGammaPeriodSubgroup.topologicalClosure) →ₜ+ Y,
      g.comp (hausdorffReflectionMap boundaryMultipleGammaPeriodSubgroup) = f := by
  exact hausdorffReflection_universal boundaryMultipleGammaPeriodSubgroup f

/-- The boundary Hausdorff-reflection map has zero kernel. -/
theorem boundaryMultipleGammaHausdorffReflectionMap_ker_eq_bot :
    (hausdorffReflectionMap boundaryMultipleGammaPeriodSubgroup).ker = ⊥ := by
  rw [hausdorffReflectionMap_ker, closureModuloSubgroup,
    boundaryMultipleGammaPeriodSubgroup_topologicalClosure]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [AddSubgroup.mem_bot]
    exact (QuotientAddGroup.eq_zero_iff y).mpr hy
  · intro hx
    rw [AddSubgroup.mem_bot] at hx
    subst x
    exact ⟨0, boundaryMultipleGammaPeriodSubgroup.zero_mem, by simp⟩

/-! ## Three-way rank conservation -/

theorem finiteMultipleGammaDADepth_add_observerDimension (m : ℕ+) :
    multipleEllipticGammaTransverseDADepth
        (finiteMultipleGammaFunctionPeriods m) (finiteMultipleGammaFunctionPeriods_im_pos m) +
      complexHausdorffObserverDimension (finiteMultipleGammaPeriodSubgroup m) = 2 := by
  rw [finiteMultipleGammaTransverseDADepth,
    finiteMultipleGammaHausdorffObserverDimension]

theorem boundaryMultipleGammaDADepth_add_observerDimension :
    multipleEllipticGammaTransverseDADepth
        boundaryMultipleGammaFunctionPeriods boundaryMultipleGammaFunctionPeriods_im_pos +
      complexHausdorffObserverDimension boundaryMultipleGammaPeriodSubgroup = 2 := by
  rw [boundaryMultipleGammaTransverseDADepth,
    boundaryMultipleGammaHausdorffObserverDimension]

theorem finiteMultipleGammaObserverDimension_sub_stabilizerRank (m : ℕ+) (z : ℂ) :
    complexHausdorffObserverDimension (finiteMultipleGammaPeriodSubgroup m) -
      markedStabilizerRank (finiteMultipleGammaPeriodMap m) z = 1 := by
  rw [finiteMultipleGammaHausdorffObserverDimension,
    finiteMultipleGammaStabilizerRank_eq_zero]

theorem boundaryMultipleGammaObserverDimension_sub_stabilizerRank (z : ℂ) :
    complexHausdorffObserverDimension boundaryMultipleGammaPeriodSubgroup -
      markedStabilizerRank boundaryMultipleGammaPeriodMap z = 1 := by
  rw [boundaryMultipleGammaHausdorffObserverDimension,
    boundaryMultipleGammaStabilizerRank_eq_one]

/-- Corollary 3.1: exact three-organ ledger over every finite stage and the boundary. -/
theorem multipleGammaThreeWayRankConservation :
    (∀ (m : ℕ+) (z : ℂ),
      multipleEllipticGammaTransverseDADepth
          (finiteMultipleGammaFunctionPeriods m) (finiteMultipleGammaFunctionPeriods_im_pos m) +
          markedStabilizerRank (finiteMultipleGammaPeriodMap m) z = 1 ∧
      multipleEllipticGammaTransverseDADepth
          (finiteMultipleGammaFunctionPeriods m) (finiteMultipleGammaFunctionPeriods_im_pos m) +
          complexHausdorffObserverDimension (finiteMultipleGammaPeriodSubgroup m) = 2 ∧
      complexHausdorffObserverDimension (finiteMultipleGammaPeriodSubgroup m) -
          markedStabilizerRank (finiteMultipleGammaPeriodMap m) z = 1) ∧
    (∀ z : ℂ,
      multipleEllipticGammaTransverseDADepth
          boundaryMultipleGammaFunctionPeriods boundaryMultipleGammaFunctionPeriods_im_pos +
          markedStabilizerRank boundaryMultipleGammaPeriodMap z = 1 ∧
      multipleEllipticGammaTransverseDADepth
          boundaryMultipleGammaFunctionPeriods boundaryMultipleGammaFunctionPeriods_im_pos +
          complexHausdorffObserverDimension boundaryMultipleGammaPeriodSubgroup = 2 ∧
      complexHausdorffObserverDimension boundaryMultipleGammaPeriodSubgroup -
          markedStabilizerRank boundaryMultipleGammaPeriodMap z = 1) := by
  constructor
  · intro m z
    exact ⟨finiteMultipleGammaDADepth_add_stabilizerRank m z,
      finiteMultipleGammaDADepth_add_observerDimension m,
      finiteMultipleGammaObserverDimension_sub_stabilizerRank m z⟩
  · intro z
    exact ⟨boundaryMultipleGammaDADepth_add_stabilizerRank z,
      boundaryMultipleGammaDADepth_add_observerDimension,
      boundaryMultipleGammaObserverDimension_sub_stabilizerRank z⟩

end
end GaloisForLFunctions.HTGeometry
