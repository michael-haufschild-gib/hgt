import GaloisForLFunctions.HTGeometry.ManifoldProductOrientation
import DifferentialGeometry.Tensor.Exterior.Pullback

/-!
# Fubini's theorem for product forms on closed oriented manifolds

For closed oriented manifolds `M₁, M₂` of dimensions `m, n ≥ 1` and top forms `γ` on `M₁`, `η` on
`M₂`, the product form `π₁*γ ∧ π₂*η` on `M₁ × M₂` (`productForm`) satisfies

`∫_{M₁×M₂} π₁*γ ∧ π₂*η = (∫_{M₁} γ)(∫_{M₂} η)`   (`topFormIntegral_productForm`),

for the product orientation, the product Haar measure and the concatenated frame
`(b₁, 0), (0, b₂)` (`splitFrame`).

* **Split wedge evaluation.**  On the concatenated frame the wedge of a form pulled back from the
  first factor with one pulled back from the second is the product of the evaluations: in the
  shuffle expansion every shuffle moving a first-factor slot into the second factor feeds a zero
  vector to the first form (`wedgeProduct_fst_snd_splitFrame`).
* **Product charts.**  The inverse tangent trivialization of a product chart is the product of the
  factor ones (`symmL_prod`), so chart values of pullbacks along the projections are the factor
  chart values composed with the projections, and chart densities multiply
  (`chartDensity_productForm`).
* **Fubini.**  Decomposing with the products `ρ_p(z₁)σ_q(z₂)` of the chart partitions, each piece
  is a chart integral in a product chart, which factorises by Fubini on the product of the chart
  targets (`chartIntegral_weighted_productForm`).
-/

open ContinuousAlternatingMap

namespace GaloisForLFunctions.HTGeometry

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] {m n : ℕ}

/-- The concatenated frame `(b₁, 0), …, (0, b₂)` of `E₁ × E₂`. -/
def splitFrame (b₁ : Fin m → E₁) (b₂ : Fin n → E₂) : Fin (m + n) → E₁ × E₂ :=
  fun i => Sum.elim (fun i => (b₁ i, (0 : E₂))) (fun j => ((0 : E₁), b₂ j)) (finSumFinEquiv.symm i)

omit [NormedSpace ℝ E₁] [NormedSpace ℝ E₂] in
theorem splitFrame_comp_finSumFinEquiv (b₁ : Fin m → E₁) (b₂ : Fin n → E₂) :
    splitFrame b₁ b₂ ∘ finSumFinEquiv =
      Sum.elim (fun i => (b₁ i, (0 : E₂))) (fun j => ((0 : E₁), b₂ j)) := by
  funext i
  simp [splitFrame]

/-- **Split wedge evaluation**: on the concatenated frame, the wedge of a form pulled back from the
first factor with one pulled back from the second is the product of the evaluations. -/
theorem wedgeProduct_fst_snd_splitFrame (A : E₁ [⋀^Fin m]→L[ℝ] ℝ) (B : E₂ [⋀^Fin n]→L[ℝ] ℝ)
    (b₁ : Fin m → E₁) (b₂ : Fin n → E₂) :
    wedgeProduct (A.compContinuousLinearMap (ContinuousLinearMap.fst ℝ E₁ E₂))
      (B.compContinuousLinearMap (ContinuousLinearMap.snd ℝ E₁ E₂))
      (ContinuousLinearMap.mul ℝ ℝ) (splitFrame b₁ b₂) = A b₁ * B b₂ := by
  classical
  set w := Sum.elim (fun i => (b₁ i, (0 : E₂))) (fun j => ((0 : E₁), b₂ j)) with hw
  rw [wedge_product_def, uncurryFinAdd, ContinuousAlternatingMap.domDomCongr_apply,
    splitFrame_comp_finSumFinEquiv, uncurrySum_apply, _root_.sum_apply]
  refine (Finset.sum_eq_single (Quotient.mk'' 1) ?_ ?_).trans ?_
  · intro σ _ hσ
    induction σ using Quotient.inductionOn' with
    | h τ =>
      rw [uncurrySum_summand_eval]
      have hnot : ¬ Set.MapsTo τ (Set.range Sum.inl) (Set.range Sum.inl) := by
        intro hmaps
        apply hσ
        have hmem := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hmaps
        refine Quotient.sound' ?_
        show (QuotientGroup.leftRel _).r τ 1
        rw [QuotientGroup.leftRel_apply]
        simpa using inv_mem hmem
      rw [Set.MapsTo] at hnot
      push Not at hnot
      obtain ⟨x, ⟨i, rfl⟩, hi⟩ := hnot
      obtain ⟨j, hj⟩ : ∃ j, τ (Sum.inl i) = Sum.inr j := by
        rcases h : τ (Sum.inl i) with a | j
        · exact absurd ⟨a, h.symm⟩ hi
        · exact ⟨j, rfl⟩
      have hzero : A (Prod.fst ∘ fun k => Sum.elim (fun i => (b₁ i, (0 : E₂)))
          (fun j => ((0 : E₁), b₂ j)) (τ (Sum.inl k))) = 0 :=
        A.map_coord_zero i (by simp [hj])
      simp only [ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
        compContinuousLinearMap_apply, ContinuousLinearMap.mul_apply']
      simp only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] at *
      rw [hzero, zero_mul, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
  · rw [uncurrySum_summand_eval]
    simp only [Equiv.Perm.coe_one, id_eq, Equiv.Perm.sign_one, one_smul,
      ContinuousLinearMap.compContinuousAlternatingMap₂_apply, compContinuousLinearMap_apply,
      ContinuousLinearMap.mul_apply']
    rfl

section Charts

open Manifold Bundle Set
open scoped Manifold ContDiff

variable {H₁ H₂ : Type*} [TopologicalSpace H₁] [TopologicalSpace H₂]
  {I₁ : ModelWithCorners ℝ E₁ H₁} {I₂ : ModelWithCorners ℝ E₂ H₂}
  {M₁ M₂ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]

/-- Tangent coordinate changes between product charts are products. -/
theorem tangentCoordChange_prod_general (x y z : M₁ × M₂)
    (hzx : z ∈ (chartAt (ModelProd H₁ H₂) x).source)
    (hzy : z ∈ (chartAt (ModelProd H₁ H₂) y).source) :
    tangentCoordChange (I₁.prod I₂) x y z =
      (tangentCoordChange I₁ x.1 y.1 z.1).prodMap (tangentCoordChange I₂ x.2 y.2 z.2) := by
  have hx' : z.1 ∈ (chartAt H₁ x.1).source ∧ z.2 ∈ (chartAt H₂ x.2).source := by
    simpa only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source, Set.mem_prod]
      using hzx
  have hy' : z.1 ∈ (chartAt H₁ y.1).source ∧ z.2 ∈ (chartAt H₂ y.2).source := by
    simpa only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source, Set.mem_prod]
      using hzy
  have hz₁ : z.1 ∈ (extChartAt I₁ x.1).source ∩ (extChartAt I₁ y.1).source :=
    ⟨by simpa only [extChartAt_source] using hx'.1, by simpa only [extChartAt_source] using hy'.1⟩
  have hz₂ : z.2 ∈ (extChartAt I₂ x.2).source ∩ (extChartAt I₂ y.2).source :=
    ⟨by simpa only [extChartAt_source] using hx'.2, by simpa only [extChartAt_source] using hy'.2⟩
  have hzp : z ∈ (extChartAt (I₁.prod I₂) x).source ∩ (extChartAt (I₁.prod I₂) y).source :=
    ⟨by simpa only [extChartAt_source] using hzx, by simpa only [extChartAt_source] using hzy⟩
  refine ((I₁.prod I₂).uniqueDiffWithinAt_image (x := (chartAt (ModelProd H₁ H₂) x) z)).eq
    (hasFDerivWithinAt_tangentCoordChange (I := I₁.prod I₂) hzp) ?_
  have h₁ := hasFDerivWithinAt_tangentCoordChange (I := I₁) hz₁
  have h₂ := hasFDerivWithinAt_tangentCoordChange (I := I₂) hz₂
  have hs₁ : Prod.fst '' (Set.range (I₁.prod I₂)) = Set.range I₁ := by
    rw [ModelWithCorners.range_prod]
    exact Set.fst_image_prod (Set.range I₁) ⟨I₂ ((chartAt H₂ y.2) y.2), Set.mem_range_self _⟩
  have hs₂ : Prod.snd '' (Set.range (I₁.prod I₂)) = Set.range I₂ := by
    rw [ModelWithCorners.range_prod]
    exact Set.snd_image_prod ⟨I₁ ((chartAt H₁ y.1) y.1), Set.mem_range_self _⟩ (Set.range I₂)
  rw [← hs₁] at h₁
  rw [← hs₂] at h₂
  have h := HasFDerivWithinAt.prodMap
    (p := (extChartAt I₁ x.1 z.1, extChartAt I₂ x.2 z.2)) h₁ h₂
  have hfun : ((extChartAt (I₁.prod I₂) y) ∘ (extChartAt (I₁.prod I₂) x).symm) =
      Prod.map ((extChartAt I₁ y.1) ∘ (extChartAt I₁ x.1).symm)
        ((extChartAt I₂ y.2) ∘ (extChartAt I₂ x.2).symm) := by
    funext q
    simp only [Function.comp_apply, extChartAt_prod, PartialEquiv.prod_symm,
      PartialEquiv.prod_coe]
    rfl
  have hpt : extChartAt (I₁.prod I₂) x z = (extChartAt I₁ x.1 z.1, extChartAt I₂ x.2 z.2) := by
    simp only [extChartAt_prod, PartialEquiv.prod_coe]
  rw [← hfun, ← hpt] at h
  exact h

/-- The inverse tangent trivialization of a product chart is the product of the factor ones. -/
theorem symmL_prod (p z : M₁ × M₂) (hz : z ∈ (chartAt (ModelProd H₁ H₂) p).source) :
    (trivializationAt (E₁ × E₂) (TangentSpace (I₁.prod I₂)) p).symmL ℝ z =
      ((trivializationAt E₁ (TangentSpace I₁) p.1).symmL ℝ z.1).prodMap
        ((trivializationAt E₂ (TangentSpace I₂) p.2).symmL ℝ z.2) := by
  have hz' : z.1 ∈ (chartAt H₁ p.1).source ∧ z.2 ∈ (chartAt H₂ p.2).source := by
    simpa only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source, Set.mem_prod]
      using hz
  rw [TangentBundle.symmL_trivializationAt_eq_core hz,
    TangentBundle.symmL_trivializationAt_eq_core hz'.1,
    TangentBundle.symmL_trivializationAt_eq_core hz'.2]
  exact tangentCoordChange_prod_general p z z hz (mem_chart_source _ z)

/-- The chart value of a form pulled back from the first factor. -/
theorem formChartValue_pullback_fst {k : ℕ} (γ : DifferentialGeometry.DifferentialForm I₁ M₁ k)
    (p z : M₁ × M₂) (hz : z ∈ (chartAt (ModelProd H₁ H₂) p).source) :
    formChartValue p (DifferentialGeometry.DifferentialForm.pullback Prod.fst
      (contMDiff_fst : ContMDiff (I₁.prod I₂) I₁ ∞ (Prod.fst : M₁ × M₂ → M₁)) γ) z =
      (formChartValue p.1 γ z.1).compContinuousLinearMap (ContinuousLinearMap.fst ℝ E₁ E₂) := by
  rw [formChartValue_eq, formChartValue_eq, symmL_prod p z hz]
  ext v
  simp [DifferentialGeometry.DifferentialForm.pullback]
  rfl

/-- The chart value of a form pulled back from the second factor. -/
theorem formChartValue_pullback_snd {k : ℕ} (η : DifferentialGeometry.DifferentialForm I₂ M₂ k)
    (p z : M₁ × M₂) (hz : z ∈ (chartAt (ModelProd H₁ H₂) p).source) :
    formChartValue p (DifferentialGeometry.DifferentialForm.pullback Prod.snd
      (contMDiff_snd : ContMDiff (I₁.prod I₂) I₂ ∞ (Prod.snd : M₁ × M₂ → M₂)) η) z =
      (formChartValue p.2 η z.2).compContinuousLinearMap (ContinuousLinearMap.snd ℝ E₁ E₂) := by
  rw [formChartValue_eq, formChartValue_eq, symmL_prod p z hz]
  ext v
  simp [DifferentialGeometry.DifferentialForm.pullback]
  rfl


/-- The chart value of a wedge product is the wedge product of the chart values. -/
theorem formChartValue_wedge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {k l : ℕ}
    (α : DifferentialGeometry.DifferentialForm I M k)
    (β : DifferentialGeometry.DifferentialForm I M l) (p z : M) :
    formChartValue p (DifferentialGeometry.DifferentialForm.wedge α β) z =
      wedgeProduct (formChartValue p α z) (formChartValue p β z) (ContinuousLinearMap.mul ℝ ℝ) := by
  rw [formChartValue_eq, formChartValue_eq, formChartValue_eq]
  exact DifferentialGeometry.DifferentialForm.wedge_product_compContinuousLinearMap _ _ _

/-- The product form `π₁*γ ∧ π₂*η`. -/
noncomputable def productForm {k l : ℕ} (γ : DifferentialGeometry.DifferentialForm I₁ M₁ k)
    (η : DifferentialGeometry.DifferentialForm I₂ M₂ l) :
    DifferentialGeometry.DifferentialForm (I₁.prod I₂) (M₁ × M₂) (k + l) :=
  DifferentialGeometry.DifferentialForm.wedge
    (DifferentialGeometry.DifferentialForm.pullback Prod.fst
      (contMDiff_fst : ContMDiff (I₁.prod I₂) I₁ ∞ (Prod.fst : M₁ × M₂ → M₁)) γ)
    (DifferentialGeometry.DifferentialForm.pullback Prod.snd
      (contMDiff_snd : ContMDiff (I₁.prod I₂) I₂ ∞ (Prod.snd : M₁ × M₂ → M₂)) η)

/-- In a product chart the product form evaluates on the concatenated frame to the product of
the factor evaluations. -/
theorem formChartValue_productForm_splitFrame {k l : ℕ}
    (γ : DifferentialGeometry.DifferentialForm I₁ M₁ k)
    (η : DifferentialGeometry.DifferentialForm I₂ M₂ l) (p z : M₁ × M₂)
    (hz : z ∈ (chartAt (ModelProd H₁ H₂) p).source) (b₁ : Fin k → E₁) (b₂ : Fin l → E₂) :
    formChartValue p (productForm γ η) z (splitFrame b₁ b₂) =
      formChartValue p.1 γ z.1 b₁ * formChartValue p.2 η z.2 b₂ := by
  rw [productForm, formChartValue_wedge, formChartValue_pullback_fst γ p z hz,
    formChartValue_pullback_snd η p z hz]
  exact wedgeProduct_fst_snd_splitFrame _ _ b₁ b₂


/-! ## Fubini for product forms -/

omit [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂] in
theorem extChartAt_prod_target (p : M₁ × M₂) :
    (extChartAt (I₁.prod I₂) p).target =
      (extChartAt I₁ p.1).target ×ˢ (extChartAt I₂ p.2).target := by
  rw [extChartAt_prod, PartialEquiv.prod_target]

omit [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂] in
theorem extChartAt_prod_symm_apply (p : M₁ × M₂) (y : E₁ × E₂) :
    (extChartAt (I₁.prod I₂) p).symm y =
      ((extChartAt I₁ p.1).symm y.1, (extChartAt I₂ p.2).symm y.2) := by
  rw [extChartAt_prod, PartialEquiv.prod_symm, PartialEquiv.prod_coe]

variable [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] {m n : ℕ} [NeZero m] [NeZero n]

/-- The chart density of the product form in a product chart is the product of the factor
densities. -/
theorem chartDensity_productForm (o₁ : DifferentialGeometry.ManifoldOrientation I₁ M₁ m)
    (o₂ : DifferentialGeometry.ManifoldOrientation I₂ M₂ n) (e₁ : Orientation ℝ E₁ (Fin m))
    (e₂ : Orientation ℝ E₂ (Fin n)) (b₁ : Fin m → E₁) (b₂ : Fin n → E₂)
    (γ : DifferentialGeometry.DifferentialForm I₁ M₁ m)
    (η : DifferentialGeometry.DifferentialForm I₂ M₂ n) (p : M₁ × M₂) {y : E₁ × E₂}
    (hy : y ∈ (extChartAt (I₁.prod I₂) p).target) :
    chartDensity (prodManifoldOrientation o₁ o₂)
        (prodOrientation o₁.dimension_eq o₂.dimension_eq e₁ e₂) (splitFrame b₁ b₂) p
        (productForm γ η) y =
      chartDensity o₁ e₁ b₁ p.1 γ y.1 * chartDensity o₂ e₂ b₂ p.2 η y.2 := by
  have hz : (extChartAt (I₁.prod I₂) p).symm y ∈ (chartAt (ModelProd H₁ H₂) p).source := by
    rw [← extChartAt_source (I := I₁.prod I₂)]
    exact (extChartAt (I₁.prod I₂) p).map_target hy
  unfold chartDensity
  rw [formChartValue_productForm_splitFrame γ η p _ hz, chartSign_prodManifoldOrientation,
    extChartAt_prod_symm_apply]
  ring

/-- The product of two smooth weights. -/
noncomputable def prodWeight (f₁ : C^∞⟮I₁, M₁; ℝ⟯) (f₂ : C^∞⟮I₂, M₂; ℝ⟯) :
    C^∞⟮I₁.prod I₂, M₁ × M₂; ℝ⟯ :=
  ⟨fun z => f₁ z.1 * f₂ z.2,
    (f₁.contMDiff.comp contMDiff_fst).mul (f₂.contMDiff.comp contMDiff_snd)⟩

omit [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂] [FiniteDimensional ℝ E₁]
  [FiniteDimensional ℝ E₂] in
@[simp] theorem prodWeight_apply (f₁ : C^∞⟮I₁, M₁; ℝ⟯) (f₂ : C^∞⟮I₂, M₂; ℝ⟯) (z : M₁ × M₂) :
    prodWeight f₁ f₂ z = f₁ z.1 * f₂ z.2 := rfl

variable [MeasurableSpace E₁] [BorelSpace E₁] [MeasurableSpace E₂] [BorelSpace E₂]

/-- **Chart Fubini**: a product-weighted product form integrates in a product chart to the
product of the weighted factor integrals. -/
theorem chartIntegral_weighted_productForm [I₁.Boundaryless] [I₂.Boundaryless]
    (μ₁ : MeasureTheory.Measure E₁) (μ₂ : MeasureTheory.Measure E₂)
    [MeasureTheory.SigmaFinite μ₁] [MeasureTheory.SigmaFinite μ₂]
    (o₁ : DifferentialGeometry.ManifoldOrientation I₁ M₁ m)
    (o₂ : DifferentialGeometry.ManifoldOrientation I₂ M₂ n) (e₁ : Orientation ℝ E₁ (Fin m))
    (e₂ : Orientation ℝ E₂ (Fin n)) (b₁ : Fin m → E₁) (b₂ : Fin n → E₂)
    (γ : DifferentialGeometry.DifferentialForm I₁ M₁ m)
    (η : DifferentialGeometry.DifferentialForm I₂ M₂ n) (f₁ : C^∞⟮I₁, M₁; ℝ⟯)
    (f₂ : C^∞⟮I₂, M₂; ℝ⟯) (p₁ : M₁) (p₂ : M₂) :
    chartIntegral (μ₁.prod μ₂) (prodManifoldOrientation o₁ o₂)
        (prodOrientation o₁.dimension_eq o₂.dimension_eq e₁ e₂) (splitFrame b₁ b₂) (p₁, p₂)
        (weightedForm (prodWeight f₁ f₂) (productForm γ η)) =
      chartIntegral μ₁ o₁ e₁ b₁ p₁ (weightedForm f₁ γ) *
        chartIntegral μ₂ o₂ e₂ b₂ p₂ (weightedForm f₂ η) := by
  unfold chartIntegral
  rw [extChartAt_prod_target, ← MeasureTheory.setIntegral_prod_mul]
  refine MeasureTheory.setIntegral_congr_fun
    ((isOpen_extChartAt_target p₁).prod (isOpen_extChartAt_target p₂)).measurableSet
    fun y hy => ?_
  have hy' : y ∈ (extChartAt (I₁.prod I₂) (p₁, p₂)).target := by
    rw [extChartAt_prod_target]
    exact hy
  rw [chartDensity_weightedForm, chartDensity_productForm o₁ o₂ e₁ e₂ b₁ b₂ γ η _ hy',
    chartDensity_weightedForm, chartDensity_weightedForm, extChartAt_prod_symm_apply,
    prodWeight_apply]
  ring


theorem differentialForm_sum_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {k : ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → DifferentialGeometry.DifferentialForm I M k) (z : M) :
    (∑ i ∈ s, f i) z = ∑ i ∈ s, f i z := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      DifferentialGeometry.DifferentialForm.add_apply, ih]

theorem sum_chartPartition_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [CompactSpace M] (z : M) :
    ∑ p ∈ (finite_chartPartition_support (I := I) (M := M)).toFinset,
      chartPartition I M p z = 1 := by
  rw [← (chartPartition I M).sum_eq_one (Set.mem_univ z)]
  refine (finsum_eq_sum_of_support_subset _ fun p hp => ?_).symm
  exact (finite_chartPartition_support (I := I) (M := M)).mem_toFinset.mpr ⟨_, hp⟩

/-- **Fubini for product forms**: `∫_{M₁×M₂} π₁*γ ∧ π₂*η = (∫_{M₁} γ)(∫_{M₂} η)`, for the product
orientation, the product Haar measure and the concatenated frame. -/
theorem topFormIntegral_productForm [T2Space M₁] [CompactSpace M₁] [T2Space M₂]
    [CompactSpace M₂] [I₁.Boundaryless] [I₂.Boundaryless]
    (μ₁ : MeasureTheory.Measure E₁) (μ₂ : MeasureTheory.Measure E₂) [μ₁.IsAddHaarMeasure]
    [μ₂.IsAddHaarMeasure] (o₁ : DifferentialGeometry.ManifoldOrientation I₁ M₁ m)
    (o₂ : DifferentialGeometry.ManifoldOrientation I₂ M₂ n) (e₁ : Orientation ℝ E₁ (Fin m))
    (e₂ : Orientation ℝ E₂ (Fin n)) (b₁ : Fin m → E₁) (b₂ : Fin n → E₂)
    (γ : DifferentialGeometry.DifferentialForm I₁ M₁ m)
    (η : DifferentialGeometry.DifferentialForm I₂ M₂ n) :
    topFormIntegral (μ₁.prod μ₂) (prodManifoldOrientation o₁ o₂)
        (prodOrientation o₁.dimension_eq o₂.dimension_eq e₁ e₂) (splitFrame b₁ b₂)
        (productForm γ η) =
      topFormIntegral μ₁ o₁ e₁ b₁ γ * topFormIntegral μ₂ o₂ e₂ b₂ η := by
  set S₁ := (finite_chartPartition_support (I := I₁) (M := M₁)).toFinset
  set S₂ := (finite_chartPartition_support (I := I₂) (M := M₂)).toFinset
  set ρ := chartPartition I₁ M₁
  set σ := chartPartition I₂ M₂
  have hdecomp : productForm γ η = ∑ pq ∈ S₁ ×ˢ S₂,
      weightedForm (prodWeight (ρ pq.1) (σ pq.2)) (productForm γ η) := by
    apply ContMDiffSection.ext
    intro z
    rw [differentialForm_sum_apply]
    simp only [weightedForm_apply, prodWeight_apply]
    rw [← Finset.sum_smul, Finset.sum_product]
    dsimp only
    rw [← Finset.sum_mul_sum, sum_chartPartition_apply, sum_chartPartition_apply, one_mul,
      one_smul]
  conv_lhs => rw [hdecomp]
  rw [topFormIntegral_sum, topFormIntegral_eq_sum μ₁, topFormIntegral_eq_sum μ₂,
    Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_congr rfl fun pq _ => ?_
  obtain ⟨p, q⟩ := pq
  have hK : IsClosed (tsupport (ρ p) ×ˢ tsupport (σ q)) :=
    (isClosed_tsupport _).prod (isClosed_tsupport _)
  have hKs : tsupport (ρ p) ×ˢ tsupport (σ q) ⊆ (extChartAt (I₁.prod I₂) (p, q)).source := by
    rw [extChartAt_prod, PartialEquiv.prod_source]
    exact Set.prod_mono (tsupport_chartPartition_subset p) (tsupport_chartPartition_subset q)
  have hsupp : ∀ z, weightedForm (prodWeight (ρ p) (σ q)) (productForm γ η) z ≠ 0 →
      z ∈ tsupport (ρ p) ×ˢ tsupport (σ q) := by
    intro z hz
    have hw : prodWeight (ρ p) (σ q) z ≠ 0 := fun h0 => hz (by rw [weightedForm_apply, h0,
      zero_smul])
    rw [prodWeight_apply] at hw
    exact ⟨subset_tsupport _ (left_ne_zero_of_mul hw), subset_tsupport _ (right_ne_zero_of_mul hw)⟩
  rw [topFormIntegral_eq_chartIntegral _ _ _ _ _ hK hKs hsupp]
  exact chartIntegral_weighted_productForm μ₁ μ₂ o₁ o₂ e₁ e₂ b₁ b₂ γ η (ρ p) (σ q) p q

end Charts

end GaloisForLFunctions.HTGeometry
