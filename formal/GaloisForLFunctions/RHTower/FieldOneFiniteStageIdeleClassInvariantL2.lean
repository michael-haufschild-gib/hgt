import GaloisForLFunctions.RHTower.FieldOneFiniteStageModuleOneInvariantL2

/-!
# The module-one invariant part of the finite-stage idele-class `L²` space

This file transports the product-side fixed-point classification through the canonical
topological-group splitting

`C_S ≃ K_S × ℝ≥0ˣ`.

Consequently the literal `K_S`-fixed subspace of the split-Haar `L²(C_S)` is unitarily
equivalent to `L²(ℝ≥0ˣ)`.  This is the exact carrier identification used before the
Hardy--Titchmarsh and Sonin projections in the Connes--Consani semilocal construction.
-/

open scoped NNReal ENNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain MeasureTheory

@[simp] theorem fieldOneFiniteStageIdeleClassSplit_moduleOne
    (S : Finset (HeightOneSpectrum ℤ))
    (k : FieldOneFiniteStageModuleOneClass S) :
    fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv S k.1 = (k, 1) := by
  apply Prod.ext
  · apply Subtype.ext
    change k.1 *
      (fieldOneFiniteStagePositiveRealClassSection S
        (fieldOneFiniteStageIdeleClassUnitModule S k.1))⁻¹ = k.1
    rw [show fieldOneFiniteStageIdeleClassUnitModule S k.1 = 1 from k.2]
    simp
  · change fieldOneFiniteStageIdeleClassUnitModule S k.1 = 1
    exact k.2

@[simp] theorem fieldOneFiniteStageIdeleClassSplit_symm_moduleOne
    (S : Finset (HeightOneSpectrum ℤ))
    (k : FieldOneFiniteStageModuleOneClass S) :
    (fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv S).symm (k, 1) = k.1 := by
  apply (fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv S).injective
  rw [(fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv S).apply_symm_apply,
    fieldOneFiniteStageIdeleClassSplit_moduleOne]

/-- Left translation by the module-one class group on the literal split-Haar `L²(C_S)`. -/
def fieldOneFiniteStageSplitClassModuleOneLeftRegular
    (S : Finset (HeightOneSpectrum ℤ))
    (k : FieldOneFiniteStageModuleOneClass S) :
    FieldOneFiniteStageSplitClassL2 S ≃ₗᵢ[ℂ]
      FieldOneFiniteStageSplitClassL2 S where
  __ := Lp.compMeasurePreservingₗᵢ ℂ (k.1⁻¹ * ·)
    (measurePreserving_mul_left
      (fieldOneFiniteStageSplitHaarMeasure S) k.1⁻¹)
  invFun := Lp.compMeasurePreserving (k.1 * ·)
    (measurePreserving_mul_left
      (fieldOneFiniteStageSplitHaarMeasure S) k.1)
  left_inv f := by
    change Lp.compMeasurePreserving (k.1 * ·)
        (measurePreserving_mul_left
          (fieldOneFiniteStageSplitHaarMeasure S) k.1)
      (Lp.compMeasurePreserving (k.1⁻¹ * ·)
        (measurePreserving_mul_left
          (fieldOneFiniteStageSplitHaarMeasure S) k.1⁻¹) f) = f
    rw [← Lp.compMeasurePreserving_comp_apply f
      (measurePreserving_mul_left
        (fieldOneFiniteStageSplitHaarMeasure S) k.1⁻¹)
      (measurePreserving_mul_left
        (fieldOneFiniteStageSplitHaarMeasure S) k.1)]
    simp
    exact Lp.compMeasurePreserving_id_apply f
  right_inv f := by
    change Lp.compMeasurePreserving (k.1⁻¹ * ·)
        (measurePreserving_mul_left
          (fieldOneFiniteStageSplitHaarMeasure S) k.1⁻¹)
      (Lp.compMeasurePreserving (k.1 * ·)
        (measurePreserving_mul_left
          (fieldOneFiniteStageSplitHaarMeasure S) k.1) f) = f
    rw [← Lp.compMeasurePreserving_comp_apply f
      (measurePreserving_mul_left
        (fieldOneFiniteStageSplitHaarMeasure S) k.1)
      (measurePreserving_mul_left
        (fieldOneFiniteStageSplitHaarMeasure S) k.1⁻¹)]
    simp
    exact Lp.compMeasurePreserving_id_apply f

/-- The literal `K_S`-fixed subspace of the split-Haar `L²(C_S)`. -/
def fieldOneFiniteStageSplitClassModuleOneInvariantSubmodule
    (S : Finset (HeightOneSpectrum ℤ)) :
    Submodule ℂ (FieldOneFiniteStageSplitClassL2 S) where
  carrier := {f | ∀ k, fieldOneFiniteStageSplitClassModuleOneLeftRegular S k f = f}
  zero_mem' := by intro k; simp
  add_mem' := by
    intro f g hf hg k
    rw [map_add, hf k, hg k]
  smul_mem' := by
    intro c f hf k
    rw [map_smul, hf k]

theorem fieldOneFiniteStageSplitL2Unitary_intertwines_moduleOne
    (S : Finset (HeightOneSpectrum ℤ))
    (k : FieldOneFiniteStageModuleOneClass S)
    (f : FieldOneFiniteStageSplitClassL2 S) :
    fieldOneFiniteStageSplitL2Unitary S
        (fieldOneFiniteStageSplitClassModuleOneLeftRegular S k f) =
      fieldOneFiniteStageProductModuleOneLeftRegular S k
        (fieldOneFiniteStageSplitL2Unitary S f) := by
  change Lp.compMeasurePreserving
      (fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv S).symm
        (fieldOneFiniteStageSplit_symm_measurePreserving S)
        (fieldOneFiniteStageSplitClassModuleOneLeftRegular S k f) =
    Lp.compMeasurePreserving ((k⁻¹, 1) * ·)
      (measurePreserving_mul_left
        (fieldOneFiniteStageSplitProductHaarMeasure S) (k⁻¹, 1))
      (fieldOneFiniteStageSplitL2Unitary S f)
  apply Lp.ext
  let e := fieldOneFiniteStageIdeleClassSplitContinuousMulEquiv S
  have hleftSplit := Lp.coeFn_compMeasurePreserving
    (fieldOneFiniteStageSplitClassModuleOneLeftRegular S k f)
    (fieldOneFiniteStageSplit_symm_measurePreserving S)
  have hclass := Lp.coeFn_compMeasurePreserving f
    (measurePreserving_mul_left
      (fieldOneFiniteStageSplitHaarMeasure S) k.1⁻¹)
  have hclassComp := (fieldOneFiniteStageSplit_symm_measurePreserving S).quasiMeasurePreserving
    |>.ae_eq_comp hclass
  have hright := Lp.coeFn_compMeasurePreserving
    (fieldOneFiniteStageSplitL2Unitary S f)
    (measurePreserving_mul_left
      (fieldOneFiniteStageSplitProductHaarMeasure S) (k⁻¹, 1))
  have hsplit := Lp.coeFn_compMeasurePreserving f
    (fieldOneFiniteStageSplit_symm_measurePreserving S)
  have hsplitComp := (measurePreserving_mul_left
    (fieldOneFiniteStageSplitProductHaarMeasure S) (k⁻¹, 1)).quasiMeasurePreserving
      |>.ae_eq_comp hsplit
  filter_upwards [hleftSplit, hclassComp, hright, hsplitComp]
      with x hls hc hr hs
  rw [hls, hr]
  change
    ((↑↑(Lp.compMeasurePreserving (k.1⁻¹ * ·)
        (measurePreserving_mul_left
          (fieldOneFiniteStageSplitHaarMeasure S) k.1⁻¹) f) ∘ e.symm) x) =
      ((↑↑(Lp.compMeasurePreserving e.symm
        (fieldOneFiniteStageSplit_symm_measurePreserving S) f) ∘
          ((k⁻¹, 1) * ·)) x)
  rw [hc, hs]
  change (f : FieldOneFiniteStageIdeleClassGroup S → ℂ)
      (k.1⁻¹ * e.symm x) =
    (f : FieldOneFiniteStageIdeleClassGroup S → ℂ)
      (e.symm ((k⁻¹, 1) * x))
  apply congrArg (fun y =>
    (f : FieldOneFiniteStageIdeleClassGroup S → ℂ) y)
  rw [map_mul, fieldOneFiniteStageIdeleClassSplit_symm_moduleOne]
  rfl

theorem fieldOneFiniteStageSplitL2Unitary_mem_invariants_iff
    (S : Finset (HeightOneSpectrum ℤ))
    (f : FieldOneFiniteStageSplitClassL2 S) :
    fieldOneFiniteStageSplitL2Unitary S f ∈
        fieldOneFiniteStageProductModuleOneInvariantSubmodule S ↔
      f ∈ fieldOneFiniteStageSplitClassModuleOneInvariantSubmodule S := by
  constructor
  · intro hf k
    apply (fieldOneFiniteStageSplitL2Unitary S).injective
    rw [fieldOneFiniteStageSplitL2Unitary_intertwines_moduleOne, hf k]
  · intro hf k
    rw [← fieldOneFiniteStageSplitL2Unitary_intertwines_moduleOne, hf k]

def fieldOneFiniteStageClassInvariantsToProductInvariants
    (S : Finset (HeightOneSpectrum ℤ)) :
    fieldOneFiniteStageSplitClassModuleOneInvariantSubmodule S →ₗᵢ[ℂ]
      fieldOneFiniteStageProductModuleOneInvariantSubmodule S where
  toFun f := ⟨fieldOneFiniteStageSplitL2Unitary S f.1,
    (fieldOneFiniteStageSplitL2Unitary_mem_invariants_iff S f.1).2 f.2⟩
  map_add' f g := by
    apply Subtype.ext
    exact map_add (fieldOneFiniteStageSplitL2Unitary S) f.1 g.1
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul (fieldOneFiniteStageSplitL2Unitary S) c f.1
  norm_map' f := (fieldOneFiniteStageSplitL2Unitary S).norm_map f.1

theorem fieldOneFiniteStageClassInvariantsToProductInvariants_surjective
    (S : Finset (HeightOneSpectrum ℤ)) :
    Function.Surjective (fieldOneFiniteStageClassInvariantsToProductInvariants S) := by
  intro f
  let g : FieldOneFiniteStageSplitClassL2 S :=
    (fieldOneFiniteStageSplitL2Unitary S).symm f.1
  have hg : g ∈ fieldOneFiniteStageSplitClassModuleOneInvariantSubmodule S := by
    rw [← fieldOneFiniteStageSplitL2Unitary_mem_invariants_iff]
    simp [g, f.2]
  refine ⟨⟨g, hg⟩, ?_⟩
  apply Subtype.ext
  change fieldOneFiniteStageSplitL2Unitary S g = f.1
  simp [g]

/-- The `K_S`-fixed spaces on `L²(C_S)` and `L²(K_S × ℝ≥0ˣ)` are unitarily equivalent. -/
def fieldOneFiniteStageClassProductInvariantUnitary
    (S : Finset (HeightOneSpectrum ℤ)) :
    fieldOneFiniteStageSplitClassModuleOneInvariantSubmodule S ≃ₗᵢ[ℂ]
      fieldOneFiniteStageProductModuleOneInvariantSubmodule S :=
  LinearIsometryEquiv.ofSurjective
    (fieldOneFiniteStageClassInvariantsToProductInvariants S)
    (fieldOneFiniteStageClassInvariantsToProductInvariants_surjective S)

/-- Exact radial classification of the literal `K_S`-fixed part of split-Haar `L²(C_S)`. -/
def fieldOneFiniteStagePositiveClassInvariantUnitary
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOnePositiveUnitsL2 ≃ₗᵢ[ℂ]
      fieldOneFiniteStageSplitClassModuleOneInvariantSubmodule S :=
  (fieldOneFiniteStagePositiveProductInvariantUnitary S).trans
    (fieldOneFiniteStageClassProductInvariantUnitary S).symm

end

end GaloisForLFunctions.RHTower
