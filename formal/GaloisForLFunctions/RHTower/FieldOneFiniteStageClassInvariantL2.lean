import GaloisForLFunctions.RHTower.FieldOneFiniteStageClassModuleOneAction
import GaloisForLFunctions.RHTower.FieldOneFiniteStageIdeleClassInvariantL2

/-!
# The source unitary `w_S` on literal finite-stage class spaces

This file constructs the actual `K_S`-fixed subspace of `L²(X_S)` using
module-one scaling on the additive quotient.  Restriction to the conull
idele locus and multiplication by the source half-density intertwine that
literal action with Haar-side translation on `C_S`.  Combining the resulting
fixed-space equivalence with the exact Haar splitting
`C_S ≃ K_S × ℝ_+^*` gives the source unitary

`w_S : L²(X_S)^{K_S} ≃ L²(ℝ_+^*, d*u)`.
-/

open scoped NNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain MeasureTheory

/-! ### Literal regular representations -/

/-- Left translation on weighted `L²(C_S, |c|d*c)`. -/
def fieldOneFiniteStageIdeleClassAdditiveModuleOneLeftRegular
    (S : Finset (HeightOneSpectrum ℤ))
    (k : FieldOneFiniteStageModuleOneClass S) :
    FieldOneFiniteStageIdeleClassAdditiveL2 S ≃ₗᵢ[ℂ]
      FieldOneFiniteStageIdeleClassAdditiveL2 S where
  __ := Lp.compMeasurePreservingₗᵢ ℂ (k.1⁻¹ * ·)
    { measurable := (continuous_const.mul continuous_id).measurable
      map_eq :=
        fieldOneFiniteStageIdeleClassAdditiveMeasure_map_mulLeft_moduleOne S k⁻¹ }
  invFun := Lp.compMeasurePreserving (k.1 * ·)
    { measurable := (continuous_const.mul continuous_id).measurable
      map_eq :=
        fieldOneFiniteStageIdeleClassAdditiveMeasure_map_mulLeft_moduleOne S k }
  left_inv f := by
    change Lp.compMeasurePreserving (k.1 * ·) _
      (Lp.compMeasurePreserving (k.1⁻¹ * ·) _ f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    have hfun : ((k.1⁻¹ * ·) ∘ (k.1 * ·)) =
        (id : FieldOneFiniteStageIdeleClassGroup S → _) := by
      funext c
      simp [← mul_assoc]
    simpa only [hfun] using Lp.compMeasurePreserving_id_apply f
  right_inv f := by
    change Lp.compMeasurePreserving (k.1⁻¹ * ·) _
      (Lp.compMeasurePreserving (k.1 * ·) _ f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    have hfun : ((k.1 * ·) ∘ (k.1⁻¹ * ·)) =
        (id : FieldOneFiniteStageIdeleClassGroup S → _) := by
      funext c
      simp [← mul_assoc]
    simpa only [hfun] using Lp.compMeasurePreserving_id_apply f

/-- Pointwise-a.e. formula for weighted idele-class translation. -/
theorem fieldOneFiniteStageIdeleClassAdditiveModuleOneLeftRegular_ae
    (S : Finset (HeightOneSpectrum ℤ))
    (k : FieldOneFiniteStageModuleOneClass S)
    (f : FieldOneFiniteStageIdeleClassAdditiveL2 S) :
    fieldOneFiniteStageIdeleClassAdditiveModuleOneLeftRegular S k f =ᵐ[
        fieldOneFiniteStageIdeleClassAdditiveMeasure S]
      fun c => f (k.1⁻¹ * c) := by
  exact Lp.coeFn_compMeasurePreserving f
    ({ measurable := (continuous_const.mul continuous_id).measurable
       map_eq :=
         fieldOneFiniteStageIdeleClassAdditiveMeasure_map_mulLeft_moduleOne S k⁻¹ } :
      MeasurePreserving (k.1⁻¹ * ·)
        (fieldOneFiniteStageIdeleClassAdditiveMeasure S)
        (fieldOneFiniteStageIdeleClassAdditiveMeasure S))

/-- Literal left translation by `K_S` on `L²(X_S)`. -/
def fieldOneFiniteStageClassModuleOneLeftRegular
    (S : Finset (HeightOneSpectrum ℤ))
    (k : FieldOneFiniteStageModuleOneClass S) :
    FieldOneFiniteStageClassL2 S ≃ₗᵢ[ℂ]
      FieldOneFiniteStageClassL2 S where
  __ := Lp.compMeasurePreservingₗᵢ ℂ (k.1⁻¹ • ·)
    (fieldOneFiniteStageClassAdditiveMeasurePreserving_smul_moduleOne S k⁻¹)
  invFun := Lp.compMeasurePreserving (k.1 • ·)
    (fieldOneFiniteStageClassAdditiveMeasurePreserving_smul_moduleOne S k)
  left_inv f := by
    change Lp.compMeasurePreserving (k.1 • ·) _
      (Lp.compMeasurePreserving (k.1⁻¹ • ·) _ f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    have hfun : ((k.1⁻¹ • ·) ∘ (k.1 • ·)) =
        (id : FieldOneFiniteStageClassSpace S → _) := by
      funext x
      simp [smul_smul]
    simpa only [hfun] using Lp.compMeasurePreserving_id_apply f
  right_inv f := by
    change Lp.compMeasurePreserving (k.1⁻¹ • ·) _
      (Lp.compMeasurePreserving (k.1 • ·) _ f) = f
    rw [← Lp.compMeasurePreserving_comp_apply]
    have hfun : ((k.1 • ·) ∘ (k.1⁻¹ • ·)) =
        (id : FieldOneFiniteStageClassSpace S → _) := by
      funext x
      simp [smul_smul]
    simpa only [hfun] using Lp.compMeasurePreserving_id_apply f

/-- Pointwise-a.e. formula for literal class-space translation. -/
theorem fieldOneFiniteStageClassModuleOneLeftRegular_ae
    (S : Finset (HeightOneSpectrum ℤ))
    (k : FieldOneFiniteStageModuleOneClass S)
    (f : FieldOneFiniteStageClassL2 S) :
    fieldOneFiniteStageClassModuleOneLeftRegular S k f =ᵐ[
        fieldOneFiniteStageClassAdditiveMeasure S]
      fun x => f (k.1⁻¹ • x) := by
  exact Lp.coeFn_compMeasurePreserving f
    (fieldOneFiniteStageClassAdditiveMeasurePreserving_smul_moduleOne S k⁻¹)

/-- Pointwise-a.e. formula for split-Haar idele-class translation. -/
theorem fieldOneFiniteStageSplitClassModuleOneLeftRegular_ae
    (S : Finset (HeightOneSpectrum ℤ))
    (k : FieldOneFiniteStageModuleOneClass S)
    (f : FieldOneFiniteStageSplitClassL2 S) :
    fieldOneFiniteStageSplitClassModuleOneLeftRegular S k f =ᵐ[
        fieldOneFiniteStageSplitHaarMeasure S]
      fun c => f (k.1⁻¹ * c) := by
  exact Lp.coeFn_compMeasurePreserving f
    (measurePreserving_mul_left
      (fieldOneFiniteStageSplitHaarMeasure S) k.1⁻¹)

/-- Literal fixed vectors `L²(X_S)^{K_S}`. -/
def fieldOneFiniteStageClassModuleOneInvariantSubmodule
    (S : Finset (HeightOneSpectrum ℤ)) :
    Submodule ℂ (FieldOneFiniteStageClassL2 S) where
  carrier := {f | ∀ k, fieldOneFiniteStageClassModuleOneLeftRegular S k f = f}
  zero_mem' := by intro k; simp
  add_mem' := by
    intro f g hf hg k
    rw [map_add, hf k, hg k]
  smul_mem' := by
    intro c f hf k
    rw [map_smul, hf k]

/-! ### Intertwining -/

theorem fieldOneFiniteStageClassIdeleAdditiveL2Unitary_intertwines_moduleOne
    (S : Finset (HeightOneSpectrum ℤ))
    (k : FieldOneFiniteStageModuleOneClass S)
    (f : FieldOneFiniteStageClassL2 S) :
    fieldOneFiniteStageClassIdeleClassAdditiveL2Unitary S
        (fieldOneFiniteStageClassModuleOneLeftRegular S k f) =
      fieldOneFiniteStageIdeleClassAdditiveModuleOneLeftRegular S k
        (fieldOneFiniteStageClassIdeleClassAdditiveL2Unitary S f) := by
  apply Lp.ext
  have hleft := fieldOneFiniteStageClassIdeleClassAdditiveL2Unitary_ae S
    (fieldOneFiniteStageClassModuleOneLeftRegular S k f)
  have hclass := fieldOneFiniteStageClassModuleOneLeftRegular_ae S k f
  have hclassComp :=
    (fieldOneFiniteStageIdeleClassToClassSpace_measurePreserving S).quasiMeasurePreserving
      |>.ae_eq_comp hclass
  have hright :=
    fieldOneFiniteStageIdeleClassAdditiveModuleOneLeftRegular_ae S k
      (fieldOneFiniteStageClassIdeleClassAdditiveL2Unitary S f)
  have hpull := fieldOneFiniteStageClassIdeleClassAdditiveL2Unitary_ae S f
  have hpullComp :=
    ({ measurable := (continuous_const.mul continuous_id).measurable
       map_eq :=
         fieldOneFiniteStageIdeleClassAdditiveMeasure_map_mulLeft_moduleOne S k⁻¹ } :
      MeasurePreserving (k.1⁻¹ * ·)
        (fieldOneFiniteStageIdeleClassAdditiveMeasure S)
        (fieldOneFiniteStageIdeleClassAdditiveMeasure S)).quasiMeasurePreserving
      |>.ae_eq_comp hpull
  filter_upwards [hleft, hclassComp, hright, hpullComp]
      with c hl hc hr hp
  change
    (fieldOneFiniteStageClassModuleOneLeftRegular S k f)
        (fieldOneFiniteStageIdeleClassToClassSpace S c) =
      f (k.1⁻¹ • fieldOneFiniteStageIdeleClassToClassSpace S c) at hc
  change
    (fieldOneFiniteStageClassIdeleClassAdditiveL2Unitary S f)
        (k.1⁻¹ * c) =
      f (fieldOneFiniteStageIdeleClassToClassSpace S (k.1⁻¹ * c)) at hp
  rw [hl, hr, hc, hp]
  congr 1
  exact (fieldOneFiniteStageIdeleClassToClassSpace_mul S k.1⁻¹ c).symm

theorem fieldOneFiniteStageHalfDensityUnitary_intertwines_moduleOne
    (S : Finset (HeightOneSpectrum ℤ))
    (k : FieldOneFiniteStageModuleOneClass S)
    (f : FieldOneFiniteStageIdeleClassAdditiveL2 S) :
    fieldOneFiniteStageIdeleClassHalfDensityUnitary S
        (fieldOneFiniteStageIdeleClassAdditiveModuleOneLeftRegular S k f) =
      fieldOneFiniteStageSplitClassModuleOneLeftRegular S k
        (fieldOneFiniteStageIdeleClassHalfDensityUnitary S f) := by
  let w := fieldOneFiniteStageIdeleClassModuleReal S
  let hw := fieldOneFiniteStageIdeleClassModuleReal_measurable S
  let hp := fieldOneFiniteStageIdeleClassModuleReal_pos S
  apply Lp.ext
  have hleft := fieldOneFiniteStageIdeleClassHalfDensityUnitary_ae S
    (fieldOneFiniteStageIdeleClassAdditiveModuleOneLeftRegular S k f)
  have hweighted :=
    fieldOneFiniteStageIdeleClassAdditiveModuleOneLeftRegular_ae S k f
  have hweightedBase :
      (fieldOneFiniteStageIdeleClassAdditiveModuleOneLeftRegular S k f :
          FieldOneFiniteStageIdeleClassGroup S → ℂ) =ᵐ[
            fieldOneFiniteStageSplitHaarMeasure S]
        (fun c => f (k.1⁻¹ * c)) := by
    apply (GaloisForLFunctions.HTGeometry.withDensity_realDensity_ae_eq hw hp).mp
    simpa only [fieldOneFiniteStageIdeleClassAdditiveMeasure] using hweighted
  have hright := fieldOneFiniteStageSplitClassModuleOneLeftRegular_ae S k
    (fieldOneFiniteStageIdeleClassHalfDensityUnitary S f)
  have hhalf := fieldOneFiniteStageIdeleClassHalfDensityUnitary_ae S f
  have hhalfComp :=
    (measurePreserving_mul_left
      (fieldOneFiniteStageSplitHaarMeasure S) k.1⁻¹).quasiMeasurePreserving
      |>.ae_eq_comp hhalf
  filter_upwards [hleft, hweightedBase, hright, hhalfComp]
      with c hl hwc hr hh
  change (fieldOneFiniteStageIdeleClassHalfDensityUnitary S f)
      (k.1⁻¹ * c) =
    GaloisForLFunctions.HTGeometry.sqrtWeight
      (fieldOneFiniteStageIdeleClassModuleReal S) (k.1⁻¹ * c) *
        f (k.1⁻¹ * c) at hh
  rw [hl, hwc, hr, hh]
  have hk : fieldOneFiniteStageIdeleClassModule S k.1 = 1 := by
    have hkUnits := congrArg (fun u : ℝ≥0ˣ => (u : ℝ≥0)) k.2
    simpa [fieldOneFiniteStageIdeleClassUnitModule] using hkUnits
  have hmodule : w (k.1⁻¹ * c) = w c := by
    change (fieldOneFiniteStageIdeleClassModule S (k.1⁻¹ * c) : ℝ) =
      (fieldOneFiniteStageIdeleClassModule S c : ℝ)
    rw [map_mul, map_inv, hk]
    simp
  change (Real.sqrt (w c) : ℂ) * f (k.1⁻¹ * c) =
    (Real.sqrt (w (k.1⁻¹ * c)) : ℂ) * f (k.1⁻¹ * c)
  rw [hmodule]

theorem fieldOneFiniteStageClassToSplitClassL2Unitary_intertwines_moduleOne
    (S : Finset (HeightOneSpectrum ℤ))
    (k : FieldOneFiniteStageModuleOneClass S)
    (f : FieldOneFiniteStageClassL2 S) :
    fieldOneFiniteStageClassToSplitClassL2Unitary S
        (fieldOneFiniteStageClassModuleOneLeftRegular S k f) =
      fieldOneFiniteStageSplitClassModuleOneLeftRegular S k
        (fieldOneFiniteStageClassToSplitClassL2Unitary S f) := by
  change fieldOneFiniteStageIdeleClassHalfDensityUnitary S
      (fieldOneFiniteStageClassIdeleClassAdditiveL2Unitary S
        (fieldOneFiniteStageClassModuleOneLeftRegular S k f)) = _
  rw [fieldOneFiniteStageClassIdeleAdditiveL2Unitary_intertwines_moduleOne,
    fieldOneFiniteStageHalfDensityUnitary_intertwines_moduleOne]
  rfl

/-! ### Fixed-space source unitary -/

def fieldOneFiniteStageClassInvariantToSplitInvariant
    (S : Finset (HeightOneSpectrum ℤ)) :
    fieldOneFiniteStageClassModuleOneInvariantSubmodule S →ₗᵢ[ℂ]
      fieldOneFiniteStageSplitClassModuleOneInvariantSubmodule S where
  toFun f :=
    ⟨fieldOneFiniteStageClassToSplitClassL2Unitary S f.1, by
      intro k
      rw [← fieldOneFiniteStageClassToSplitClassL2Unitary_intertwines_moduleOne,
        f.2 k]⟩
  map_add' f g := by
    apply Subtype.ext
    exact map_add (fieldOneFiniteStageClassToSplitClassL2Unitary S) f.1 g.1
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul (fieldOneFiniteStageClassToSplitClassL2Unitary S) c f.1
  norm_map' f := (fieldOneFiniteStageClassToSplitClassL2Unitary S).norm_map f.1

theorem fieldOneFiniteStageClassInvariantToSplitInvariant_surjective
    (S : Finset (HeightOneSpectrum ℤ)) :
    Function.Surjective (fieldOneFiniteStageClassInvariantToSplitInvariant S) := by
  intro g
  let f : FieldOneFiniteStageClassL2 S :=
    (fieldOneFiniteStageClassToSplitClassL2Unitary S).symm g.1
  have hf : f ∈ fieldOneFiniteStageClassModuleOneInvariantSubmodule S := by
    intro k
    apply (fieldOneFiniteStageClassToSplitClassL2Unitary S).injective
    rw [fieldOneFiniteStageClassToSplitClassL2Unitary_intertwines_moduleOne]
    have hUf : fieldOneFiniteStageClassToSplitClassL2Unitary S f = g.1 := by
      simp [f]
    rw [hUf]
    exact g.2 k
  refine ⟨⟨f, hf⟩, ?_⟩
  apply Subtype.ext
  change fieldOneFiniteStageClassToSplitClassL2Unitary S f = g.1
  simp [f]

/-- Fixed-vector equivalence induced by restriction and half-density. -/
def fieldOneFiniteStageClassSplitInvariantUnitary
    (S : Finset (HeightOneSpectrum ℤ)) :
    fieldOneFiniteStageClassModuleOneInvariantSubmodule S ≃ₗᵢ[ℂ]
      fieldOneFiniteStageSplitClassModuleOneInvariantSubmodule S :=
  LinearIsometryEquiv.ofSurjective
    (fieldOneFiniteStageClassInvariantToSplitInvariant S)
    (fieldOneFiniteStageClassInvariantToSplitInvariant_surjective S)

/-- Literal finite-stage source unitary
`w_S : L²(X_S)^{K_S} ≃ L²(ℝ_+^*,d*u)`. -/
def fieldOneFiniteStageSourceUnitary
    (S : Finset (HeightOneSpectrum ℤ)) :
    fieldOneFiniteStageClassModuleOneInvariantSubmodule S ≃ₗᵢ[ℂ]
      FieldOnePositiveUnitsL2 :=
  (fieldOneFiniteStageClassSplitInvariantUnitary S).trans
    (fieldOneFiniteStagePositiveClassInvariantUnitary S).symm

end

end GaloisForLFunctions.RHTower
