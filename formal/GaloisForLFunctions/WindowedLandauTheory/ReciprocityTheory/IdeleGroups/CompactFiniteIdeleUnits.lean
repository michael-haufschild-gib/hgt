import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdeleRestrictedProduct
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdeleDivisor
import GaloisForLFunctions.HTGeometry.ABHN.NumberFieldFiniteLocalField

/-! Finite local integral unit groups are compact. Their product maps
continuously into the ideles with infinite coordinates equal to one. -/

noncomputable section

open NumberField IsDedekindDomain Topology Filter
open scoped RestrictedProduct WithZero ValuativeRel

namespace GlobalTheory.Reciprocity.IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

theorem isCompact_localIntegralUnits (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
      Set (v.adicCompletion K)ˣ) := by
  let F := v.adicCompletion K
  let O := v.adicCompletionIntegers K
  have h (w : FinitePlace K) : IsCompact
      (w.maximalIdeal.adicCompletionIntegers K : Set (w.maximalIdeal.adicCompletion K)) := by
    let J := w.maximalIdeal.adicCompletion K
    let v₀ : Valuation J ℤᵐ⁰ := Valued.v
    letI : ValuativeRel J := ValuativeRel.ofValuation v₀
    letI : v₀.Compatible := Valuation.Compatible.ofValuation v₀
    letI : IsNonarchimedeanLocalField J :=
      GaloisForLFunctions.HTGeometry.ABHN.numberFieldAdicCompletionIsNonarchimedeanLocalField K w
    have hc := IsNonarchimedeanLocalField.isCompact_closedBall J 1
    have he : (w.maximalIdeal.adicCompletionIntegers K : Set J) =
        {x | ValuativeRel.valuation J x ≤ 1} := by
      ext x
      change v₀ x ≤ 1 ↔ ValuativeRel.valuation J x ≤ 1
      simpa only [map_one] using (ValuativeRel.isEquiv v₀ (ValuativeRel.valuation J) x 1)
    rwa [he]
  have hO : IsCompact (O : Set F) := by
    have hc := h (FinitePlace.mk v)
    rw [FinitePlace.maximalIdeal_mk] at hc
    exact hc
  let g : Fˣ → F × F := fun a => ((a : F), ((a⁻¹ : Fˣ) : F))
  have hg : IsEmbedding g :=
    ((Homeomorph.refl F).prodCongr MulOpposite.opHomeomorph.symm).isEmbedding.comp
      (Units.isEmbedding_embedProduct (M := F))
  rw [hg.isCompact_iff]
  have he : g '' ((Submonoid.ofClass O).units : Set Fˣ) =
      ((O : Set F) ×ˢ (O : Set F)) ∩ {p : F × F | p.1 * p.2 = 1} := by
    ext p
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨ha, Units.mul_inv a⟩
    · rintro ⟨hp, hm⟩
      let a : Fˣ := ⟨p.1, p.2, hm, (mul_comm p.2 p.1).trans hm⟩
      exact ⟨a, hp, Prod.ext rfl rfl⟩
  rw [he]
  exact (hO.prod hO).inter_right (isClosed_eq (continuous_fst.mul continuous_snd) continuous_const)

/-- Product of the integral local unit groups at all finite places. -/
abbrev FiniteIntegralUnits (K : Type*) [Field K] [NumberField K] :=
  ∀ v : HeightOneSpectrum (𝓞 K), (Submonoid.ofClass (v.adicCompletionIntegers K)).units

instance compactSpace_finiteIntegralUnits : CompactSpace (FiniteIntegralUnits K) := by
  letI (v : HeightOneSpectrum (𝓞 K)) :
      CompactSpace ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
        Set (v.adicCompletion K)ˣ) :=
    isCompact_iff_compactSpace.mp (isCompact_localIntegralUnits v)
  exact Pi.compactSpace

def finiteIntegralIdele (a : FiniteIntegralUnits K) : IdeleGroup K :=
  (prodRestrictedEquiv K).symm (1, ⟨fun v => (a v).val, .of_forall fun v => (a v).2⟩)

theorem continuous_finiteIntegralIdele : Continuous (finiteIntegralIdele (K := K)) := by
  let f (a : FiniteIntegralUnits K) : Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units]_[𝓟 Set.univ] :=
    ⟨fun v => (a v).val, eventually_principal.mpr fun v _ => (a v).2⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.mpr
    (continuous_pi fun v => continuous_subtype_val.comp (continuous_apply v))
  have h : cofinite ≤ (𝓟 (Set.univ : Set (HeightOneSpectrum (𝓞 K)))) := by simp
  exact (prodRestrictedEquiv K).symm.continuous.comp
    (continuous_const.prodMk ((RestrictedProduct.continuous_inclusion h).comp hf))

@[simp]
theorem finiteProj_finiteIntegralIdele (a : FiniteIntegralUnits K) (v : HeightOneSpectrum (𝓞 K)) :
    finiteProj v (finiteIntegralIdele a) = (a v).val := by
  apply Units.ext
  rw [coe_finiteProj, ← prodRestrictedEquiv_apply_snd, finiteIntegralIdele, ContinuousMulEquiv.apply_symm_apply]
  rfl

@[simp]
theorem infiniteProj_finiteIntegralIdele (a : FiniteIntegralUnits K) (w : InfinitePlace K) :
    infiniteProj w (finiteIntegralIdele a) = 1 := by
  apply Units.ext
  rw [coe_infiniteProj, ← prodRestrictedEquiv_apply_fst, finiteIntegralIdele, ContinuousMulEquiv.apply_symm_apply]
  rfl

theorem exists_finiteIntegralUnits_of_ord_zero {x : IdeleGroup K}
    (hx : ∀ v, ord v x = 0) :
    ∃ a : FiniteIntegralUnits K, ∀ v, finiteProj v x = finiteProj v (finiteIntegralIdele a) := by
  have h (v : HeightOneSpectrum (𝓞 K)) : finiteProj v x ∈
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
    rw [Submonoid.mem_units_iff, ← map_inv, coe_finiteProj, coe_finiteProj]
    exact (ord_eq_zero_iff v x).mp (hx v)
  let a : FiniteIntegralUnits K := fun v => ⟨finiteProj v x, h v⟩
  exact ⟨a, fun v => (finiteProj_finiteIntegralIdele a v).symm⟩

end GlobalTheory.Reciprocity.IdeleGroup
