import GaloisForLFunctions.RHTower.IntegralSubgroupFiniteCoverMeasureScaling

namespace GaloisForLFunctions.RHTower

open MeasureTheory
open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups

noncomputable section

/-- The finite-cover quotient projection is quasi-measure-preserving for the
canonical quotient measures. -/
theorem integralFiniteCoverProjection_quasiMeasurePreserving
    (K Γ : Subgroup SL2Z) [K.IsFiniteRelIndex Γ] (hKΓ : K ≤ Γ) :
    Measure.QuasiMeasurePreserving
      (subgroupQuotientProjection (realImage K) (realImage Γ) (Subgroup.map_mono hKΓ))
      (integralSubgroupQuotientMeasure K) (integralSubgroupQuotientMeasure Γ) := by
  apply Measure.QuasiMeasurePreserving.mk
  · exact subgroupQuotientProjection_measurable _ _ (Subgroup.map_mono hKΓ)
  · rw [map_subgroupQuotientProjection_integralSubgroupQuotientMeasure K Γ hKΓ]
    simpa only [Nat.cast_smul_eq_nsmul] using
      (Measure.smul_absolutelyContinuous
        (μ := integralSubgroupQuotientMeasure Γ)
        (c := (Nat.card (Γ ⧸ K.subgroupOf Γ) : ENNReal)))

/-- Pullback of an `L²` function along a finite integral subgroup cover. -/
noncomputable def integralFiniteCoverPullbackLp
    (K Γ : Subgroup SL2Z) [K.IsFiniteRelIndex Γ] (hKΓ : K ≤ Γ) :
    Lp ℂ 2 (integralSubgroupQuotientMeasure Γ) →
      Lp ℂ 2 (integralSubgroupQuotientMeasure K) := fun f =>
  (memLp_comp_subgroupQuotientProjection K Γ hKΓ (f : SL2R ⧸ realImage Γ → ℂ) 2
    (Lp.memLp f)).toLp
    ((f : SL2R ⧸ realImage Γ → ℂ) ∘
      subgroupQuotientProjection (realImage K) (realImage Γ) (Subgroup.map_mono hKΓ))

/-- The finite-cover `L²` pullback has its literal quotient-function representative. -/
theorem coe_integralFiniteCoverPullbackLp
    (K Γ : Subgroup SL2Z) [K.IsFiniteRelIndex Γ] (hKΓ : K ≤ Γ)
    (f : Lp ℂ 2 (integralSubgroupQuotientMeasure Γ)) :
    integralFiniteCoverPullbackLp K Γ hKΓ f =ᵐ[integralSubgroupQuotientMeasure K]
      (f : SL2R ⧸ realImage Γ → ℂ) ∘
        subgroupQuotientProjection (realImage K) (realImage Γ) (Subgroup.map_mono hKΓ) :=
  MemLp.coeFn_toLp _

/-- The finite-cover `L²` pullback is complex-linear. -/
noncomputable def integralFiniteCoverPullbackLpLinear
    (K Γ : Subgroup SL2Z) [K.IsFiniteRelIndex Γ] (hKΓ : K ≤ Γ) :
    Lp ℂ 2 (integralSubgroupQuotientMeasure Γ) →ₗ[ℂ]
      Lp ℂ 2 (integralSubgroupQuotientMeasure K) where
  toFun := integralFiniteCoverPullbackLp K Γ hKΓ
  map_add' f h := by
    apply Lp.ext
    have hadd_scaled : ∀ᵐ x ∂integralSubgroupQuotientMeasure K,
        (f + h : Lp ℂ 2 (integralSubgroupQuotientMeasure Γ))
          (subgroupQuotientProjection (realImage K) (realImage Γ) (Subgroup.map_mono hKΓ) x) =
        f (subgroupQuotientProjection (realImage K) (realImage Γ) (Subgroup.map_mono hKΓ) x) +
          h (subgroupQuotientProjection (realImage K) (realImage Γ) (Subgroup.map_mono hKΓ) x) := by
      simpa only [Function.comp_apply, Pi.add_apply] using!
        (Lp.coeFn_add f h).comp_tendsto
          (integralFiniteCoverProjection_quasiMeasurePreserving K Γ hKΓ).tendsto_ae
    filter_upwards [coe_integralFiniteCoverPullbackLp K Γ hKΓ (f + h),
      coe_integralFiniteCoverPullbackLp K Γ hKΓ f,
      coe_integralFiniteCoverPullbackLp K Γ hKΓ h, hadd_scaled,
      Lp.coeFn_add (integralFiniteCoverPullbackLp K Γ hKΓ f)
        (integralFiniteCoverPullbackLp K Γ hKΓ h)] with x hfh hf hh hadd hsum
    rw [hfh, hsum]
    change (f + h : Lp ℂ 2 (integralSubgroupQuotientMeasure Γ))
        (subgroupQuotientProjection (realImage K) (realImage Γ) (Subgroup.map_mono hKΓ) x) =
      integralFiniteCoverPullbackLp K Γ hKΓ f x +
        integralFiniteCoverPullbackLp K Γ hKΓ h x
    rw [hf, hh]
    exact hadd
  map_smul' c f := by
    apply Lp.ext
    have hsmul_scaled : ∀ᵐ x ∂integralSubgroupQuotientMeasure K,
        (c • f : Lp ℂ 2 (integralSubgroupQuotientMeasure Γ))
          (subgroupQuotientProjection (realImage K) (realImage Γ) (Subgroup.map_mono hKΓ) x) =
        c • f (subgroupQuotientProjection (realImage K) (realImage Γ) (Subgroup.map_mono hKΓ) x) := by
      simpa only [Function.comp_apply, Pi.smul_apply] using!
        (Lp.coeFn_smul c f).comp_tendsto
          (integralFiniteCoverProjection_quasiMeasurePreserving K Γ hKΓ).tendsto_ae
    filter_upwards [coe_integralFiniteCoverPullbackLp K Γ hKΓ (c • f),
      coe_integralFiniteCoverPullbackLp K Γ hKΓ f, hsmul_scaled,
      Lp.coeFn_smul c (integralFiniteCoverPullbackLp K Γ hKΓ f)] with x hcf hf hsmul hsum
    simp only [RingHom.id_apply]
    rw [hcf, hsum]
    simp only [Function.comp_apply, Pi.smul_apply]
    rw [hsmul, hf]
    rfl

end

end GaloisForLFunctions.RHTower
