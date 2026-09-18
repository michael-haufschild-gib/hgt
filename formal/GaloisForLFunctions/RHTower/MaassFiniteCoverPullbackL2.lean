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

/-- Finite-cover pullback has the exact square-root degree norm scaling. -/
theorem norm_integralFiniteCoverPullbackLp
    (K Γ : Subgroup SL2Z) [K.IsFiniteRelIndex Γ] (hKΓ : K ≤ Γ)
    (f : Lp ℂ 2 (integralSubgroupQuotientMeasure Γ)) :
    ‖integralFiniteCoverPullbackLp K Γ hKΓ f‖ =
      Real.sqrt (Nat.card (Γ ⧸ K.subgroupOf Γ) : ℝ) * ‖f‖ := by
  let Q := Γ ⧸ K.subgroupOf Γ
  letI : Nonempty Q := ⟨QuotientGroup.mk 1⟩
  letI : Fintype Q := Fintype.ofFinite _
  have hcardNat : Nat.card Q ≠ 0 := Nat.ne_of_gt (Nat.card_pos (α := Q))
  have hcard : (Nat.card Q : ENNReal) ≠ 0 := by
    exact_mod_cast hcardNat
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (coe_integralFiniteCoverPullbackLp K Γ hKΓ f),
    eLpNorm_comp_subgroupQuotientProjection K Γ hKΓ
      (f : SL2R ⧸ realImage Γ → ℂ) 2
      ((Lp.aestronglyMeasurable f).smul_measure _)]
  rw [← Nat.cast_smul_eq_nsmul ENNReal,
    eLpNorm_smul_measure_of_ne_zero hcard, smul_eq_mul, ENNReal.toReal_mul]
  congr 1
  rw [← ENNReal.toReal_rpow]
  norm_num
  rw [← Real.sqrt_eq_rpow]

/-- Finite-cover pullback is a bounded complex-linear map on quotient `L²`. -/
noncomputable def integralFiniteCoverPullbackLpContinuousLinear
    (K Γ : Subgroup SL2Z) [K.IsFiniteRelIndex Γ] (hKΓ : K ≤ Γ) :
    Lp ℂ 2 (integralSubgroupQuotientMeasure Γ) →L[ℂ]
      Lp ℂ 2 (integralSubgroupQuotientMeasure K) :=
  LinearMap.mkContinuous (integralFiniteCoverPullbackLpLinear K Γ hKΓ)
    (Real.sqrt (Nat.card (Γ ⧸ K.subgroupOf Γ) : ℝ))
    (fun f => (norm_integralFiniteCoverPullbackLp K Γ hKΓ f).le)

end

end GaloisForLFunctions.RHTower
