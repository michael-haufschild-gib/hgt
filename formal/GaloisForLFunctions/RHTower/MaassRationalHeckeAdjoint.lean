import GaloisForLFunctions.RHTower.SelbergMaassFiniteFiberIntegration

/-!
# Hilbert adjoint for the rational finite Hecke correspondence

The finite trace from the rational common cover to its rational-conjugate
quotient is paired with literal pullback along that cover. This file proves
the cover projection is quasi-measure-preserving, constructs bounded pullback
on quotient `L²`, establishes exact degree scaling, and proves that pullback
is the Hilbert adjoint of the finite fibre trace.
-/

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set
open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups Pointwise Function

noncomputable section

theorem setIntegral_rationalHeckeConjugateFiberTrace_inner_eq
    (N : ℕ) (g : GL (Fin 2) ℚ)
    (f : SL2R ⧸ rationalHeckeCommonCoverReal N g → ℂ)
    (h : SL2R ⧸ rationalConjugateSL2Group N g → ℂ)
    (hφ : IntegrableOn (fun x : SL2R =>
      inner ℂ (f (QuotientGroup.mk x)) (h (QuotientGroup.mk x)))
      (rationalConjugateFiniteCoverFundamentalSet N g) realSL2Haar) :
    (∫ x in rationalConjugateSL2FundamentalSet N g,
      inner ℂ (rationalHeckeConjugateFiberTrace N g f (QuotientGroup.mk x))
        (h (QuotientGroup.mk x)) ∂realSL2Haar) =
    ∫ x in rationalConjugateFiniteCoverFundamentalSet N g,
      inner ℂ (f (QuotientGroup.mk x)) (h (QuotientGroup.mk x)) ∂realSL2Haar := by
  let D := (rationalConjugateSL2Group N g) ⧸
    (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)
  letI : Fintype D := Fintype.ofFinite _
  let S := rationalConjugateSL2FundamentalSet N g
  let FC := rationalConjugateFiniteCoverFundamentalSet N g
  let πK : SL2R → SL2R ⧸ rationalHeckeCommonCoverReal N g := QuotientGroup.mk
  let πR : SL2R → SL2R ⧸ rationalConjugateSL2Group N g := QuotientGroup.mk
  let φ : SL2R → ℂ := fun x => inner ℂ (f (πK x)) (h (πR x))
  change (∫ x in S, inner ℂ (rationalHeckeConjugateFiberTrace N g f (πR x))
      (h (πR x)) ∂realSL2Haar) = ∫ x in FC, φ x ∂realSL2Haar
  calc
    (∫ x in S, inner ℂ (rationalHeckeConjugateFiberTrace N g f (πR x))
        (h (πR x)) ∂realSL2Haar) =
      ∫ x in S, ∑ c : D, inner ℂ (f (πK (x * c.out.val))) (h (πR x))
        ∂realSL2Haar := by
      apply integral_congr_ae
      filter_upwards with x
      rw [show rationalHeckeConjugateFiberTrace N g f (πR x) =
        ∑ c : D, f (RHTower.deningerFiberMap
          (H := rationalHeckeCommonCoverReal N g) x c) by
          exact rationalHeckeConjugateFiberTrace_mk N g f x]
      rw [sum_inner]
      apply Finset.sum_congr rfl
      intro c hc
      rw [rationalHeckeConjugateFiberCoordinate_eq_mk_out]
    _ = ∫ x in S, ∑ c : D, φ (x * c.out.val) ∂realSL2Haar := by
      apply integral_congr_ae
      filter_upwards with x
      apply Finset.sum_congr rfl
      intro c hc
      dsimp only [φ]
      congr 1
      apply congrArg h
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply]
      change x⁻¹ * (x * c.out.val) ∈ rationalConjugateSL2Group N g
      convert c.out.property using 1
      group
    _ = ∫ x in FC, φ x ∂realSL2Haar := by
      symm
      apply setIntegral_rationalConjugateFiniteCoverFundamentalSet_eq_fiberSum N g φ
      simpa only [FC, φ, πK, πR] using hφ


/-- The finite common-cover projection preserves null sets. -/
theorem rationalHeckeConjugateCoverProjection_quasiMeasurePreserving
    (N : ℕ) (g : GL (Fin 2) ℚ) :
    Measure.QuasiMeasurePreserving (rationalHeckeConjugateCoverProjection N g)
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g))
      (rationalConjugateSL2QuotientMeasure N g) := by
  apply Measure.QuasiMeasurePreserving.mk
  · exact subgroupQuotientProjection_measurable _ _
      (realImage_rationalHeckeIntegralIntersection_le_conjugate N g)
  · rw [map_rationalHeckeConjugateCoverProjection_integralSubgroupQuotientMeasure N g]
    simpa only [Nat.cast_smul_eq_nsmul] using
      (Measure.smul_absolutelyContinuous
        (μ := rationalConjugateSL2QuotientMeasure N g)
        (c := (Nat.card ((rationalConjugateSL2Group N g) ⧸
          (rationalHeckeCommonCoverReal N g).subgroupOf
            (rationalConjugateSL2Group N g)) : ENNReal)))

/-- Pullback from the rational-conjugate quotient to its finite common cover. -/
theorem rationalHeckeConjugateCoverPullback_memLp
    (N : ℕ) (g : GL (Fin 2) ℚ)
    (f : Lp ℂ 2 (rationalConjugateSL2QuotientMeasure N g)) :
    MemLp ((f : SL2R ⧸ rationalConjugateSL2Group N g → ℂ) ∘
      rationalHeckeConjugateCoverProjection N g) 2
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) := by
  let D := (rationalConjugateSL2Group N g) ⧸
    (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)
  have htop : (Nat.card D : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hscaled : MemLp (f : SL2R ⧸ rationalConjugateSL2Group N g → ℂ) 2
      ((Nat.card D : ENNReal) • rationalConjugateSL2QuotientMeasure N g) :=
    (Lp.memLp f).smul_measure htop
  dsimp only [D] at hscaled
  rw [Nat.cast_smul_eq_nsmul ENNReal] at hscaled
  rw [← map_rationalHeckeConjugateCoverProjection_integralSubgroupQuotientMeasure N g] at hscaled
  exact hscaled.comp_of_map
    (subgroupQuotientProjection_measurable _ _
      (realImage_rationalHeckeIntegralIntersection_le_conjugate N g)).aemeasurable

/-- The common-cover pullback represented in quotient `L²`. -/
noncomputable def rationalHeckeConjugateCoverPullbackLp (N : ℕ) (g : GL (Fin 2) ℚ) :
    Lp ℂ 2 (rationalConjugateSL2QuotientMeasure N g) →
      Lp ℂ 2 (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) := fun f =>
  (rationalHeckeConjugateCoverPullback_memLp N g f).toLp
    ((f : SL2R ⧸ rationalConjugateSL2Group N g → ℂ) ∘
      rationalHeckeConjugateCoverProjection N g)

/-- The common-cover pullback has its literal quotient-function representative. -/
theorem coe_rationalHeckeConjugateCoverPullbackLp (N : ℕ) (g : GL (Fin 2) ℚ)
    (f : Lp ℂ 2 (rationalConjugateSL2QuotientMeasure N g)) :
    rationalHeckeConjugateCoverPullbackLp N g f =ᵐ[
      integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)]
      (f : SL2R ⧸ rationalConjugateSL2Group N g → ℂ) ∘
        rationalHeckeConjugateCoverProjection N g :=
  MemLp.coeFn_toLp (rationalHeckeConjugateCoverPullback_memLp N g f)


/-- Pullback along the common-cover projection is complex-linear. -/
theorem rationalHeckeConjugateCoverPullbackLp_map_add (N : ℕ) (g : GL (Fin 2) ℚ)
    (f h : Lp ℂ 2 (rationalConjugateSL2QuotientMeasure N g)) :
    rationalHeckeConjugateCoverPullbackLp N g (f + h) =
      rationalHeckeConjugateCoverPullbackLp N g f +
        rationalHeckeConjugateCoverPullbackLp N g h := by
  have hadd := (Lp.coeFn_add f h).comp_tendsto
    (rationalHeckeConjugateCoverProjection_quasiMeasurePreserving N g).tendsto_ae
  apply Lp.ext
  filter_upwards [coe_rationalHeckeConjugateCoverPullbackLp N g (f + h), hadd,
    coe_rationalHeckeConjugateCoverPullbackLp N g f,
    coe_rationalHeckeConjugateCoverPullbackLp N g h,
    Lp.coeFn_add (rationalHeckeConjugateCoverPullbackLp N g f)
      (rationalHeckeConjugateCoverPullbackLp N g h)] with x hleft hadd hf hh hright
  rw [hleft, hadd]
  change f (rationalHeckeConjugateCoverProjection N g x) +
      h (rationalHeckeConjugateCoverProjection N g x) =
    (rationalHeckeConjugateCoverPullbackLp N g f +
      rationalHeckeConjugateCoverPullbackLp N g h) x
  change rationalHeckeConjugateCoverPullbackLp N g f x =
    f (rationalHeckeConjugateCoverProjection N g x) at hf
  change rationalHeckeConjugateCoverPullbackLp N g h x =
    h (rationalHeckeConjugateCoverProjection N g x) at hh
  rw [← hf, ← hh]
  change (rationalHeckeConjugateCoverPullbackLp N g f +
    rationalHeckeConjugateCoverPullbackLp N g h) x =
      rationalHeckeConjugateCoverPullbackLp N g f x +
        rationalHeckeConjugateCoverPullbackLp N g h x at hright
  exact hright.symm

theorem rationalHeckeConjugateCoverPullbackLp_map_smul (N : ℕ) (g : GL (Fin 2) ℚ)
    (c : ℂ) (f : Lp ℂ 2 (rationalConjugateSL2QuotientMeasure N g)) :
    rationalHeckeConjugateCoverPullbackLp N g (c • f) =
      c • rationalHeckeConjugateCoverPullbackLp N g f := by
  have hsmul := (Lp.coeFn_smul c f).comp_tendsto
    (rationalHeckeConjugateCoverProjection_quasiMeasurePreserving N g).tendsto_ae
  apply Lp.ext
  filter_upwards [coe_rationalHeckeConjugateCoverPullbackLp N g (c • f), hsmul,
    coe_rationalHeckeConjugateCoverPullbackLp N g f,
    Lp.coeFn_smul c (rationalHeckeConjugateCoverPullbackLp N g f)]
    with x hleft hsmul hf hright
  rw [hleft, hsmul]
  change c • f (rationalHeckeConjugateCoverProjection N g x) =
    (c • rationalHeckeConjugateCoverPullbackLp N g f) x
  change rationalHeckeConjugateCoverPullbackLp N g f x =
    f (rationalHeckeConjugateCoverProjection N g x) at hf
  rw [← hf]
  change (c • rationalHeckeConjugateCoverPullbackLp N g f) x =
    c • rationalHeckeConjugateCoverPullbackLp N g f x at hright
  exact hright.symm

/-- The common-cover pullback as a linear map on quotient `L²`. -/
noncomputable def rationalHeckeConjugateCoverPullbackLpLinear (N : ℕ) (g : GL (Fin 2) ℚ) :
    Lp ℂ 2 (rationalConjugateSL2QuotientMeasure N g) →ₗ[ℂ]
      Lp ℂ 2 (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) where
  toFun := rationalHeckeConjugateCoverPullbackLp N g
  map_add' := rationalHeckeConjugateCoverPullbackLp_map_add N g
  map_smul' := rationalHeckeConjugateCoverPullbackLp_map_smul N g


/-- The rational common-cover pullback has exact square-root degree norm scaling. -/
theorem norm_rationalHeckeConjugateCoverPullbackLp
    (N : ℕ) (g : GL (Fin 2) ℚ)
    (f : Lp ℂ 2 (rationalConjugateSL2QuotientMeasure N g)) :
    ‖rationalHeckeConjugateCoverPullbackLp N g f‖ =
      Real.sqrt (Nat.card ((rationalConjugateSL2Group N g) ⧸
        (rationalHeckeCommonCoverReal N g).subgroupOf
          (rationalConjugateSL2Group N g)) : ℝ) * ‖f‖ := by
  let D := (rationalConjugateSL2Group N g) ⧸
    (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)
  have hcardNat : Nat.card D ≠ 0 := Nat.ne_of_gt (Nat.card_pos (α := D))
  have hcard : (Nat.card D : ENNReal) ≠ 0 := by
    exact_mod_cast hcardNat
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (coe_rationalHeckeConjugateCoverPullbackLp N g f),
    eLpNorm_comp_rationalHeckeConjugateCoverProjection N g
      (f : SL2R ⧸ rationalConjugateSL2Group N g → ℂ) 2
      ((Lp.aestronglyMeasurable f).smul_measure _)]
  rw [← Nat.cast_smul_eq_nsmul ENNReal,
    eLpNorm_smul_measure_of_ne_zero hcard, smul_eq_mul, ENNReal.toReal_mul]
  congr 1
  rw [← ENNReal.toReal_rpow]
  norm_num
  rw [← Real.sqrt_eq_rpow]

/-- The common-cover pullback is a bounded complex-linear operator on quotient `L²`. -/
noncomputable def rationalHeckeConjugateCoverPullbackLpContinuousLinear
    (N : ℕ) (g : GL (Fin 2) ℚ) :
    Lp ℂ 2 (rationalConjugateSL2QuotientMeasure N g) →L[ℂ]
      Lp ℂ 2 (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) :=
  LinearMap.mkContinuous (rationalHeckeConjugateCoverPullbackLpLinear N g)
    (Real.sqrt (Nat.card ((rationalConjugateSL2Group N g) ⧸
      (rationalHeckeCommonCoverReal N g).subgroupOf
        (rationalConjugateSL2Group N g)) : ℝ))
    (fun f => (norm_rationalHeckeConjugateCoverPullbackLp N g f).le)


/-- The finite-fibre trace and finite-cover pullback are exact Hilbert adjoints. -/
theorem rationalHeckeConjugateFiberTraceLp_inner_eq_pullback
    (N : ℕ) (g : GL (Fin 2) ℚ)
    (f : Lp ℂ 2
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)))
    (h : Lp ℂ 2 (rationalConjugateSL2QuotientMeasure N g)) :
    inner ℂ (rationalHeckeConjugateFiberTraceLp N g f) h =
      inner ℂ f (rationalHeckeConjugateCoverPullbackLp N g h) := by
  let K := rationalHeckeCommonCoverReal N g
  let R := rationalConjugateSL2Group N g
  let D := R ⧸ K.subgroupOf R
  letI : Fintype D := Fintype.ofFinite _
  let S := rationalConjugateSL2FundamentalSet N g
  let FC := rationalConjugateFiniteCoverFundamentalSet N g
  let μK := integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)
  let μR := rationalConjugateSL2QuotientMeasure N g
  let πK : SL2R → SL2R ⧸ K := QuotientGroup.mk
  let πR : SL2R → SL2R ⧸ R := QuotientGroup.mk
  let p := rationalHeckeConjugateCoverProjection N g
  let f₀ := AEStronglyMeasurable.mk f (Lp.aestronglyMeasurable f)
  let h₀ := AEStronglyMeasurable.mk h (Lp.aestronglyMeasurable h)
  have hπK : Measurable πK := QuotientGroup.measurable_coe
  have hπR : Measurable πR := QuotientGroup.measurable_coe
  have hp : Measurable p := subgroupQuotientProjection_measurable _ _
    (realImage_rationalHeckeIntegralIntersection_le_conjugate N g)
  have hπKpres : MeasurePreserving πK (realSL2Haar.restrict FC) μK := by
    dsimp only [μK, FC, πK, K]
    rw [integralSubgroupQuotientMeasure_eq_map_rationalConjugateFiniteCoverFundamentalSet N g]
    exact ⟨QuotientGroup.measurable_coe, rfl⟩
  have hπRpres : MeasurePreserving πR (realSL2Haar.restrict S) μR := by
    dsimp only [μR, S, πR, R]
    exact (rationalConjugateSL2FundamentalSet_isFundamentalDomain N g).measurePreserving_quotient_mk _
  have hcomp : p ∘ πK = πR := by
    funext x
    exact subgroupQuotientProjection_mk _ _
      (realImage_rationalHeckeIntegralIntersection_le_conjugate N g) x
  have hπRcover : MeasurePreserving πR (realSL2Haar.restrict FC)
      (Nat.card D • μR) := by
    refine ⟨hπR, ?_⟩
    calc
      Measure.map πR (realSL2Haar.restrict FC) =
          Measure.map (p ∘ πK) (realSL2Haar.restrict FC) := by rw [hcomp]
      _ = Measure.map p (Measure.map πK (realSL2Haar.restrict FC)) :=
        (Measure.map_map hp hπK).symm
      _ = Measure.map p μK := by
        dsimp only [μK, FC, πK, K]
        rw [← integralSubgroupQuotientMeasure_eq_map_rationalConjugateFiniteCoverFundamentalSet N g]
      _ = Nat.card D • μR := by
        dsimp only [p, μK, μR, D, K, R]
        exact map_rationalHeckeConjugateCoverProjection_integralSubgroupQuotientMeasure N g
  have hf₀strong : StronglyMeasurable f₀ :=
    (Lp.aestronglyMeasurable f).stronglyMeasurable_mk
  have hh₀strong : StronglyMeasurable h₀ :=
    (Lp.aestronglyMeasurable h).stronglyMeasurable_mk
  have hf₀ : MemLp f₀ 2 μK :=
    (memLp_congr_ae (Lp.aestronglyMeasurable f).ae_eq_mk).mp (Lp.memLp f)
  have hh₀ : MemLp h₀ 2 μR :=
    (memLp_congr_ae (Lp.aestronglyMeasurable h).ae_eq_mk).mp (Lp.memLp h)
  have hfFC : MemLp (f₀ ∘ πK) 2 (realSL2Haar.restrict FC) :=
    hf₀.comp_measurePreserving hπKpres
  have hDtop : (Nat.card D : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hhscaled : MemLp h₀ 2 (Nat.card D • μR) := by
    have hscale := hh₀.smul_measure hDtop
    rw [Nat.cast_smul_eq_nsmul ENNReal] at hscale
    exact hscale
  have hhFC : MemLp (h₀ ∘ πR) 2 (realSL2Haar.restrict FC) :=
    hhscaled.comp_measurePreserving hπRcover
  let φ : SL2R → ℂ := fun x => inner ℂ (f₀ (πK x)) (h₀ (πR x))
  have hφ : IntegrableOn φ FC realSL2Haar := by
    change Integrable (h₀ ∘ πR * star (f₀ ∘ πK)) (realSL2Haar.restrict FC)
    simpa only [Pi.star_apply, mul_comm] using hfFC.star.integrable_mul hhFC
  have hraw := setIntegral_rationalHeckeConjugateFiberTrace_inner_eq N g f₀ h₀ (by
    simpa only [FC, φ, πK, πR] using hφ)
  have htraceAE : rationalHeckeConjugateFiberTraceLp N g f =ᵐ[μR]
      rationalHeckeConjugateFiberTrace N g f₀ := by
    dsimp only [μR, f₀]
    exact coe_rationalHeckeConjugateFiberTraceLp N g f
  have hfAE : (f : SL2R ⧸ K → ℂ) =ᵐ[μK] f₀ := by
    dsimp only [μK, f₀, K]
    exact (Lp.aestronglyMeasurable f).ae_eq_mk
  have hhAE : (h : SL2R ⧸ R → ℂ) =ᵐ[μR] h₀ := by
    dsimp only [μR, h₀, R]
    exact (Lp.aestronglyMeasurable h).ae_eq_mk
  have hpullAE : rationalHeckeConjugateCoverPullbackLp N g h =ᵐ[μK]
      h₀ ∘ p := by
    have hcompAE := hhAE.comp_tendsto
      (rationalHeckeConjugateCoverProjection_quasiMeasurePreserving N g).tendsto_ae
    calc
      rationalHeckeConjugateCoverPullbackLp N g h =ᵐ[μK]
          (h : SL2R ⧸ R → ℂ) ∘ p := by
            dsimp only [μK, R, p]
            exact coe_rationalHeckeConjugateCoverPullbackLp N g h
      _ =ᵐ[μK] h₀ ∘ p := hcompAE
  have hleftAE : (fun y => inner ℂ (rationalHeckeConjugateFiberTraceLp N g f y) (h y))
      =ᵐ[μR] fun y => inner ℂ (rationalHeckeConjugateFiberTrace N g f₀ y) (h₀ y) := by
    filter_upwards [htraceAE, hhAE] with y hyT hyh
    rw [hyT, hyh]
  have hrightAE : (fun y => inner ℂ (f y)
      (rationalHeckeConjugateCoverPullbackLp N g h y)) =ᵐ[μK]
      fun y => inner ℂ (f₀ y) (h₀ (p y)) := by
    filter_upwards [hfAE, hpullAE] with y hyf hyh
    rw [hyf]
    simpa only [Function.comp_apply] using congrArg (inner ℂ (f₀ y)) hyh
  rw [L2.inner_def, L2.inner_def]
  calc
    (∫ y, inner ℂ (rationalHeckeConjugateFiberTraceLp N g f y) (h y) ∂μR) =
        ∫ y, inner ℂ (rationalHeckeConjugateFiberTrace N g f₀ y) (h₀ y) ∂μR :=
      integral_congr_ae hleftAE
    _ = ∫ x in S, inner ℂ (rationalHeckeConjugateFiberTrace N g f₀ (πR x))
          (h₀ (πR x)) ∂realSL2Haar := by
      rw [← hπRpres.map_eq]
      exact integral_map hπR.aemeasurable
        (AEStronglyMeasurable.inner
          (rationalHeckeConjugateFiberTrace_measurable_of_stronglyMeasurable N g f₀ hf₀strong).aestronglyMeasurable
          hh₀strong.aestronglyMeasurable)
    _ = ∫ x in FC, inner ℂ (f₀ (πK x)) (h₀ (πR x)) ∂realSL2Haar := by
      dsimp only [S, FC, πK, πR, K, R] at hraw ⊢
      exact hraw
    _ = ∫ y, inner ℂ (f₀ y) (h₀ (p y)) ∂μK := by
      rw [← hπKpres.map_eq]
      symm
      exact integral_map hπK.aemeasurable
        (AEStronglyMeasurable.inner hf₀strong.aestronglyMeasurable
          (hh₀strong.comp_measurable hp).aestronglyMeasurable)
    _ = ∫ y, inner ℂ (f y) (rationalHeckeConjugateCoverPullbackLp N g h y) ∂μK :=
      (integral_congr_ae hrightAE).symm


/-- The bounded finite-fibre trace has finite-cover pullback as its Hilbert adjoint. -/
theorem rationalHeckeConjugateFiberTraceLpContinuousLinear_adjoint
    (N : ℕ) (g : GL (Fin 2) ℚ) :
    ContinuousLinearMap.adjoint (rationalHeckeConjugateFiberTraceLpContinuousLinear N g) =
      rationalHeckeConjugateCoverPullbackLpContinuousLinear N g := by
  apply ContinuousLinearMap.ext
  intro h
  apply ext_inner_left ℂ
  intro f
  calc
    inner ℂ f (ContinuousLinearMap.adjoint
        (rationalHeckeConjugateFiberTraceLpContinuousLinear N g) h) =
        inner ℂ (rationalHeckeConjugateFiberTraceLpContinuousLinear N g f) h :=
      ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = inner ℂ f (rationalHeckeConjugateCoverPullbackLpContinuousLinear N g h) :=
      rationalHeckeConjugateFiberTraceLp_inner_eq_pullback N g f h

end

end GaloisForLFunctions.RHTower
