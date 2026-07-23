import GaloisForLFunctions.HTGeometry.HomogeneousMultipleEllipticGammaScaleReflectionUniversalityLaw
import GaloisForLFunctions.HTGeometry.EllipticGammaTwoTierExternalFreenessUniversalityLaw

/-!
# Homogeneous multiple elliptic-Gamma logarithmic-derivative reflection universality

Restoring the base period does more than make the multiple elliptic-Gamma value scale invariant.
Its logarithmic derivative becomes a covector of homogeneous weight `-1`: simultaneous nonzero
scaling of every period and the argument multiplies it by the inverse scale. Reflection through
the physical period sum acts on the same covector by the rank-parity sign.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι]

local instance homogeneousMultipleEllipticGammaLogDerivativeUnivDomain :
    IsDomain (Bottcher.analyticSubring Set.univ) :=
  multipleEllipticGammaHTUnivDomain

local instance homogeneousMultipleEllipticGammaLogDerivativeComplexAlgebraAnalytic :
    Algebra ℂ (Bottcher.analyticSubring Set.univ) :=
  multipleEllipticGammaHTComplexAlgebraAnalytic

local instance homogeneousMultipleEllipticGammaLogDerivativeComplexAlgebraMero :
    Algebra ℂ (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTComplexAlgebraMero

local instance homogeneousMultipleEllipticGammaLogDerivativeMeroDifferential :
    Differential (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTMeroDifferential

local instance homogeneousMultipleEllipticGammaLogDerivativeComplexDifferential :
    Differential ℂ :=
  multipleEllipticGammaHTComplexDifferential

local instance homogeneousMultipleEllipticGammaLogDerivativeMeroCharZero :
    CharZero (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTMeroCharZero

local instance homogeneousMultipleEllipticGammaLogDerivativeComplexDifferentialAlgebra :
    DifferentialAlgebra ℂ (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTComplexDifferentialAlgebra

local instance homogeneousMultipleEllipticGammaLogDerivativeCoordinateDifferential :
    Differential meromorphicRationalCoordinateField :=
  multipleEllipticGammaHTCoordinateDifferential

local instance homogeneousMultipleEllipticGammaLogDerivativeCoordinateDifferentialAlgebra :
    DifferentialAlgebra meromorphicRationalCoordinateField
      (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTCoordinateDifferentialAlgebra

/-- The parity-dependent normalized multiple elliptic-Gamma product is differentiable at every
point where its backward product is nonzero. The assumption is needed only in even rank, where
the backward product is the denominator. -/
theorem differentiableAt_multipleEllipticGammaProduct_of_backward_ne_zero
    {τ : ι → ℂ} (hτ : ∀ i, 0 < (τ i).im) {z : ℂ}
    (hzB : multipleEllipticGammaBackwardProduct τ z ≠ 0) :
    DifferentiableAt ℂ (multipleEllipticGammaProduct τ) z := by
  change DifferentiableAt ℂ
    (fun w => if Even (Fintype.card ι) then
      multipleEllipticGammaForwardProduct τ w /
        multipleEllipticGammaBackwardProduct τ w
    else
      multipleEllipticGammaForwardProduct τ w *
        multipleEllipticGammaBackwardProduct τ w) z
  by_cases hcard : Even (Fintype.card ι)
  · simp only [hcard, if_true]
    exact
      (differentiable_multipleEllipticGammaForwardProduct hτ).differentiableAt.div
        (differentiable_multipleEllipticGammaBackwardProduct hτ).differentiableAt hzB
  · simp only [hcard, if_false]
    exact
      (differentiable_multipleEllipticGammaForwardProduct hτ).differentiableAt.mul
        (differentiable_multipleEllipticGammaBackwardProduct hτ).differentiableAt

/-- The homogeneous logarithmic derivative is the normalized logarithmic derivative multiplied
by the inverse base period. -/
theorem logDeriv_homogeneousMultipleEllipticGammaProduct_eq
    (ω₀ : ℂ) (ω : ι → ℂ)
    (hω : ∀ i, 0 < (ω i / ω₀).im) (z : ℂ)
    (hzB : multipleEllipticGammaBackwardProduct
      (fun i => ω i / ω₀) (z / ω₀) ≠ 0) :
    logDeriv (homogeneousMultipleEllipticGammaProduct ω₀ ω) z =
      logDeriv (multipleEllipticGammaProduct (fun i => ω i / ω₀)) (z / ω₀) *
        (1 / ω₀) := by
  change logDeriv
      (multipleEllipticGammaProduct (fun i => ω i / ω₀) ∘ fun w : ℂ => w / ω₀) z = _
  have hg : DifferentiableAt ℂ (fun w : ℂ => w / ω₀) z := by
    fun_prop
  have hchain := logDeriv_comp
    (f := multipleEllipticGammaProduct (fun i => ω i / ω₀))
    (g := fun w : ℂ => w / ω₀) (x := z)
    (differentiableAt_multipleEllipticGammaProduct_of_backward_ne_zero hω hzB) hg
  simpa only [Function.comp_apply, deriv_div_const, deriv_id''] using hchain

/-- **Homogeneous weight-minus-one law.** Simultaneously scaling every period and the argument
by a nonzero scalar multiplies the physical logarithmic derivative by the inverse scalar. -/
theorem logDeriv_homogeneousMultipleEllipticGammaProduct_scale
    (c : ℂ) (hc : c ≠ 0) (ω₀ : ℂ) (hω₀ : ω₀ ≠ 0)
    (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i / ω₀).im) (z : ℂ)
    (hzB : multipleEllipticGammaBackwardProduct
      (fun i => ω i / ω₀) (z / ω₀) ≠ 0) :
    logDeriv
        (homogeneousMultipleEllipticGammaProduct (c * ω₀) (fun i => c * ω i))
        (c * z) =
      c⁻¹ * logDeriv (homogeneousMultipleEllipticGammaProduct ω₀ ω) z := by
  have hscaled : ∀ i, 0 < ((c * ω i) / (c * ω₀)).im := by
    intro i
    rw [mul_div_mul_left (ω i) ω₀ hc]
    exact hω i
  rw [logDeriv_homogeneousMultipleEllipticGammaProduct_eq
      (c * ω₀) (fun i => c * ω i) hscaled (c * z) (by
        simpa only [mul_div_mul_left _ _ hc] using hzB)]
  rw [logDeriv_homogeneousMultipleEllipticGammaProduct_eq
      ω₀ ω hω z hzB]
  simp_rw [mul_div_mul_left _ _ hc]
  field_simp

/-- **Physical-period logarithmic reflection law.** Reflection through the unnormalized period
sum acts on the homogeneous logarithmic derivative by the rank-parity sign. -/
theorem logDeriv_homogeneousMultipleEllipticGammaProduct_reflection
    (ω₀ : ℂ) (ω : ι → ℂ)
    (hω : ∀ i, 0 < (ω i / ω₀).im) (z : ℂ)
    (hzF : multipleEllipticGammaForwardProduct (fun i => ω i / ω₀) (z / ω₀) ≠ 0)
    (hzB : multipleEllipticGammaBackwardProduct (fun i => ω i / ω₀) (z / ω₀) ≠ 0) :
    logDeriv (homogeneousMultipleEllipticGammaProduct ω₀ ω)
        ((∑ i, ω i) - z) =
      multipleEllipticGammaLogSign ι *
        logDeriv (homogeneousMultipleEllipticGammaProduct ω₀ ω) z := by
  have hcenter :
      ((∑ i, ω i) - z) / ω₀ =
        (∑ i, ω i / ω₀) - z / ω₀ := by
    rw [sub_div, Finset.sum_div]
  obtain ⟨hrF, hrB⟩ :=
    multipleEllipticGammaProducts_reflection_ne_zero hzF hzB
  rw [logDeriv_homogeneousMultipleEllipticGammaProduct_eq
      ω₀ ω hω ((∑ i, ω i) - z) (by
        rw [hcenter]
        exact hrB),
    logDeriv_homogeneousMultipleEllipticGammaProduct_eq
      ω₀ ω hω z hzB,
    hcenter,
    logDeriv_multipleEllipticGammaProduct_reflection hω hzF hzB]
  ring

/-- **Homogeneous multiple elliptic-Gamma log-derivative universality law.** A rank-three minor
forces hypertranscendence of the product and its logarithmic derivative, while the restored
physical logarithmic derivative has homogeneous weight `-1` and parity reflection through the
physical period sum. -/
theorem homogeneousMultipleEllipticGamma_logDerivativeScaleReflectionUniversality
    [DecidableEq ι] (ω₀ : ℂ) (hω₀ : ω₀ ≠ 0) (ω : ι → ℂ)
    (hω : ∀ i, 0 < (ω i / ω₀).im)
    (hminor : MultipleEllipticGammaHasRankThreeMinor (fun i => ω i / ω₀)) :
    HypertranscendentalOver meromorphicRationalCoordinateField
        (multipleEllipticGammaMero (fun i => ω i / ω₀) hω) ∧
      HypertranscendentalOver meromorphicRationalCoordinateField
        (multipleEllipticGammaLogDerivMero (fun i => ω i / ω₀) hω) ∧
      (∀ (c : ℂ), c ≠ 0 → ∀ z : ℂ,
        multipleEllipticGammaBackwardProduct
            (fun i => ω i / ω₀) (z / ω₀) ≠ 0 →
        logDeriv
            (homogeneousMultipleEllipticGammaProduct
              (c * ω₀) (fun i => c * ω i))
            (c * z) =
          c⁻¹ * logDeriv
            (homogeneousMultipleEllipticGammaProduct ω₀ ω) z) ∧
      ∀ z : ℂ,
        multipleEllipticGammaForwardProduct
            (fun i => ω i / ω₀) (z / ω₀) ≠ 0 →
        multipleEllipticGammaBackwardProduct
            (fun i => ω i / ω₀) (z / ω₀) ≠ 0 →
        logDeriv (homogeneousMultipleEllipticGammaProduct ω₀ ω)
            ((∑ i, ω i) - z) =
          multipleEllipticGammaLogSign ι *
            logDeriv (homogeneousMultipleEllipticGammaProduct ω₀ ω) z := by
  have hbase :=
    homogeneousMultipleEllipticGamma_scaleReflectionHypertranscendenceUniversality
      ω₀ ω hω hminor
  refine ⟨hbase.1, hbase.2.1, ?_, ?_⟩
  · intro c hc z hzB
    exact logDeriv_homogeneousMultipleEllipticGammaProduct_scale
      c hc ω₀ hω₀ ω hω z hzB
  · intro z hzF hzB
    exact logDeriv_homogeneousMultipleEllipticGammaProduct_reflection
      ω₀ ω hω z hzF hzB

/-- **Homogeneous multiple elliptic-Gamma product/log-derivative Ward universality law.**  One
rank-three normalized period minor simultaneously forces hypertranscendence, product parity
covariance under every common scale, zero radial Ward jets on both reflection branches,
logarithmic weight `-1`, and logarithmic parity reflection. -/
theorem homogeneousMultipleEllipticGamma_productLogDerivativeWardUniversality
    [DecidableEq ι] (ω₀ : ℂ) (hω₀ : ω₀ ≠ 0) (ω : ι → ℂ)
    (hω : ∀ i, 0 < (ω i / ω₀).im)
    (hminor : MultipleEllipticGammaHasRankThreeMinor (fun i => ω i / ω₀)) :
    HypertranscendentalOver meromorphicRationalCoordinateField
        (multipleEllipticGammaMero (fun i => ω i / ω₀) hω) ∧
      HypertranscendentalOver meromorphicRationalCoordinateField
        (multipleEllipticGammaLogDerivMero (fun i => ω i / ω₀) hω) ∧
      (∀ (c : ℂ), c ≠ 0 → ∀ z : ℂ,
        homogeneousMultipleEllipticGammaProduct
            (c * ω₀) (fun i => c * ω i) (c * ((∑ i, ω i) - z)) =
          if Even (Fintype.card ι) then
            (homogeneousMultipleEllipticGammaProduct
              (c * ω₀) (fun i => c * ω i) (c * z))⁻¹
          else
            homogeneousMultipleEllipticGammaProduct
              (c * ω₀) (fun i => c * ω i) (c * z)) ∧
      (∀ z : ℂ,
        HasDerivAt
            (fun c : ℂ => homogeneousMultipleEllipticGammaProduct
              (c * ω₀) (fun i => c * ω i) (c * z))
            0 1 ∧
          HasDerivAt
            (fun c : ℂ => homogeneousMultipleEllipticGammaProduct
              (c * ω₀) (fun i => c * ω i) (c * ((∑ i, ω i) - z)))
            0 1) ∧
      (∀ (c : ℂ), c ≠ 0 → ∀ z : ℂ,
        multipleEllipticGammaBackwardProduct
            (fun i => ω i / ω₀) (z / ω₀) ≠ 0 →
        logDeriv
            (homogeneousMultipleEllipticGammaProduct
              (c * ω₀) (fun i => c * ω i))
            (c * z) =
          c⁻¹ * logDeriv
            (homogeneousMultipleEllipticGammaProduct ω₀ ω) z) ∧
      ∀ z : ℂ,
        multipleEllipticGammaForwardProduct
            (fun i => ω i / ω₀) (z / ω₀) ≠ 0 →
        multipleEllipticGammaBackwardProduct
            (fun i => ω i / ω₀) (z / ω₀) ≠ 0 →
        logDeriv (homogeneousMultipleEllipticGammaProduct ω₀ ω)
            ((∑ i, ω i) - z) =
          multipleEllipticGammaLogSign ι *
            logDeriv (homogeneousMultipleEllipticGammaProduct ω₀ ω) z := by
  have hproduct :=
    homogeneousMultipleEllipticGamma_scaleReflectionHypertranscendenceUniversality
      ω₀ ω hω hminor
  have hlog :=
    homogeneousMultipleEllipticGamma_logDerivativeScaleReflectionUniversality
      ω₀ hω₀ ω hω hminor
  exact ⟨hproduct.1, hproduct.2.1, hproduct.2.2.1, hproduct.2.2.2,
    hlog.2.2.1, hlog.2.2.2⟩

/-- The normalized rank-two period family attached to an elliptic-Gamma pair remains in the
upper half-plane. -/
theorem ellipticGamma_rankTwoNormalizedPeriods_upperHalfPlane
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    ∀ i : Fin 2, 0 < (![sigma, tau] i / 1).im := by
  intro i
  fin_cases i
  · simpa using hsigma
  · simpa using htau

/-- A single independent elliptic-Gamma period triple simultaneously certifies external-shift
freeness and the full rank-two homogeneous product/log-derivative Ward phase. -/
structure EllipticGammaSharedPeriodExternalWardCertificate
    {κ : Type*} [DecidableEq κ]
    (s : Finset κ) (h : κ → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im) : Prop where
  externalQuotientMatroidFree :
    differentialFamilyMatroid (F := meromorphicRationalCoordinateField)
        (ellipticGammaExternalQuotientFamily h sigma tau hsigma htau) =
      Matroid.freeOn Set.univ
  externalDefectDifferentialAtomic :
    ∀ (L : κ → Polynomial ℂ),
      (∃ i ∈ s, L i ≠ 0) →
      ∀ {a b : Bottcher.analyticSubring (Set.univ : Set ℂ)}, b ≠ 0 →
      ∀ {f g : ℂ → ℂ}, AnalyticOnNhd ℂ f Set.univ →
      AnalyticOnNhd ℂ g Set.univ →
      Filter.Germ.coeRingHom (Filter.principal Set.univ) f =
        (a : Filter.Germ (Filter.principal Set.univ) ℂ) →
      Filter.Germ.coeRingHom (Filter.principal Set.univ) g =
        (b : Filter.Germ (Filter.principal Set.univ) ℂ) →
      Function.Periodic (fun z ↦ f z / g z) 1 →
      Function.Periodic (fun z ↦ f z / g z) tau →
      ellipticGammaExternalDifferentialFamilySum
          s L h sigma tau hsigma htau ≠
        algebraMap (Bottcher.analyticSubring Set.univ)
            (Bottcher.meroField Set.univ) a /
          algebraMap (Bottcher.analyticSubring Set.univ)
            (Bottcher.meroField Set.univ) b
  productHypertranscendental :
    HypertranscendentalOver meromorphicRationalCoordinateField
      (multipleEllipticGammaMero
        (fun i : Fin 2 => ![sigma, tau] i / 1)
        (ellipticGamma_rankTwoNormalizedPeriods_upperHalfPlane
          sigma tau hsigma htau))
  logDerivativeHypertranscendental :
    HypertranscendentalOver meromorphicRationalCoordinateField
      (multipleEllipticGammaLogDerivMero
        (fun i : Fin 2 => ![sigma, tau] i / 1)
        (ellipticGamma_rankTwoNormalizedPeriods_upperHalfPlane
          sigma tau hsigma htau))
  productScaleReflection :
    ∀ (c : ℂ), c ≠ 0 → ∀ z : ℂ,
      homogeneousMultipleEllipticGammaProduct
          (c * 1) (fun i : Fin 2 => c * ![sigma, tau] i)
          (c * ((∑ i : Fin 2, ![sigma, tau] i) - z)) =
        if Even (Fintype.card (Fin 2)) then
          (homogeneousMultipleEllipticGammaProduct
            (c * 1) (fun i : Fin 2 => c * ![sigma, tau] i) (c * z))⁻¹
        else
          homogeneousMultipleEllipticGammaProduct
            (c * 1) (fun i : Fin 2 => c * ![sigma, tau] i) (c * z)
  radialWardJets :
    ∀ z : ℂ,
      HasDerivAt
          (fun c : ℂ => homogeneousMultipleEllipticGammaProduct
            (c * 1) (fun i : Fin 2 => c * ![sigma, tau] i) (c * z))
          0 1 ∧
        HasDerivAt
          (fun c : ℂ => homogeneousMultipleEllipticGammaProduct
            (c * 1) (fun i : Fin 2 => c * ![sigma, tau] i)
            (c * ((∑ i : Fin 2, ![sigma, tau] i) - z)))
          0 1
  logDerivativeScaleWeight :
    ∀ (c : ℂ), c ≠ 0 → ∀ z : ℂ,
      multipleEllipticGammaBackwardProduct
          (fun i : Fin 2 => ![sigma, tau] i / 1) (z / 1) ≠ 0 →
      logDeriv
          (homogeneousMultipleEllipticGammaProduct
            (c * 1) (fun i : Fin 2 => c * ![sigma, tau] i))
          (c * z) =
        c⁻¹ * logDeriv
          (homogeneousMultipleEllipticGammaProduct 1 ![sigma, tau]) z
  logDerivativeReflection :
    ∀ z : ℂ,
      multipleEllipticGammaForwardProduct
          (fun i : Fin 2 => ![sigma, tau] i / 1) (z / 1) ≠ 0 →
      multipleEllipticGammaBackwardProduct
          (fun i : Fin 2 => ![sigma, tau] i / 1) (z / 1) ≠ 0 →
      logDeriv (homogeneousMultipleEllipticGammaProduct 1 ![sigma, tau])
          ((∑ i : Fin 2, ![sigma, tau] i) - z) =
        multipleEllipticGammaLogSign (Fin 2) *
          logDeriv (homogeneousMultipleEllipticGammaProduct 1 ![sigma, tau]) z

/-- **Shared-period external/Ward universality law.**  For every separated external shift family,
the same rational independence of `(1, sigma, tau)` simultaneously forces rational-base quotient
matroid freeness, elliptic-base defect differential atomicity, rank-two product and logarithmic
derivative hypertranscendence, product scale/reflection covariance, both zero radial Ward jets,
logarithmic scale weight `-1`, and logarithmic parity reflection. -/
theorem ellipticGamma_sharedPeriodExternalWardUniversality
    {κ : Type*} [DecidableEq κ]
    (s : Finset κ) (h : κ → ℂ) (sigma tau : ℂ)
    (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (hnonres : ∀ j, ThetaTranslationNonresonant tau sigma (h j))
    (hsep : ∀ i j, j ≠ i →
      ThetaTranslationNonresonant tau sigma (h j - h i)) :
    EllipticGammaSharedPeriodExternalWardCertificate
      s h sigma tau hsigma htau := by
  have hexternal :=
    ellipticGamma_twoTierExternalFreenessUniversality
      s h sigma tau hsigma htau hindependent hnonres hsep
  have hperiods :=
    ellipticGamma_rankTwoNormalizedPeriods_upperHalfPlane
      sigma tau hsigma htau
  have hminor : MultipleEllipticGammaHasRankThreeMinor
      (fun i : Fin 2 => ![sigma, tau] i / 1) := by
    refine ⟨0, 1, Fin.zero_ne_one, ?_⟩
    simpa using hindependent
  have hward :=
    homogeneousMultipleEllipticGamma_productLogDerivativeWardUniversality
      (ι := Fin 2) 1 one_ne_zero ![sigma, tau] hperiods hminor
  exact
    { externalQuotientMatroidFree := hexternal.1
      externalDefectDifferentialAtomic := hexternal.2
      productHypertranscendental := hward.1
      logDerivativeHypertranscendental := hward.2.1
      productScaleReflection := hward.2.2.1
      radialWardJets := hward.2.2.2.1
      logDerivativeScaleWeight := hward.2.2.2.2.1
      logDerivativeReflection := hward.2.2.2.2.2 }

end

end GaloisForLFunctions
