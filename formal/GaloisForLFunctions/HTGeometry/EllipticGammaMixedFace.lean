import GaloisForLFunctions.HTGeometry.MeromorphicEllipticGamma
import GaloisForLFunctions.HTGeometry.AnalyticSubringEvaluation

/-!
# The actual elliptic-gamma mixed pair face in the global meromorphic field

The entire double products define a nonzero quotient in the global meromorphic differential field.
This file proves that the mixed external-translation/period face of its logarithmic derivative is
exactly the translated Jacobi-theta logarithmic-derivative defect.

The pointwise product calculation initially holds off finitely many zero divisors.  Their product is
a nonzero global analytic germ, so it is nonzero on some neighborhood.  The analytic identity
theorem then promotes the cleared identity from that regular neighborhood to the whole plane.  The
final field theorem therefore has no regularity or nonvanishing hypotheses.
-/

open Filter Topology Set Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance ellipticGammaMixedFaceUnivDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance ellipticGammaMixedFaceUnivDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

@[simp] theorem univGermEval_ellipticGammaForwardAnalytic
    (σ τ z : ℂ) (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    univGermEval z
        (ellipticGammaForwardAnalytic σ τ hσ hτ : Germ (𝓟 Set.univ) ℂ) =
      ellipticGammaForwardProduct σ τ z := by
  rfl

@[simp] theorem univGermEval_ellipticGammaBackwardAnalytic
    (σ τ z : ℂ) (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    univGermEval z
        (ellipticGammaBackwardAnalytic σ τ hσ hτ : Germ (𝓟 Set.univ) ℂ) =
      ellipticGammaBackwardProduct σ τ z := by
  rfl

@[simp] theorem univGermEval_ellipticGammaForwardAnalytic_deriv
    (σ τ z : ℂ) (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    univGermEval z
        (analyticSubringDeriv isOpen_univ
          (ellipticGammaForwardAnalytic σ τ hσ hτ) : Germ (𝓟 Set.univ) ℂ) =
      deriv (ellipticGammaForwardProduct σ τ) z := by
  rfl

@[simp] theorem univGermEval_ellipticGammaBackwardAnalytic_deriv
    (σ τ z : ℂ) (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    univGermEval z
        (analyticSubringDeriv isOpen_univ
          (ellipticGammaBackwardAnalytic σ τ hσ hτ) : Germ (𝓟 Set.univ) ℂ) =
      deriv (ellipticGammaBackwardProduct σ τ) z := by
  rfl

@[simp] theorem univGermEval_thetaAnalytic
    (τ z : ℂ) (hτ : 0 < τ.im) :
    univGermEval z (thetaAnalytic τ hτ : Germ (𝓟 Set.univ) ℂ) =
      jacobiTheta₂ z τ := by
  rfl

@[simp] theorem univGermEval_thetaPrimeAnalytic
    (τ z : ℂ) (hτ : 0 < τ.im) :
    univGermEval z (thetaPrimeAnalytic τ hτ : Germ (𝓟 Set.univ) ℂ) =
      jacobiTheta₂' z τ := by
  rfl

@[simp] theorem univGermEval_constToAnalytic_mixedFace
    (c z : ℂ) :
    univGermEval z
        (constToAnalytic Set.univ c : Germ (Filter.principal Set.univ) ℂ) = c := by
  rfl

/-- On the regular locus, evaluation of the global logarithmic-derivative fraction is the additive
double-sum kernel. -/
theorem univGermEval_ellipticGammaLogDeriv_div_eq_additiveKernel
    {σ τ z : ℂ} (hσ : 0 < σ.im) (hτ : 0 < τ.im)
    (hzF : ellipticGammaForwardProduct σ τ z ≠ 0)
    (hzB : ellipticGammaBackwardProduct σ τ z ≠ 0) :
    univGermEval z
        (ellipticGammaLogDerivNumeratorAnalytic σ τ hσ hτ :
          Germ (𝓟 Set.univ) ℂ) /
      univGermEval z
        (ellipticGammaLogDerivDenominatorAnalytic σ τ hσ hτ :
          Germ (𝓟 Set.univ) ℂ) =
      ellipticGammaAdditiveLogKernel σ τ z := by
  have h := logDeriv_ellipticGammaProduct_eq_additiveKernel hσ hτ hzF hzB
  change logDeriv (fun w => ellipticGammaForwardProduct σ τ w /
    ellipticGammaBackwardProduct σ τ w) z = _ at h
  rw [logDeriv_div z hzF hzB
    (differentiable_ellipticGammaForwardProduct hσ hτ z)
    (differentiable_ellipticGammaBackwardProduct hσ hτ z)] at h
  change
    (deriv (ellipticGammaForwardProduct σ τ) z *
          ellipticGammaBackwardProduct σ τ z -
        ellipticGammaForwardProduct σ τ z *
          deriv (ellipticGammaBackwardProduct σ τ) z) /
      (ellipticGammaForwardProduct σ τ z *
        ellipticGammaBackwardProduct σ τ z) = _
  rw [logDeriv_apply, logDeriv_apply] at h
  field_simp [hzF, hzB] at h ⊢
  linear_combination h

/-- Evaluation of the theta-defect fraction is the pointwise translated logarithmic-derivative
difference on its regular locus. -/
theorem univGermEval_thetaLogDerivDefect_div_eq
    {h τ z : ℂ} (hτ : 0 < τ.im)
    (hz : jacobiTheta₂ z τ ≠ 0) (hzh : jacobiTheta₂ (z + h) τ ≠ 0) :
    univGermEval z
        (thetaLogDerivDefectNumeratorAnalytic h τ hτ : Germ (𝓟 Set.univ) ℂ) /
      univGermEval z
        (thetaLogDerivDefectDenominatorAnalytic h τ hτ : Germ (𝓟 Set.univ) ℂ) =
      thetaLogDeriv (z + h) τ - thetaLogDeriv z τ := by
  change
    (jacobiTheta₂' (z + h) τ * jacobiTheta₂ z τ -
        jacobiTheta₂ (z + h) τ * jacobiTheta₂' z τ) /
      (jacobiTheta₂ (z + h) τ * jacobiTheta₂ z τ) = _
  rw [thetaLogDeriv, thetaLogDeriv]
  field_simp [hz, hzh]

/-! ## Direct structural source faces -/

/-- **First direct elliptic-gamma source face modulo normalization.**  The `sigma`-translation
defect of the genuine elliptic-gamma logarithmic derivative is the `tau`-theta logarithmic
derivative up to the single comparison constant between the constructed and analytic theta
kernels. -/
theorem ellipticGammaLogDerivMero_source_face_sigma
    {sigma tau : ℂ} (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    ∃ c : ℂ,
      addTranslationMeroEquiv sigma
          (ellipticGammaLogDerivMero sigma tau hsigma htau) -
        ellipticGammaLogDerivMero sigma tau hsigma htau =
          thetaLogDerivMero tau htau +
            algebraMap (analyticSubring Set.univ) (meroField Set.univ)
              (constToAnalytic Set.univ c) := by
  obtain ⟨c, hc⟩ :=
    ellipticThetaAdditiveLogKernel_eq_thetaLogDeriv_add_constant htau
  refine ⟨c, ?_⟩
  let D := ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau
  let Q := thetaAnalytic tau htau
  have hmap_ne {a : analyticSubring Set.univ} (ha : a ≠ 0) :
      algebraMap (analyticSubring Set.univ) (meroField Set.univ) a ≠ 0 :=
    fun hz ↦ ha ((IsFractionRing.injective (analyticSubring Set.univ)
      (meroField Set.univ)) (by simpa using hz))
  have hD : D ≠ 0 :=
    ellipticGammaLogDerivDenominatorAnalytic_ne_zero sigma tau hsigma htau
  have hTD : addTranslationAnalyticEquiv sigma D ≠ 0 :=
    fun hz ↦ hD ((addTranslationAnalyticEquiv sigma).injective (by simpa using hz))
  have hQ : Q ≠ 0 := thetaAnalytic_ne_zero tau htau
  dsimp [D, Q] at hD hTD hQ
  let R : analyticSubring Set.univ :=
    addTranslationAnalyticEquiv sigma
          (ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau) *
      ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau *
      thetaAnalytic tau htau
  have hR : R ≠ 0 := by
    dsimp [R]
    exact mul_ne_zero (mul_ne_zero hTD hD) hQ
  obtain ⟨z0, hz0⟩ := exists_univGermEval_ne_zero_of_ne_zero hR
  have hreg := eventually_univGermEval_ne_zero hz0
  rw [ellipticGammaLogDerivMero_eq_div, thetaLogDerivMero,
    map_div₀, addTranslationMeroEquiv_algebraMap,
    addTranslationMeroEquiv_algebraMap]
  field_simp [hmap_ne hD, hmap_ne hTD, hmap_ne hQ]
  simp only [← map_mul, ← map_sub, ← map_add]
  rw [(IsFractionRing.injective (analyticSubring Set.univ)
    (meroField Set.univ)).eq_iff]
  apply analyticSubring_eq_of_eventually_eval_eq (z₀ := z0)
  filter_upwards [hreg] with z hzR
  have hzR' := hzR
  simp only [R, univGermEval_analyticSubring_mul,
    univGermEval_addTranslationAnalyticEquiv,
    ellipticGammaLogDerivDenominatorAnalytic,
    univGermEval_ellipticGammaForwardAnalytic,
    univGermEval_ellipticGammaBackwardAnalytic,
    univGermEval_thetaAnalytic, mul_ne_zero_iff] at hzR'
  rcases hzR' with ⟨⟨⟨hzsF, hzsB⟩, hzF, hzB⟩, hztheta⟩
  have hKs := univGermEval_ellipticGammaLogDeriv_div_eq_additiveKernel
    hsigma htau hzsF hzsB
  have hK := univGermEval_ellipticGammaLogDeriv_div_eq_additiveKernel
    hsigma htau hzF hzB
  have hratio :
      univGermEval (z + sigma)
            (ellipticGammaLogDerivNumeratorAnalytic sigma tau hsigma htau :
              Germ (Filter.principal Set.univ) ℂ) /
          univGermEval (z + sigma)
            (ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau :
              Germ (Filter.principal Set.univ) ℂ) -
        univGermEval z
            (ellipticGammaLogDerivNumeratorAnalytic sigma tau hsigma htau :
              Germ (Filter.principal Set.univ) ℂ) /
          univGermEval z
            (ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau :
              Germ (Filter.principal Set.univ) ℂ) =
      univGermEval z
          (thetaPrimeAnalytic tau htau : Germ (Filter.principal Set.univ) ℂ) /
        univGermEval z
          (thetaAnalytic tau htau : Germ (Filter.principal Set.univ) ℂ) + c := by
    rw [hKs, hK, ellipticGammaAdditiveLogKernel_add_sigma_sub hsigma htau]
    simpa [thetaLogDeriv] using hc z hztheta
  have hds : univGermEval (z + sigma)
      (ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau :
        Germ (Filter.principal Set.univ) ℂ) ≠ 0 := by
    change ellipticGammaForwardProduct sigma tau (z + sigma) *
      ellipticGammaBackwardProduct sigma tau (z + sigma) ≠ 0
    exact mul_ne_zero hzsF hzsB
  have hd : univGermEval z
      (ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau :
        Germ (Filter.principal Set.univ) ℂ) ≠ 0 := by
    change ellipticGammaForwardProduct sigma tau z *
      ellipticGammaBackwardProduct sigma tau z ≠ 0
    exact mul_ne_zero hzF hzB
  simp only [univGermEval_analyticSubring_add,
    univGermEval_analyticSubring_mul,
    univGermEval_analyticSubring_sub,
    univGermEval_addTranslationAnalyticEquiv,
    univGermEval_constToAnalytic_mixedFace]
  field_simp [hds, hd, hztheta] at hratio
  linear_combination hratio

/-- **Second direct elliptic-gamma source face modulo normalization.**  The `tau`-translation
defect is the recentered `sigma`-theta logarithmic derivative up to its comparison constant. -/
theorem ellipticGammaLogDerivMero_source_face_tau
    {sigma tau : ℂ} (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    ∃ d : ℂ,
      addTranslationMeroEquiv tau
          (ellipticGammaLogDerivMero sigma tau hsigma htau) -
        ellipticGammaLogDerivMero sigma tau hsigma htau =
          addTranslationMeroEquiv ((tau - sigma) / 2)
              (thetaLogDerivMero sigma hsigma) +
            algebraMap (analyticSubring Set.univ) (meroField Set.univ)
              (constToAnalytic Set.univ d) := by
  obtain ⟨d, hcomparison⟩ :=
    ellipticThetaAdditiveLogKernel_eq_thetaLogDeriv_add_constant hsigma
  refine ⟨d, ?_⟩
  let c : ℂ := (tau - sigma) / 2
  let D := ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau
  let Q := addTranslationAnalyticEquiv c (thetaAnalytic sigma hsigma)
  have hmap_ne {a : analyticSubring Set.univ} (ha : a ≠ 0) :
      algebraMap (analyticSubring Set.univ) (meroField Set.univ) a ≠ 0 :=
    fun hz ↦ ha ((IsFractionRing.injective (analyticSubring Set.univ)
      (meroField Set.univ)) (by simpa using hz))
  have hD : D ≠ 0 :=
    ellipticGammaLogDerivDenominatorAnalytic_ne_zero sigma tau hsigma htau
  have hTD : addTranslationAnalyticEquiv tau D ≠ 0 :=
    fun hz ↦ hD ((addTranslationAnalyticEquiv tau).injective (by simpa using hz))
  have hQ : Q ≠ 0 :=
    fun hz ↦ thetaAnalytic_ne_zero sigma hsigma
      ((addTranslationAnalyticEquiv c).injective (by simpa [Q] using hz))
  dsimp [D, Q] at hD hTD hQ
  have hQ' : addTranslationAnalyticEquiv ((tau - sigma) / 2)
      (thetaAnalytic sigma hsigma) ≠ 0 := by
    simpa [c] using hQ
  let R : analyticSubring Set.univ :=
    addTranslationAnalyticEquiv tau
          (ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau) *
      ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau *
      addTranslationAnalyticEquiv c (thetaAnalytic sigma hsigma)
  have hR : R ≠ 0 := by
    dsimp [R]
    exact mul_ne_zero (mul_ne_zero hTD hD) hQ
  obtain ⟨z0, hz0⟩ := exists_univGermEval_ne_zero_of_ne_zero hR
  have hreg := eventually_univGermEval_ne_zero hz0
  rw [ellipticGammaLogDerivMero_eq_div, thetaLogDerivMero,
    map_div₀, addTranslationMeroEquiv_algebraMap,
    addTranslationMeroEquiv_algebraMap,
    map_div₀, addTranslationMeroEquiv_algebraMap,
    addTranslationMeroEquiv_algebraMap]
  field_simp [hmap_ne hD, hmap_ne hTD, hmap_ne hQ']
  simp only [← map_mul, ← map_sub, ← map_add]
  rw [(IsFractionRing.injective (analyticSubring Set.univ)
    (meroField Set.univ)).eq_iff]
  apply analyticSubring_eq_of_eventually_eval_eq (z₀ := z0)
  filter_upwards [hreg] with z hzR
  have hzR' := hzR
  simp only [R, univGermEval_analyticSubring_mul,
    univGermEval_addTranslationAnalyticEquiv,
    ellipticGammaLogDerivDenominatorAnalytic,
    univGermEval_ellipticGammaForwardAnalytic,
    univGermEval_ellipticGammaBackwardAnalytic,
    univGermEval_thetaAnalytic, mul_ne_zero_iff] at hzR'
  rcases hzR' with ⟨⟨⟨hztF, hztB⟩, hzF, hzB⟩, hztheta⟩
  have hKt := univGermEval_ellipticGammaLogDeriv_div_eq_additiveKernel
    hsigma htau hztF hztB
  have hK := univGermEval_ellipticGammaLogDeriv_div_eq_additiveKernel
    hsigma htau hzF hzB
  have hratio :
      univGermEval (z + tau)
            (ellipticGammaLogDerivNumeratorAnalytic sigma tau hsigma htau :
              Germ (Filter.principal Set.univ) ℂ) /
          univGermEval (z + tau)
            (ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau :
              Germ (Filter.principal Set.univ) ℂ) -
        univGermEval z
            (ellipticGammaLogDerivNumeratorAnalytic sigma tau hsigma htau :
              Germ (Filter.principal Set.univ) ℂ) /
          univGermEval z
            (ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau :
              Germ (Filter.principal Set.univ) ℂ) =
      univGermEval (z + c)
            (thetaPrimeAnalytic sigma hsigma : Germ (Filter.principal Set.univ) ℂ) /
        univGermEval (z + c)
          (thetaAnalytic sigma hsigma : Germ (Filter.principal Set.univ) ℂ) + d := by
    rw [hKt, hK, ellipticGammaAdditiveLogKernel_add_tau_sub hsigma htau]
    dsimp only [c]
    simpa [thetaLogDeriv, add_assoc] using
      hcomparison (z + (tau - sigma) / 2) hztheta
  have hdt : univGermEval (z + tau)
      (ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau :
        Germ (Filter.principal Set.univ) ℂ) ≠ 0 := by
    change ellipticGammaForwardProduct sigma tau (z + tau) *
      ellipticGammaBackwardProduct sigma tau (z + tau) ≠ 0
    exact mul_ne_zero hztF hztB
  have hd : univGermEval z
      (ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau :
        Germ (Filter.principal Set.univ) ℂ) ≠ 0 := by
    change ellipticGammaForwardProduct sigma tau z *
      ellipticGammaBackwardProduct sigma tau z ≠ 0
    exact mul_ne_zero hzF hzB
  simp only [univGermEval_analyticSubring_add,
    univGermEval_analyticSubring_mul,
    univGermEval_analyticSubring_sub,
    univGermEval_addTranslationAnalyticEquiv,
    univGermEval_constToAnalytic_mixedFace]
  field_simp [hdt, hd, hztheta] at hratio
  linear_combination hratio

/-- **Actual elliptic-gamma mixed pair face.** For the logarithmic derivative of the genuine
elliptic-gamma double product, the mixed external translation `h` and structural period `σ` is
exactly the translated Jacobi-theta logarithmic-derivative defect.  This is an unconditional
identity in the global meromorphic differential field. -/
theorem ellipticGammaLogDerivMero_mixed_face_sigma
    {σ τ h : ℂ} (hσ : 0 < σ.im) (hτ : 0 < τ.im) :
    addTranslationMeroEquiv σ
        (addTranslationMeroEquiv h (ellipticGammaLogDerivMero σ τ hσ hτ) -
          ellipticGammaLogDerivMero σ τ hσ hτ) -
      (addTranslationMeroEquiv h (ellipticGammaLogDerivMero σ τ hσ hτ) -
        ellipticGammaLogDerivMero σ τ hσ hτ) =
      thetaLogDerivDefectMero h τ hτ := by
  rw [addTranslationMeroEquiv_mixed_defect_comm]
  obtain ⟨c, hface⟩ := ellipticGammaLogDerivMero_source_face_sigma hσ hτ
  rw [hface, (addTranslationMeroEquiv h).map_add,
    addTranslationMeroEquiv_const,
    thetaLogDerivDefectMero]
  ring

end

end GaloisForLFunctions
