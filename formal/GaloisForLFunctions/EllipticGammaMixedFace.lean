import GaloisForLFunctions.MeromorphicEllipticGamma
import GaloisForLFunctions.AnalyticSubringEvaluation

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
  let D := ellipticGammaLogDerivDenominatorAnalytic σ τ hσ hτ
  let Q := thetaLogDerivDefectDenominatorAnalytic h τ hτ
  have hmap_ne {a : analyticSubring Set.univ} (ha : a ≠ 0) :
      algebraMap (analyticSubring Set.univ) (meroField Set.univ) a ≠ 0 :=
    fun hz => ha ((IsFractionRing.injective (analyticSubring Set.univ)
      (meroField Set.univ)) (by simpa using hz))
  have hD : D ≠ 0 := ellipticGammaLogDerivDenominatorAnalytic_ne_zero σ τ hσ hτ
  have hTD (q : ℂ) : addTranslationAnalyticEquiv q D ≠ 0 :=
    fun hz => hD ((addTranslationAnalyticEquiv q).injective (by simpa using hz))
  have hQ : Q ≠ 0 := thetaLogDerivDefectDenominatorAnalytic_ne_zero h τ hτ
  dsimp [D, Q] at hD hTD hQ
  let R : analyticSubring Set.univ :=
    addTranslationAnalyticEquiv (σ + h)
          (ellipticGammaLogDerivDenominatorAnalytic σ τ hσ hτ) *
      addTranslationAnalyticEquiv σ
          (ellipticGammaLogDerivDenominatorAnalytic σ τ hσ hτ) *
      addTranslationAnalyticEquiv h
          (ellipticGammaLogDerivDenominatorAnalytic σ τ hσ hτ) *
      ellipticGammaLogDerivDenominatorAnalytic σ τ hσ hτ *
      thetaLogDerivDefectDenominatorAnalytic h τ hτ
  have hR : R ≠ 0 := by
    dsimp [R]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (hTD (σ + h)) (hTD σ)) (hTD h)) hD) hQ
  obtain ⟨z₀, hz₀⟩ := exists_univGermEval_ne_zero_of_ne_zero hR
  have hreg := eventually_univGermEval_ne_zero hz₀
  rw [ellipticGammaLogDerivMero_eq_div]
  simp only [map_sub, map_div₀, addTranslationMeroEquiv_algebraMap]
  simp_rw [addTranslationAnalyticEquiv_add]
  rw [thetaLogDerivDefectMero_eq_div]
  field_simp [hmap_ne hD, hmap_ne (hTD h), hmap_ne (hTD σ),
    hmap_ne (hTD (σ + h)), hmap_ne hQ]
  simp only [← map_mul, ← map_sub]
  rw [(IsFractionRing.injective (analyticSubring Set.univ)
    (meroField Set.univ)).eq_iff]
  apply analyticSubring_eq_of_eventually_eval_eq (z₀ := z₀)
  filter_upwards [hreg] with z hzR
  have hzR' := hzR
  simp only [R, univGermEval_analyticSubring_mul,
    univGermEval_addTranslationAnalyticEquiv,
    ellipticGammaLogDerivDenominatorAnalytic,
    thetaLogDerivDefectDenominatorAnalytic,
    univGermEval_ellipticGammaForwardAnalytic,
    univGermEval_ellipticGammaBackwardAnalytic,
    univGermEval_thetaAnalytic, mul_ne_zero_iff] at hzR'
  rcases hzR' with
    ⟨⟨⟨⟨⟨hzshF, hzshB⟩, hzsF, hzsB⟩, hzhF, hzhB⟩, hzF, hzB⟩,
      hzhθ, hzθ⟩
  have hKsh := univGermEval_ellipticGammaLogDeriv_div_eq_additiveKernel
    hσ hτ hzshF hzshB
  have hKs := univGermEval_ellipticGammaLogDeriv_div_eq_additiveKernel
    hσ hτ hzsF hzsB
  have hKh := univGermEval_ellipticGammaLogDeriv_div_eq_additiveKernel
    hσ hτ hzhF hzhB
  have hK := univGermEval_ellipticGammaLogDeriv_div_eq_additiveKernel
    hσ hτ hzF hzB
  have hθ := univGermEval_thetaLogDerivDefect_div_eq hτ hzθ hzhθ
  have hmix := ellipticGammaAdditiveLogKernel_mixed_defect_sigma
    hσ hτ hzθ hzhθ
  have hratio :
      (univGermEval (z + (σ + h))
            (ellipticGammaLogDerivNumeratorAnalytic σ τ hσ hτ :
              Germ (𝓟 Set.univ) ℂ) /
          univGermEval (z + (σ + h))
            (ellipticGammaLogDerivDenominatorAnalytic σ τ hσ hτ :
              Germ (𝓟 Set.univ) ℂ) -
        univGermEval (z + σ)
            (ellipticGammaLogDerivNumeratorAnalytic σ τ hσ hτ :
              Germ (𝓟 Set.univ) ℂ) /
          univGermEval (z + σ)
            (ellipticGammaLogDerivDenominatorAnalytic σ τ hσ hτ :
              Germ (𝓟 Set.univ) ℂ)) -
      (univGermEval (z + h)
            (ellipticGammaLogDerivNumeratorAnalytic σ τ hσ hτ :
              Germ (𝓟 Set.univ) ℂ) /
          univGermEval (z + h)
            (ellipticGammaLogDerivDenominatorAnalytic σ τ hσ hτ :
              Germ (𝓟 Set.univ) ℂ) -
        univGermEval z
            (ellipticGammaLogDerivNumeratorAnalytic σ τ hσ hτ :
              Germ (𝓟 Set.univ) ℂ) /
          univGermEval z
            (ellipticGammaLogDerivDenominatorAnalytic σ τ hσ hτ :
              Germ (𝓟 Set.univ) ℂ)) =
      univGermEval z
          (thetaLogDerivDefectNumeratorAnalytic h τ hτ :
            Germ (𝓟 Set.univ) ℂ) /
        univGermEval z
          (thetaLogDerivDefectDenominatorAnalytic h τ hτ :
            Germ (𝓟 Set.univ) ℂ) := by
    rw [hKsh, hKs, hKh, hK, hθ]
    rw [show z + (σ + h) = z + h + σ by ring]
    linear_combination hmix
  have hdsh : univGermEval (z + (σ + h))
      (ellipticGammaLogDerivDenominatorAnalytic σ τ hσ hτ :
        Germ (𝓟 Set.univ) ℂ) ≠ 0 := by
    change ellipticGammaForwardProduct σ τ (z + (σ + h)) *
      ellipticGammaBackwardProduct σ τ (z + (σ + h)) ≠ 0
    exact mul_ne_zero hzshF hzshB
  have hds : univGermEval (z + σ)
      (ellipticGammaLogDerivDenominatorAnalytic σ τ hσ hτ :
        Germ (𝓟 Set.univ) ℂ) ≠ 0 := by
    change ellipticGammaForwardProduct σ τ (z + σ) *
      ellipticGammaBackwardProduct σ τ (z + σ) ≠ 0
    exact mul_ne_zero hzsF hzsB
  have hdh : univGermEval (z + h)
      (ellipticGammaLogDerivDenominatorAnalytic σ τ hσ hτ :
        Germ (𝓟 Set.univ) ℂ) ≠ 0 := by
    change ellipticGammaForwardProduct σ τ (z + h) *
      ellipticGammaBackwardProduct σ τ (z + h) ≠ 0
    exact mul_ne_zero hzhF hzhB
  have hd : univGermEval z
      (ellipticGammaLogDerivDenominatorAnalytic σ τ hσ hτ :
        Germ (𝓟 Set.univ) ℂ) ≠ 0 := by
    change ellipticGammaForwardProduct σ τ z *
      ellipticGammaBackwardProduct σ τ z ≠ 0
    exact mul_ne_zero hzF hzB
  have hq : univGermEval z
      (thetaLogDerivDefectDenominatorAnalytic h τ hτ :
        Germ (𝓟 Set.univ) ℂ) ≠ 0 := by
    change jacobiTheta₂ (z + h) τ * jacobiTheta₂ z τ ≠ 0
    exact mul_ne_zero hzhθ hzθ
  simp only [univGermEval_analyticSubring_mul,
    univGermEval_analyticSubring_sub,
    univGermEval_addTranslationAnalyticEquiv]
  field_simp [hdsh, hds, hdh, hd, hq] at hratio
  linear_combination hratio

end

end GaloisForLFunctions
