import GaloisForLFunctions.HTGeometry.MeromorphicEllipticCompositumDifferenceDifferential
import GaloisForLFunctions.HTGeometry.EllipticGammaProductSourceEquation

/-!
# The actual elliptic-gamma defect as a rank-three primitive system

This module packages every external translation defect of the genuine elliptic-gamma
logarithmic derivative as a compatible primitive over `E_sigma E_tau`.  The `sigma` face is the
existing `tau`-theta defect.  The `tau` face is the recentered `sigma`-theta defect forced by the
second polarized product equation.  The period-one face vanishes exactly.
-/

open Filter Topology Set Function Complex
open scoped Differential Topology

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance ellipticGammaPairedIncrementDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance ellipticGammaPairedIncrementComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance ellipticGammaPairedIncrementComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  ((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance ellipticGammaPairedIncrementAmbientDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance ellipticGammaPairedIncrementRestrictedDifferential
    (sigma tau : ℂ) :
    Differential (meromorphicEllipticCompositum sigma tau) :=
  meromorphicEllipticCompositumDifferential sigma tau

/-! ## Exact period one -/

theorem addTranslationAnalyticEquiv_ellipticGammaForwardAnalytic_one
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    addTranslationAnalyticEquiv 1
        (ellipticGammaForwardAnalytic sigma tau hsigma htau) =
      ellipticGammaForwardAnalytic sigma tau hsigma htau := by
  apply Subtype.ext
  let htr : Tendsto (addTranslation 1) (Filter.principal Set.univ)
      (Filter.principal Set.univ) :=
    tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)
  change
    (Germ.ofFun (l := Filter.principal Set.univ)
      (ellipticGammaForwardProduct sigma tau)).compTendsto
        (addTranslation 1) htr =
      Germ.ofFun (l := Filter.principal Set.univ)
        (ellipticGammaForwardProduct sigma tau)
  rw [Germ.coe_compTendsto, Germ.coe_eq]
  exact eventually_principal.mpr fun z _ ↦ by
    simpa [addTranslation] using
      ellipticGammaForwardProduct_add_one sigma tau z

theorem addTranslationAnalyticEquiv_ellipticGammaBackwardAnalytic_one
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    addTranslationAnalyticEquiv 1
        (ellipticGammaBackwardAnalytic sigma tau hsigma htau) =
      ellipticGammaBackwardAnalytic sigma tau hsigma htau := by
  apply Subtype.ext
  let htr : Tendsto (addTranslation 1) (Filter.principal Set.univ)
      (Filter.principal Set.univ) :=
    tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)
  change
    (Germ.ofFun (l := Filter.principal Set.univ)
      (ellipticGammaBackwardProduct sigma tau)).compTendsto
        (addTranslation 1) htr =
      Germ.ofFun (l := Filter.principal Set.univ)
        (ellipticGammaBackwardProduct sigma tau)
  rw [Germ.coe_compTendsto, Germ.coe_eq]
  exact eventually_principal.mpr fun z _ ↦ by
    simpa [addTranslation] using
      ellipticGammaBackwardProduct_add_one sigma tau z

/-- The genuine elliptic-gamma meromorphic product is fixed by translation by one. -/
theorem addTranslationMeroEquiv_ellipticGammaMero_one
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    addTranslationMeroEquiv 1 (ellipticGammaMero sigma tau hsigma htau) =
      ellipticGammaMero sigma tau hsigma htau := by
  rw [ellipticGammaMero, map_div₀,
    addTranslationMeroEquiv_algebraMap,
    addTranslationMeroEquiv_algebraMap,
    addTranslationAnalyticEquiv_ellipticGammaForwardAnalytic_one,
    addTranslationAnalyticEquiv_ellipticGammaBackwardAnalytic_one]

/-- The logarithmic derivative of the genuine elliptic-gamma product is period one. -/
theorem addTranslationMeroEquiv_ellipticGammaLogDerivMero_one
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    addTranslationMeroEquiv 1
        (ellipticGammaLogDerivMero sigma tau hsigma htau) =
      ellipticGammaLogDerivMero sigma tau hsigma htau := by
  rw [ellipticGammaLogDerivMero, map_div₀,
    addTranslationMeroEquiv_deriv,
    addTranslationMeroEquiv_ellipticGammaMero_one]

/-! ## The polarized `tau` face -/

/-- The mixed external-translation/`tau` face of the additive product kernel is the
`sigma`-theta logarithmic-derivative defect at the forced recentered coordinate. -/
theorem ellipticGammaAdditiveLogKernel_mixed_defect_tau
    {sigma tau h z : ℂ} (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hz : jacobiTheta₂ (z + (tau - sigma) / 2) sigma ≠ 0)
    (hzh : jacobiTheta₂ (z + (tau - sigma) / 2 + h) sigma ≠ 0) :
    (ellipticGammaAdditiveLogKernel sigma tau (z + h + tau) -
        ellipticGammaAdditiveLogKernel sigma tau (z + h)) -
      (ellipticGammaAdditiveLogKernel sigma tau (z + tau) -
        ellipticGammaAdditiveLogKernel sigma tau z) =
      thetaLogDeriv (z + (tau - sigma) / 2 + h) sigma -
        thetaLogDeriv (z + (tau - sigma) / 2) sigma := by
  rw [ellipticGammaAdditiveLogKernel_add_tau_sub hsigma htau,
    ellipticGammaAdditiveLogKernel_add_tau_sub hsigma htau]
  simpa [add_assoc, add_comm, add_left_comm] using
    ellipticThetaAdditiveLogKernel_defect_eq_thetaLogDerivDefect
      hsigma hz hzh

/-- **Second actual elliptic-gamma mixed face.**  In the global meromorphic differential field,
the `tau`-increment of an external defect is the translated `sigma`-theta defect dictated by the
polarized coordinate convention. -/
theorem ellipticGammaLogDerivMero_mixed_face_tau
    {sigma tau h : ℂ} (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    addTranslationMeroEquiv tau
        (addTranslationMeroEquiv h
            (ellipticGammaLogDerivMero sigma tau hsigma htau) -
          ellipticGammaLogDerivMero sigma tau hsigma htau) -
      (addTranslationMeroEquiv h
          (ellipticGammaLogDerivMero sigma tau hsigma htau) -
        ellipticGammaLogDerivMero sigma tau hsigma htau) =
      addTranslationMeroEquiv ((tau - sigma) / 2)
        (thetaLogDerivDefectMero h sigma hsigma) := by
  let D := ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau
  let Q := thetaLogDerivDefectDenominatorAnalytic h sigma hsigma
  let c : ℂ := (tau - sigma) / 2
  have hmap_ne {a : analyticSubring Set.univ} (ha : a ≠ 0) :
      algebraMap (analyticSubring Set.univ) (meroField Set.univ) a ≠ 0 :=
    fun hz ↦ ha ((IsFractionRing.injective (analyticSubring Set.univ)
      (meroField Set.univ)) (by simpa using hz))
  have hD : D ≠ 0 :=
    ellipticGammaLogDerivDenominatorAnalytic_ne_zero sigma tau hsigma htau
  have hTD (q : ℂ) : addTranslationAnalyticEquiv q D ≠ 0 :=
    fun hz ↦ hD ((addTranslationAnalyticEquiv q).injective (by simpa using hz))
  have hQ : Q ≠ 0 := thetaLogDerivDefectDenominatorAnalytic_ne_zero h sigma hsigma
  have hTQ : addTranslationAnalyticEquiv c Q ≠ 0 :=
    fun hz ↦ hQ ((addTranslationAnalyticEquiv c).injective (by simpa using hz))
  dsimp [D, Q] at hD hTD hQ hTQ
  let R : analyticSubring Set.univ :=
    addTranslationAnalyticEquiv (tau + h)
          (ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau) *
      addTranslationAnalyticEquiv tau
          (ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau) *
      addTranslationAnalyticEquiv h
          (ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau) *
      ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau *
      addTranslationAnalyticEquiv c
        (thetaLogDerivDefectDenominatorAnalytic h sigma hsigma)
  have hR : R ≠ 0 := by
    dsimp [R]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (hTD (tau + h)) (hTD tau)) (hTD h)) hD) hTQ
  obtain ⟨z0, hz0⟩ := exists_univGermEval_ne_zero_of_ne_zero hR
  have hreg := eventually_univGermEval_ne_zero hz0
  rw [ellipticGammaLogDerivMero_eq_div]
  simp only [map_sub, map_div₀, addTranslationMeroEquiv_algebraMap]
  simp_rw [addTranslationAnalyticEquiv_add]
  rw [thetaLogDerivDefectMero_eq_div, map_div₀,
    addTranslationMeroEquiv_algebraMap,
    addTranslationMeroEquiv_algebraMap]
  have hTQ' : addTranslationAnalyticEquiv ((tau - sigma) / 2)
      (thetaLogDerivDefectDenominatorAnalytic h sigma hsigma) ≠ 0 := by
    simpa [c, Q] using hTQ
  apply (eq_div_iff (hmap_ne hTQ')).mpr
  field_simp [hmap_ne hD, hmap_ne (hTD h), hmap_ne (hTD tau),
    hmap_ne (hTD (tau + h))]
  simp only [← map_mul, ← map_sub]
  rw [(IsFractionRing.injective (analyticSubring Set.univ)
    (meroField Set.univ)).eq_iff]
  apply analyticSubring_eq_of_eventually_eval_eq (z₀ := z0)
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
    ⟨⟨⟨⟨⟨hztahF, hztahB⟩, hztF, hztB⟩, hzhF, hzhB⟩, hzF, hzB⟩,
      hzc_h_theta, hzc_theta⟩
  have hKtah := univGermEval_ellipticGammaLogDeriv_div_eq_additiveKernel
    hsigma htau hztahF hztahB
  have hKt := univGermEval_ellipticGammaLogDeriv_div_eq_additiveKernel
    hsigma htau hztF hztB
  have hKh := univGermEval_ellipticGammaLogDeriv_div_eq_additiveKernel
    hsigma htau hzhF hzhB
  have hK := univGermEval_ellipticGammaLogDeriv_div_eq_additiveKernel
    hsigma htau hzF hzB
  have htheta := univGermEval_thetaLogDerivDefect_div_eq
    hsigma hzc_theta hzc_h_theta
  have hmix := ellipticGammaAdditiveLogKernel_mixed_defect_tau
    hsigma htau hzc_theta hzc_h_theta
  have hratio :
      (univGermEval (z + (tau + h))
            (ellipticGammaLogDerivNumeratorAnalytic sigma tau hsigma htau :
              Germ (𝓟 Set.univ) ℂ) /
          univGermEval (z + (tau + h))
            (ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau :
              Germ (𝓟 Set.univ) ℂ) -
        univGermEval (z + tau)
            (ellipticGammaLogDerivNumeratorAnalytic sigma tau hsigma htau :
              Germ (𝓟 Set.univ) ℂ) /
          univGermEval (z + tau)
            (ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau :
              Germ (𝓟 Set.univ) ℂ)) -
      (univGermEval (z + h)
            (ellipticGammaLogDerivNumeratorAnalytic sigma tau hsigma htau :
              Germ (𝓟 Set.univ) ℂ) /
          univGermEval (z + h)
            (ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau :
              Germ (𝓟 Set.univ) ℂ) -
        univGermEval z
            (ellipticGammaLogDerivNumeratorAnalytic sigma tau hsigma htau :
              Germ (𝓟 Set.univ) ℂ) /
          univGermEval z
            (ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau :
              Germ (𝓟 Set.univ) ℂ)) =
      univGermEval (z + c)
          (thetaLogDerivDefectNumeratorAnalytic h sigma hsigma :
            Germ (𝓟 Set.univ) ℂ) /
        univGermEval (z + c)
          (thetaLogDerivDefectDenominatorAnalytic h sigma hsigma :
            Germ (𝓟 Set.univ) ℂ) := by
    rw [hKtah, hKt, hKh, hK, htheta]
    rw [show z + (tau + h) = z + h + tau by ring]
    dsimp only [c]
    linear_combination hmix
  have hdtah : univGermEval (z + (tau + h))
      (ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau :
        Germ (𝓟 Set.univ) ℂ) ≠ 0 := by
    change ellipticGammaForwardProduct sigma tau (z + (tau + h)) *
      ellipticGammaBackwardProduct sigma tau (z + (tau + h)) ≠ 0
    exact mul_ne_zero hztahF hztahB
  have hdt : univGermEval (z + tau)
      (ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau :
        Germ (𝓟 Set.univ) ℂ) ≠ 0 := by
    change ellipticGammaForwardProduct sigma tau (z + tau) *
      ellipticGammaBackwardProduct sigma tau (z + tau) ≠ 0
    exact mul_ne_zero hztF hztB
  have hdh : univGermEval (z + h)
      (ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau :
        Germ (𝓟 Set.univ) ℂ) ≠ 0 := by
    change ellipticGammaForwardProduct sigma tau (z + h) *
      ellipticGammaBackwardProduct sigma tau (z + h) ≠ 0
    exact mul_ne_zero hzhF hzhB
  have hd : univGermEval z
      (ellipticGammaLogDerivDenominatorAnalytic sigma tau hsigma htau :
        Germ (𝓟 Set.univ) ℂ) ≠ 0 := by
    change ellipticGammaForwardProduct sigma tau z *
      ellipticGammaBackwardProduct sigma tau z ≠ 0
    exact mul_ne_zero hzF hzB
  have hq : univGermEval (z + c)
      (thetaLogDerivDefectDenominatorAnalytic h sigma hsigma :
        Germ (𝓟 Set.univ) ℂ) ≠ 0 := by
    change jacobiTheta₂ (z + c + h) sigma * jacobiTheta₂ (z + c) sigma ≠ 0
    exact mul_ne_zero hzc_h_theta hzc_theta
  simp only [univGermEval_analyticSubring_mul,
    univGermEval_analyticSubring_sub,
    univGermEval_addTranslationAnalyticEquiv]
  field_simp [hdtah, hdt, hdh, hd, hq] at hratio
  linear_combination hratio

/-! ## The compatible primitive family -/

/-- The actual external translation defect of the genuine elliptic-gamma logarithmic
derivative. -/
def ellipticGammaExternalLogDerivDefectMero
    (h sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    meroField Set.univ :=
  addTranslationMeroEquiv h
      (ellipticGammaLogDerivMero sigma tau hsigma htau) -
    ellipticGammaLogDerivMero sigma tau hsigma htau

theorem addTranslationMeroEquiv_ellipticGammaExternalDefect_one
    (h sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    addTranslationMeroEquiv 1
        (ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau) =
      ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau := by
  rw [ellipticGammaExternalLogDerivDefectMero, map_sub,
    addTranslationMeroEquiv_add]
  rw [show 1 + h = h + 1 by ring, ← addTranslationMeroEquiv_add,
    addTranslationMeroEquiv_ellipticGammaLogDerivMero_one]

/-- Every theta defect belongs to its concrete elliptic meromorphic field. -/
theorem thetaLogDerivDefectMero_mem_ellipticMeroField
    (h tau : ℂ) (htau : 0 < tau.im) :
    thetaLogDerivDefectMero h tau htau ∈ ellipticMeroField tau := by
  rw [mem_ellipticMeroField_iff]
  exact ⟨addTranslationMeroEquiv_thetaLogDerivDefect_one h tau htau,
    addTranslationMeroEquiv_thetaLogDerivDefect_tau h tau htau⟩

/-- The three actual increment cocycles, valued in the paired elliptic compositum. -/
def ellipticGammaExternalDefectIncrement
    (h sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    Fin 3 → meromorphicEllipticCompositum sigma tau := fun i ↦
  if i = 0 then 0
  else if i = 1 then ⟨thetaLogDerivDefectMero h tau htau,
      (show ellipticMeroField tau ≤ meromorphicEllipticCompositum sigma tau by
        rw [meromorphicEllipticCompositum]
        exact le_sup_right)
        (thetaLogDerivDefectMero_mem_ellipticMeroField h tau htau)⟩
  else ⟨addTranslationMeroEquiv ((tau - sigma) / 2)
        (thetaLogDerivDefectMero h sigma hsigma),
      (show ellipticMeroField sigma ≤ meromorphicEllipticCompositum sigma tau by
        rw [meromorphicEllipticCompositum]
        exact le_sup_left)
        (addTranslationMeroAlgEquiv_mem_ellipticMeroField sigma
          ((tau - sigma) / 2)
          (thetaLogDerivDefectMero_mem_ellipticMeroField h sigma hsigma))⟩

@[simp]
theorem ellipticGammaExternalDefectIncrement_zero_coe
    (h sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    ((ellipticGammaExternalDefectIncrement h sigma tau hsigma htau 0 :
        meromorphicEllipticCompositum sigma tau) : meroField Set.univ) = 0 := by
  simp [ellipticGammaExternalDefectIncrement]

@[simp]
theorem ellipticGammaExternalDefectIncrement_one_coe
    (h sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    ((ellipticGammaExternalDefectIncrement h sigma tau hsigma htau 1 :
        meromorphicEllipticCompositum sigma tau) : meroField Set.univ) =
      thetaLogDerivDefectMero h tau htau := by
  simp [ellipticGammaExternalDefectIncrement]

@[simp]
theorem ellipticGammaExternalDefectIncrement_two_coe
    (h sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    ((ellipticGammaExternalDefectIncrement h sigma tau hsigma htau 2 :
        meromorphicEllipticCompositum sigma tau) : meroField Set.univ) =
      addTranslationMeroEquiv ((tau - sigma) / 2)
        (thetaLogDerivDefectMero h sigma hsigma) := by
  simp [ellipticGammaExternalDefectIncrement]

/-- The actual external defect has the three displayed base-field increments under the finite
rank-three global source action. -/
theorem ellipticGammaExternalDefect_shift
    (h sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (i : Fin 3) :
    (rankThreeGeneratorMeromorphicDifferenceDifferentialField
        (ellipticGammaSourcePeriods sigma tau)).aut i
        (ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau) =
      ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau +
        algebraMap (meromorphicEllipticCompositum sigma tau)
          (meroField Set.univ)
          (ellipticGammaExternalDefectIncrement h sigma tau hsigma htau i) := by
  fin_cases i
  · simp only [rankThreeGeneratorMeromorphicDifferenceDifferentialField,
      ellipticGammaSourcePeriods]
    change addTranslationMeroEquiv 1
        (ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau) = _
    rw [addTranslationMeroEquiv_ellipticGammaExternalDefect_one]
    simp
  · simp only [rankThreeGeneratorMeromorphicDifferenceDifferentialField,
      ellipticGammaSourcePeriods]
    change addTranslationMeroEquiv sigma
        (ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau) =
      ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau +
        thetaLogDerivDefectMero h tau htau
    have hface := ellipticGammaLogDerivMero_mixed_face_sigma
      (h := h) hsigma htau
    change addTranslationMeroEquiv sigma
        (ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau) -
      ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau =
        thetaLogDerivDefectMero h tau htau at hface
    simpa only [add_comm] using
      sub_eq_iff_eq_add.mp hface
  · simp only [rankThreeGeneratorMeromorphicDifferenceDifferentialField,
      ellipticGammaSourcePeriods]
    change addTranslationMeroEquiv tau
        (ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau) =
      ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau +
        addTranslationMeroEquiv ((tau - sigma) / 2)
          (thetaLogDerivDefectMero h sigma hsigma)
    have hface := ellipticGammaLogDerivMero_mixed_face_tau
      (h := h) hsigma htau
    change addTranslationMeroEquiv tau
        (ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau) -
      ellipticGammaExternalLogDerivDefectMero h sigma tau hsigma htau =
        addTranslationMeroEquiv ((tau - sigma) / 2)
          (thetaLogDerivDefectMero h sigma hsigma) at hface
    simpa only [add_comm] using
      sub_eq_iff_eq_add.mp hface

end

end GaloisForLFunctions
