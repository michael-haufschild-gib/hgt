import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaFaceHierarchy
import GaloisForLFunctions.HTGeometry.EllipticGammaRationalBaseMatroid

/-!
# Rank-three-minor hypertranscendence for every multiple elliptic gamma order

The genuine multiple elliptic gamma attached to a finite period family is
hypertranscendental as soon as two distinct periods, together with `1`, are rationally
linearly independent. No independence is imposed on the remaining periods.

The proof first identifies the two-period multiple product with a translate of the genuine
elliptic gamma. It then repeatedly uses the intrinsic coface equation and additive-defect escape
to climb from that rank-three minor to the full all-order product.
-/

open Complex Set Filter Topology
open scoped BigOperators Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance multipleEllipticGammaHTUnivDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance multipleEllipticGammaHTComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance multipleEllipticGammaHTComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  meromorphicEllipticCompositumComplexAlgebraMero

local instance multipleEllipticGammaHTMeroDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance multipleEllipticGammaHTComplexDifferential : Differential ℂ where
  deriv := 0

local instance multipleEllipticGammaHTMeroCharZero : CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap ℂ (meroField Set.univ)).injective

local instance multipleEllipticGammaHTComplexDifferentialAlgebra :
    DifferentialAlgebra ℂ (meroField Set.univ) :=
  ⟨fun c ↦ by
    rw [meroField_deriv_algebraMap_complex_rationalBase]
    change (0 : meroField Set.univ) = algebraMap ℂ (meroField Set.univ) 0
    rw [map_zero]⟩

local instance multipleEllipticGammaHTCoordinateDifferential :
    Differential meromorphicRationalCoordinateField :=
  derivationClosedDifferential _
    meromorphicRationalCoordinateField_derivationClosed

local instance multipleEllipticGammaHTCoordinateDifferentialAlgebra :
    DifferentialAlgebra meromorphicRationalCoordinateField
      (meroField Set.univ) :=
  ⟨fun x ↦ derivationClosedDifferential_apply
    meromorphicRationalCoordinateField
    meromorphicRationalCoordinateField_derivationClosed x⟩

/-! ## Exact two-period normalization -/

theorem multipleEllipticGammaCoordinate_eq_ellipticThetaCoordinate
    (tau z : ℂ) :
    multipleEllipticGammaCoordinate z =
      ellipticThetaCoordinate tau (z - (1 + tau) / 2) := by
  rw [multipleEllipticGammaCoordinate, ellipticThetaCoordinate]
  rw [mul_sub, Complex.exp_sub]
  have hpi : Complex.exp (Real.pi * I) = -1 := Complex.exp_pi_mul_I
  rw [show 2 * Real.pi * I * ((1 + tau) / 2) =
      Real.pi * I + Real.pi * I * tau by ring, Complex.exp_add, hpi]
  field_simp

theorem multipleEllipticGammaForwardFactor_fin_two
    (sigma tau z : ℂ) (n : Fin 2 → ℕ) :
    multipleEllipticGammaForwardFactor ![sigma, tau] n z =
      ellipticGammaForwardFactor sigma tau (n 0, n 1)
        (z - (1 + tau) / 2) := by
  rw [multipleEllipticGammaForwardFactor, ellipticGammaForwardFactor,
    multipleEllipticGammaForwardArgument, ellipticGammaForwardArgument]
  rw [show multipleEllipticGammaCoordinate z =
      ellipticThetaCoordinate tau (z - (1 + tau) / 2) by
    exact multipleEllipticGammaCoordinate_eq_ellipticThetaCoordinate tau z]
  simp [Fin.prod_univ_two]

theorem multipleEllipticGammaBackwardFactor_fin_two
    (sigma tau z : ℂ) (n : Fin 2 → ℕ) :
    multipleEllipticGammaBackwardFactor ![sigma, tau] n z =
      ellipticGammaBackwardFactor sigma tau (n 0, n 1)
        (z - (1 + tau) / 2) := by
  rw [multipleEllipticGammaBackwardFactor, ellipticGammaBackwardFactor,
    multipleEllipticGammaBackwardArgument, ellipticGammaBackwardArgument]
  rw [show multipleEllipticGammaCoordinate z =
      ellipticThetaCoordinate tau (z - (1 + tau) / 2) by
    exact multipleEllipticGammaCoordinate_eq_ellipticThetaCoordinate tau z]
  simp [Fin.prod_univ_two]

theorem multipleEllipticGammaForwardProduct_fin_two
    (sigma tau z : ℂ) :
    multipleEllipticGammaForwardProduct ![sigma, tau] z =
      ellipticGammaForwardProduct sigma tau (z - (1 + tau) / 2) := by
  rw [multipleEllipticGammaForwardProduct, ellipticGammaForwardProduct,
    ← (finTwoArrowEquiv ℕ).tprod_eq
      (fun jk => ellipticGammaForwardFactor sigma tau jk
        (z - (1 + tau) / 2))]
  apply tprod_congr
  intro n
  exact multipleEllipticGammaForwardFactor_fin_two sigma tau z n

theorem multipleEllipticGammaBackwardProduct_fin_two
    (sigma tau z : ℂ) :
    multipleEllipticGammaBackwardProduct ![sigma, tau] z =
      ellipticGammaBackwardProduct sigma tau (z - (1 + tau) / 2) := by
  rw [multipleEllipticGammaBackwardProduct, ellipticGammaBackwardProduct,
    ← (finTwoArrowEquiv ℕ).tprod_eq
      (fun jk => ellipticGammaBackwardFactor sigma tau jk
        (z - (1 + tau) / 2))]
  apply tprod_congr
  intro n
  exact multipleEllipticGammaBackwardFactor_fin_two sigma tau z n

theorem multipleEllipticGammaProduct_fin_two
    (sigma tau : ℂ) :
    multipleEllipticGammaProduct ![sigma, tau] =
      fun z => ellipticGammaProduct sigma tau (z - (1 + tau) / 2) := by
  funext z
  have hEven : Even (Fintype.card (Fin 2)) := by simp
  rw [multipleEllipticGammaProduct, if_pos hEven, ellipticGammaProduct,
    multipleEllipticGammaForwardProduct_fin_two,
    multipleEllipticGammaBackwardProduct_fin_two]

theorem multipleEllipticGammaForwardAnalytic_fin_two
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    multipleEllipticGammaForwardAnalytic ![sigma, tau] (by
      intro i
      fin_cases i
      · exact hsigma
      · exact htau) =
      addTranslationAnalyticEquiv (-(1 + tau) / 2)
        (ellipticGammaForwardAnalytic sigma tau hsigma htau) := by
  apply Subtype.ext
  let htr : Tendsto (addTranslation (-(1 + tau) / 2))
      (Filter.principal Set.univ) (Filter.principal Set.univ) :=
    tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)
  change Germ.ofFun (l := Filter.principal Set.univ)
      (multipleEllipticGammaForwardProduct ![sigma, tau]) =
    (Germ.ofFun (l := Filter.principal Set.univ)
      (ellipticGammaForwardProduct sigma tau)).compTendsto
        (addTranslation (-(1 + tau) / 2)) htr
  rw [Germ.coe_compTendsto, Germ.coe_eq]
  exact eventually_principal.mpr fun z _ ↦ by
    rw [multipleEllipticGammaForwardProduct_fin_two]
    congr 1
    simp only [addTranslation]
    ring

theorem multipleEllipticGammaBackwardAnalytic_fin_two
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    multipleEllipticGammaBackwardAnalytic ![sigma, tau] (by
      intro i
      fin_cases i
      · exact hsigma
      · exact htau) =
      addTranslationAnalyticEquiv (-(1 + tau) / 2)
        (ellipticGammaBackwardAnalytic sigma tau hsigma htau) := by
  apply Subtype.ext
  let htr : Tendsto (addTranslation (-(1 + tau) / 2))
      (Filter.principal Set.univ) (Filter.principal Set.univ) :=
    tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)
  change Germ.ofFun (l := Filter.principal Set.univ)
      (multipleEllipticGammaBackwardProduct ![sigma, tau]) =
    (Germ.ofFun (l := Filter.principal Set.univ)
      (ellipticGammaBackwardProduct sigma tau)).compTendsto
        (addTranslation (-(1 + tau) / 2)) htr
  rw [Germ.coe_compTendsto, Germ.coe_eq]
  exact eventually_principal.mpr fun z _ ↦ by
    rw [multipleEllipticGammaBackwardProduct_fin_two]
    congr 1
    simp only [addTranslation]
    ring

theorem multipleEllipticGammaMero_fin_two
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    multipleEllipticGammaMero ![sigma, tau] (by
      intro i
      fin_cases i
      · exact hsigma
      · exact htau) =
      addTranslationMeroEquiv (-(1 + tau) / 2)
        (ellipticGammaMero sigma tau hsigma htau) := by
  have hEven : Even (Fintype.card (Fin 2)) := by simp
  rw [multipleEllipticGammaMero, if_pos hEven, ellipticGammaMero, map_div₀,
    addTranslationMeroEquiv_algebraMap, addTranslationMeroEquiv_algebraMap,
    multipleEllipticGammaForwardAnalytic_fin_two,
    multipleEllipticGammaBackwardAnalytic_fin_two]

theorem multipleEllipticGammaLogDerivMero_fin_two
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im) :
    multipleEllipticGammaLogDerivMero ![sigma, tau] (by
      intro i
      fin_cases i
      · exact hsigma
      · exact htau) =
      addTranslationMeroEquiv (-(1 + tau) / 2)
        (ellipticGammaLogDerivMero sigma tau hsigma htau) := by
  simp only [multipleEllipticGammaLogDerivMero, ellipticGammaLogDerivMero,
    Differential.logDeriv]
  rw [multipleEllipticGammaMero_fin_two sigma tau hsigma htau, map_div₀,
    addTranslationMeroEquiv_deriv]

/-! ## The rank-three seed -/

theorem hypertranscendentalOver_multipleEllipticGammaLogDerivMero_fin_two
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    HypertranscendentalOver meromorphicRationalCoordinateField
      (multipleEllipticGammaLogDerivMero ![sigma, tau] (by
        intro i
        fin_cases i
        · exact hsigma
        · exact htau)) := by
  have helliptic :=
    hypertranscendentalOver_ellipticGammaLogDerivMero_rationalBase
      sigma tau hsigma htau hindependent
  have hellipticC : HypertranscendentalOver ℂ
      (ellipticGammaLogDerivMero sigma tau hsigma htau) :=
    hypertranscendentalOver_meromorphicRationalCoordinateField_iff.mp helliptic
  have htranslatedC : HypertranscendentalOver ℂ
      (addTranslationMeroEquiv (-(1 + tau) / 2)
        (ellipticGammaLogDerivMero sigma tau hsigma htau)) := by
    intro hda
    exact hellipticC
      ((HTGeometry.DifferentialAlgEquiv.differentialAlgebraicOver_map_iff
        (addTranslationMeroDifferentialAlgEquiv (-(1 + tau) / 2)) _).mp hda)
  rw [multipleEllipticGammaLogDerivMero_fin_two sigma tau hsigma htau]
  exact hypertranscendentalOver_meromorphicRationalCoordinateField_iff.mpr
    htranslatedC

theorem hypertranscendentalOver_multipleEllipticGammaMero_fin_two
    (sigma tau : ℂ) (hsigma : 0 < sigma.im) (htau : 0 < tau.im)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    HypertranscendentalOver meromorphicRationalCoordinateField
      (multipleEllipticGammaMero ![sigma, tau] (by
        intro i
        fin_cases i
        · exact hsigma
        · exact htau)) := by
  rw [← hypertranscendentalOver_deriv_div_self_iff]
  simpa [multipleEllipticGammaLogDerivMero, Differential.logDeriv] using
    hypertranscendentalOver_multipleEllipticGammaLogDerivMero_fin_two
      sigma tau hsigma htau hindependent

/-! ## Hypertranscendence climbs the intrinsic face lattice -/

theorem hypertranscendentalOver_multipleEllipticGammaLogDerivFaceMero_of_insert
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (J : Finset ι) (q : ι) (hq : q ∉ J)
    (hcoface : HypertranscendentalOver meromorphicRationalCoordinateField
      (multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J))) :
    HypertranscendentalOver meromorphicRationalCoordinateField
      (multipleEllipticGammaLogDerivFaceMero τ hτ J) := by
  have hcofaceC : HypertranscendentalOver ℂ
      (multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J)) :=
    hypertranscendentalOver_meromorphicRationalCoordinateField_iff.mp hcoface
  have hfaceC : HypertranscendentalOver ℂ
      (multipleEllipticGammaLogDerivFaceMero τ hτ J) := by
    apply HTGeometry.DifferentialAlgEquiv.hypertranscendentalOver_of_sub_self
      (addTranslationMeroDifferentialAlgEquiv (τ q))
    have hdefect : HypertranscendentalOver ℂ
        (addTranslationMeroEquiv (τ q)
            (multipleEllipticGammaLogDerivFaceMero τ hτ J) -
          multipleEllipticGammaLogDerivFaceMero τ hτ J) := by
      rw [multipleEllipticGammaLogDerivFaceMero_addTranslation_sub τ hτ J q hq]
      exact hcofaceC
    simpa only [addTranslationMeroDifferentialAlgEquiv] using! hdefect
  exact hypertranscendentalOver_meromorphicRationalCoordinateField_iff.mpr hfaceC

theorem hypertranscendentalOver_multipleEllipticGammaLogDerivFaceMero_empty
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (J : Finset ι)
    (hface : HypertranscendentalOver meromorphicRationalCoordinateField
      (multipleEllipticGammaLogDerivFaceMero τ hτ J)) :
    HypertranscendentalOver meromorphicRationalCoordinateField
      (multipleEllipticGammaLogDerivFaceMero τ hτ ∅) := by
  induction J using Finset.induction_on with
  | empty => exact hface
  | @insert q J hq ih =>
      exact ih
        (hypertranscendentalOver_multipleEllipticGammaLogDerivFaceMero_of_insert
          τ hτ J q hq hface)

private def multipleEllipticGammaFaceEmptyEquiv
    {ι : Type} [Fintype ι] [DecidableEq ι] :
    MultipleEllipticGammaFaceIndex (∅ : Finset ι) ≃ ι where
  toFun i := i.1
  invFun i := ⟨i, by simp⟩
  left_inv i := by apply Subtype.ext; rfl
  right_inv _ := rfl

theorem multipleEllipticGammaLogDerivFaceMero_empty
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    multipleEllipticGammaLogDerivFaceMero τ hτ ∅ =
      multipleEllipticGammaLogDerivMero τ hτ := by
  change multipleEllipticGammaLogDerivMero
      (fun i : MultipleEllipticGammaFaceIndex (∅ : Finset ι) => τ i.1)
      (fun i => hτ i.1) = multipleEllipticGammaLogDerivMero τ hτ
  exact multipleEllipticGammaLogDerivMero_reindex
    (multipleEllipticGammaFaceEmptyEquiv (ι := ι)) τ hτ

/-! ## All-order rank-three-minor theorem -/

/-- A finite period family contains a rank-three minor when two distinct labels, together with
the unit period, form a rationally linearly independent triple. -/
def MultipleEllipticGammaHasRankThreeMinor
    {ι : Type} (τ : ι → ℂ) : Prop :=
  ∃ q r : ι, q ≠ r ∧
    LinearIndependent ℚ (ellipticGammaSourcePeriods (τ q) (τ r))

private def multipleEllipticGammaPairComplementQ
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (q r : ι) : MultipleEllipticGammaFaceIndex
      ((Finset.univ : Finset ι) \ {q, r}) := ⟨q, by simp⟩

private def multipleEllipticGammaPairComplementR
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (q r : ι) : MultipleEllipticGammaFaceIndex
      ((Finset.univ : Finset ι) \ {q, r}) := ⟨r, by simp⟩

private def multipleEllipticGammaPairComplementEquiv
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (q r : ι) (hqr : q ≠ r) :
    Fin 2 ≃ MultipleEllipticGammaFaceIndex
      ((Finset.univ : Finset ι) \ {q, r}) where
  toFun i := ![multipleEllipticGammaPairComplementQ q r,
    multipleEllipticGammaPairComplementR q r] i
  invFun i := if i.1 = q then 0 else 1
  left_inv i := by
    fin_cases i
    · simp [multipleEllipticGammaPairComplementQ]
    · have hrq : r ≠ q := Ne.symm hqr
      simp [multipleEllipticGammaPairComplementR, hrq]
  right_inv i := by
    apply Subtype.ext
    by_cases hi : i.1 = q
    · simp [hi, multipleEllipticGammaPairComplementQ]
    · have hir : i.1 = r := by
        simpa [hi] using i.2
      simp [hir, multipleEllipticGammaPairComplementR, Ne.symm hqr]

/-- **All-order rank-three-minor theorem.** If any two periods in a finite upper-half-plane
family are rationally independent together with `1`, then the logarithmic derivative of the
genuine multiple elliptic gamma is hypertranscendental over `ℂ(z)`. Arbitrary rational
dependencies among every other period are allowed. -/
theorem hypertranscendentalOver_multipleEllipticGammaLogDerivMero_of_rankThreeMinorPair
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (q r : ι) (hqr : q ≠ r)
    (hindependent : LinearIndependent ℚ
      (ellipticGammaSourcePeriods (τ q) (τ r))) :
    HypertranscendentalOver meromorphicRationalCoordinateField
      (multipleEllipticGammaLogDerivMero τ hτ) := by
  let J : Finset ι := Finset.univ \ {q, r}
  let e : Fin 2 ≃ MultipleEllipticGammaFaceIndex J :=
    multipleEllipticGammaPairComplementEquiv q r hqr
  have hpair :=
    hypertranscendentalOver_multipleEllipticGammaLogDerivMero_fin_two
      (τ q) (τ r) (hτ q) (hτ r) hindependent
  have hpairFaceParameters : HypertranscendentalOver
      meromorphicRationalCoordinateField
      (multipleEllipticGammaLogDerivMero
        (fun k => multipleEllipticGammaFaceParameters τ J (e k))
        (fun k => hτ (e k).1)) := by
    have hparams :
        (fun k : Fin 2 => multipleEllipticGammaFaceParameters τ J (e k)) =
          ![τ q, τ r] := by
      funext k
      fin_cases k
      · simp [e, multipleEllipticGammaPairComplementEquiv,
          multipleEllipticGammaPairComplementQ,
          multipleEllipticGammaFaceParameters]
      · simp [e, multipleEllipticGammaPairComplementEquiv,
          multipleEllipticGammaPairComplementR,
          multipleEllipticGammaFaceParameters]
    simpa only [hparams] using! hpair
  have hface : HypertranscendentalOver meromorphicRationalCoordinateField
      (multipleEllipticGammaLogDerivFaceMero τ hτ J) := by
    rw [multipleEllipticGammaLogDerivMero_reindex e
      (multipleEllipticGammaFaceParameters τ J) (fun i => hτ i.1)] at hpairFaceParameters
    exact hpairFaceParameters
  have hempty :=
    hypertranscendentalOver_multipleEllipticGammaLogDerivFaceMero_empty
      τ hτ J hface
  rw [multipleEllipticGammaLogDerivFaceMero_empty τ hτ] at hempty
  exact hempty

theorem hypertranscendentalOver_multipleEllipticGammaLogDerivMero_of_rankThreeMinor
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hminor : MultipleEllipticGammaHasRankThreeMinor τ) :
    HypertranscendentalOver meromorphicRationalCoordinateField
      (multipleEllipticGammaLogDerivMero τ hτ) := by
  obtain ⟨q, r, hqr, hindependent⟩ := hminor
  exact
    hypertranscendentalOver_multipleEllipticGammaLogDerivMero_of_rankThreeMinorPair
      τ hτ q r hqr hindependent

/-- Under the same rank-three-minor hypothesis, the genuine all-order multiple elliptic gamma
product itself is hypertranscendental over `ℂ(z)`. -/
theorem hypertranscendentalOver_multipleEllipticGammaMero_of_rankThreeMinor
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hminor : MultipleEllipticGammaHasRankThreeMinor τ) :
    HypertranscendentalOver meromorphicRationalCoordinateField
      (multipleEllipticGammaMero τ hτ) := by
  rw [← hypertranscendentalOver_deriv_div_self_iff]
  simpa [multipleEllipticGammaLogDerivMero, Differential.logDeriv] using
    hypertranscendentalOver_multipleEllipticGammaLogDerivMero_of_rankThreeMinor
      τ hτ hminor

end

end GaloisForLFunctions
