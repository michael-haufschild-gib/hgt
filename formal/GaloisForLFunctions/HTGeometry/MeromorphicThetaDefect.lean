import GaloisForLFunctions.HTGeometry.JacobiThetaDefectPrincipalPart
import GaloisForLFunctions.HTGeometry.MeromorphicTheta

/-!
# The translated theta logarithmic-derivative defect in the meromorphic field

This file identifies the analytic two-pole defect with an explicit element of the genuine
meromorphic fraction field.  Translation composition is proved at both the analytic-germ and
fraction-field levels.  The defect is fixed by the full theta period lattice, has a concrete
entire numerator and denominator, and is not constant for a nonlattice shift.
-/

open Filter Topology Set Function

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance thetaDefectUnivAnalyticDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

/-- Additive translations compose by addition on analytic germs. -/
theorem addTranslationAnalyticEquiv_add (p q : ℂ)
    (a : analyticSubring (Set.univ : Set ℂ)) :
    addTranslationAnalyticEquiv p (addTranslationAnalyticEquiv q a) =
      addTranslationAnalyticEquiv (p + q) a := by
  apply Subtype.ext
  change
    ((a : Germ (𝓟 Set.univ) ℂ).compTendsto (addTranslation q)
      (tendsto_principal_principal.mpr (Set.mapsTo_univ _ _))).compTendsto
        (addTranslation p)
        (tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)) =
      (a : Germ (𝓟 Set.univ) ℂ).compTendsto (addTranslation (p + q))
        (tendsto_principal_principal.mpr (Set.mapsTo_univ _ _))
  let ga : Germ (𝓟 Set.univ) ℂ := a.1
  change
    (ga.compTendsto (addTranslation q)
      (tendsto_principal_principal.mpr (Set.mapsTo_univ _ _))).compTendsto
        (addTranslation p)
        (tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)) =
      ga.compTendsto (addTranslation (p + q))
        (tendsto_principal_principal.mpr (Set.mapsTo_univ _ _))
  induction ga using Germ.inductionOn with
  | _ f =>
    rw [Germ.coe_compTendsto, Germ.coe_compTendsto, Germ.coe_compTendsto]
    apply Germ.coe_eq.mpr
    exact eventually_principal.mpr fun z _ => by
      simp [addTranslation, add_comm, add_left_comm]

/-- Additive translations compose by addition on the meromorphic fraction field. -/
theorem addTranslationMeroEquiv_add (p q : ℂ)
    (x : meroField (Set.univ : Set ℂ)) :
    addTranslationMeroEquiv p (addTranslationMeroEquiv q x) =
      addTranslationMeroEquiv (p + q) x := by
  obtain ⟨a, b, _hb, rfl⟩ :=
    IsFractionRing.div_surjective (analyticSubring Set.univ) x
  rw [map_div₀, map_div₀, map_div₀]
  simp only [addTranslationMeroEquiv_algebraMap, addTranslationAnalyticEquiv_add]

/-- **Commuting mixed-defect law.**  For any global meromorphic element, the two iterated
translation defects are independent of the order of the translation parameters.  This is the
general cocycle identity behind every mixed source face. -/
theorem addTranslationMeroEquiv_mixed_defect_comm (p q : ℂ)
    (x : meroField (Set.univ : Set ℂ)) :
    addTranslationMeroEquiv p (addTranslationMeroEquiv q x - x) -
        (addTranslationMeroEquiv q x - x) =
      addTranslationMeroEquiv q (addTranslationMeroEquiv p x - x) -
        (addTranslationMeroEquiv p x - x) := by
  rw [map_sub, map_sub, addTranslationMeroEquiv_add,
    addTranslationMeroEquiv_add]
  rw [show p + q = q + p by ring]

/-- Translation defects form an additive one-cocycle in the translation parameter. -/
theorem addTranslationMeroEquiv_defect_add (p q : ℂ)
    (x : meroField (Set.univ : Set ℂ)) :
    addTranslationMeroEquiv (p + q) x - x =
      (addTranslationMeroEquiv p x - x) +
        addTranslationMeroEquiv p (addTranslationMeroEquiv q x - x) := by
  rw [map_sub, addTranslationMeroEquiv_add]
  ring

/-- **Translation-defect reflection.**  Reversing the translation parameter reflects the defect
by translating the original defect back and changing its sign. -/
theorem addTranslationMeroEquiv_defect_neg (p : ℂ)
    (x : meroField (Set.univ : Set ℂ)) :
    addTranslationMeroEquiv (-p) x - x =
      -addTranslationMeroEquiv (-p) (addTranslationMeroEquiv p x - x) := by
  have hzero : addTranslationMeroEquiv 0 x = x := by
    apply (addTranslationMeroEquiv 0).injective
    simpa using addTranslationMeroEquiv_add 0 0 x
  rw [map_sub, addTranslationMeroEquiv_add]
  rw [show -p + p = 0 by ring, hzero]
  ring

/-- Every additive translation fixes the embedded complex constants. -/
theorem addTranslationMeroEquiv_const (q c : ℂ) :
    addTranslationMeroEquiv q
        (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (constToAnalytic Set.univ c)) =
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ c) := by
  rw [addTranslationMeroEquiv_algebraMap]
  congr 1

/-- The meromorphic-field realization of `phi(z+h)-phi(z)`, where `phi=theta'/theta`. -/
def thetaLogDerivDefectMero (h τ : ℂ) (hτ : 0 < τ.im) :
    meroField (Set.univ : Set ℂ) :=
  addTranslationMeroEquiv h (thetaLogDerivMero τ hτ) -
    thetaLogDerivMero τ hτ

/-- The entire cross numerator of the translated theta logarithmic-derivative defect. -/
def thetaLogDerivDefectNumeratorAnalytic (h τ : ℂ) (hτ : 0 < τ.im) :
    analyticSubring (Set.univ : Set ℂ) :=
  addTranslationAnalyticEquiv h (thetaPrimeAnalytic τ hτ) * thetaAnalytic τ hτ -
    addTranslationAnalyticEquiv h (thetaAnalytic τ hτ) * thetaPrimeAnalytic τ hτ

/-- The entire product denominator of the translated theta logarithmic-derivative defect. -/
def thetaLogDerivDefectDenominatorAnalytic (h τ : ℂ) (hτ : 0 < τ.im) :
    analyticSubring (Set.univ : Set ℂ) :=
  addTranslationAnalyticEquiv h (thetaAnalytic τ hτ) * thetaAnalytic τ hτ

theorem thetaLogDerivDefectDenominatorAnalytic_ne_zero
    (h τ : ℂ) (hτ : 0 < τ.im) :
    thetaLogDerivDefectDenominatorAnalytic h τ hτ ≠ 0 := by
  rw [thetaLogDerivDefectDenominatorAnalytic, mul_ne_zero_iff]
  exact ⟨fun hz => thetaAnalytic_ne_zero τ hτ
      ((addTranslationAnalyticEquiv h).injective (by simpa using hz)),
    thetaAnalytic_ne_zero τ hτ⟩

/-- The field defect is represented by its explicit entire cross numerator and product
denominator.  This is the concrete field-to-principal-part bridge. -/
theorem thetaLogDerivDefectMero_eq_div (h τ : ℂ) (hτ : 0 < τ.im) :
    thetaLogDerivDefectMero h τ hτ =
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (thetaLogDerivDefectNumeratorAnalytic h τ hτ) /
        algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (thetaLogDerivDefectDenominatorAnalytic h τ hτ) := by
  rw [thetaLogDerivDefectMero, thetaLogDerivMero, map_div₀,
    addTranslationMeroEquiv_algebraMap, addTranslationMeroEquiv_algebraMap,
    thetaLogDerivDefectNumeratorAnalytic,
    thetaLogDerivDefectDenominatorAnalytic, map_sub, map_mul, map_mul]
  simp only [map_mul]
  have hθ : algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (thetaAnalytic τ hτ) ≠ 0 :=
    fun hz => thetaAnalytic_ne_zero τ hτ
      ((IsFractionRing.injective (analyticSubring Set.univ)
        (meroField Set.univ)) (by simpa using hz))
  have hθh : algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (addTranslationAnalyticEquiv h (thetaAnalytic τ hτ)) ≠ 0 :=
    fun hz => thetaAnalytic_ne_zero τ hτ
      ((addTranslationAnalyticEquiv h).injective
        ((IsFractionRing.injective (analyticSubring Set.univ)
          (meroField Set.univ)) (by simpa using hz)))
  field_simp [hθ, hθh]

/-- The translated theta defect is `1`-periodic in the meromorphic field. -/
theorem addTranslationMeroEquiv_thetaLogDerivDefect_one
    (h τ : ℂ) (hτ : 0 < τ.im) :
    addTranslationMeroEquiv 1 (thetaLogDerivDefectMero h τ hτ) =
      thetaLogDerivDefectMero h τ hτ := by
  rw [thetaLogDerivDefectMero, map_sub, addTranslationMeroEquiv_add,
    addTranslationMeroEquiv_thetaLogDeriv_one]
  rw [show 1 + h = h + 1 by ring, ← addTranslationMeroEquiv_add,
    addTranslationMeroEquiv_thetaLogDeriv_one]

/-- The translated theta defect is `τ`-periodic: the logarithmic derivative's quasiperiodic
constant cancels in the defect. -/
theorem addTranslationMeroEquiv_thetaLogDerivDefect_tau
    (h τ : ℂ) (hτ : 0 < τ.im) :
    addTranslationMeroEquiv τ (thetaLogDerivDefectMero h τ hτ) =
      thetaLogDerivDefectMero h τ hτ := by
  rw [thetaLogDerivDefectMero, map_sub, addTranslationMeroEquiv_add,
    addTranslationMeroEquiv_thetaLogDeriv_tau]
  rw [show τ + h = h + τ by ring, ← addTranslationMeroEquiv_add,
    addTranslationMeroEquiv_thetaLogDeriv_tau]
  simp only [map_ofNat, map_mul, map_sub, addTranslationMeroEquiv_const]
  ring

/-- A nonlattice theta defect is not an embedded constant.  Evaluating the cleared fraction
identity at the simple theta zero leaves a nonzero product, a contradiction. -/
theorem thetaLogDerivDefectMero_ne_const_of_nonlattice
    {h τ : ℂ} (hτ : 0 < τ.im) (hh : ThetaNonlatticeShift τ h) (c : ℂ) :
    thetaLogDerivDefectMero h τ hτ ≠
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ c) := by
  intro heq
  have hθ : thetaAnalytic τ hτ ≠ 0 := thetaAnalytic_ne_zero τ hτ
  have hθh : addTranslationAnalyticEquiv h (thetaAnalytic τ hτ) ≠ 0 :=
    fun hz => hθ ((addTranslationAnalyticEquiv h).injective (by simpa using hz))
  have hθF : algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (thetaAnalytic τ hτ) ≠ 0 :=
    fun hz => hθ ((IsFractionRing.injective (analyticSubring Set.univ)
      (meroField Set.univ)) (by simpa using hz))
  have hθhF : algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (addTranslationAnalyticEquiv h (thetaAnalytic τ hτ)) ≠ 0 :=
    fun hz => hθh ((IsFractionRing.injective (analyticSubring Set.univ)
      (meroField Set.univ)) (by simpa using hz))
  rw [thetaLogDerivDefectMero, thetaLogDerivMero, map_div₀,
    addTranslationMeroEquiv_algebraMap, addTranslationMeroEquiv_algebraMap] at heq
  field_simp [hθhF, hθF] at heq
  have heqA :
      addTranslationAnalyticEquiv h (thetaPrimeAnalytic τ hτ) * thetaAnalytic τ hτ -
          addTranslationAnalyticEquiv h (thetaAnalytic τ hτ) * thetaPrimeAnalytic τ hτ =
        addTranslationAnalyticEquiv h (thetaAnalytic τ hτ) * thetaAnalytic τ hτ *
          constToAnalytic Set.univ c := by
    apply IsFractionRing.injective (analyticSubring Set.univ) (meroField Set.univ)
    simpa only [map_sub, map_mul] using heq
  have heqG := congrArg Subtype.val heqA
  let htr : Tendsto (addTranslation h) (𝓟 Set.univ) (𝓟 Set.univ) :=
    tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)
  change
    (Germ.ofFun (l := 𝓟 Set.univ) (jacobiTheta₂' · τ)).compTendsto
          (addTranslation h) htr * Germ.ofFun (l := 𝓟 Set.univ) (jacobiTheta₂ · τ) -
        (Germ.ofFun (l := 𝓟 Set.univ) (jacobiTheta₂ · τ)).compTendsto
          (addTranslation h) htr * Germ.ofFun (l := 𝓟 Set.univ) (jacobiTheta₂' · τ) =
      (Germ.ofFun (l := 𝓟 Set.univ) (jacobiTheta₂ · τ)).compTendsto
          (addTranslation h) htr * Germ.ofFun (l := 𝓟 Set.univ) (jacobiTheta₂ · τ) *
        Germ.ofFun (l := 𝓟 Set.univ) (fun _ : ℂ => c) at heqG
  rw [Germ.coe_compTendsto, Germ.coe_compTendsto,
    ← Germ.coe_mul, ← Germ.coe_mul, ← Germ.coe_sub,
    ← Germ.coe_mul, ← Germ.coe_mul, Germ.coe_eq] at heqG
  let p := thetaHalfPeriod τ
  have hp := eventually_principal.mp heqG p (Set.mem_univ p)
  have hp0 : jacobiTheta₂ p τ = 0 := by
    simpa [p] using jacobiTheta₂_thetaHalfPeriod_add_lattice_eq_zero τ 0 0
  have hpprime : jacobiTheta₂' p τ ≠ 0 := by
    simpa [p] using jacobiTheta₂'_thetaHalfPeriod_add_lattice_ne_zero hτ 0 0
  have hph : jacobiTheta₂ (p + h) τ ≠ 0 := by
    simpa [p] using theta_add_nonzero_at_lattice_of_nonlattice hτ hh 0 0
  change
    jacobiTheta₂' (p + h) τ * jacobiTheta₂ p τ -
        jacobiTheta₂ (p + h) τ * jacobiTheta₂' p τ =
      jacobiTheta₂ (p + h) τ * jacobiTheta₂ p τ * c at hp
  rw [hp0, mul_zero, zero_sub, mul_zero, zero_mul, neg_eq_zero] at hp
  exact (mul_ne_zero hph hpprime) hp

theorem thetaLogDerivDefectMero_ne_zero_of_nonlattice
    {h τ : ℂ} (hτ : 0 < τ.im) (hh : ThetaNonlatticeShift τ h) :
    thetaLogDerivDefectMero h τ hτ ≠ 0 := by
  intro hz
  exact thetaLogDerivDefectMero_ne_const_of_nonlattice hτ hh 0 (by simpa using hz)

end

end GaloisForLFunctions
