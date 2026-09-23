import GaloisForLFunctions.HTGeometry.BesselOrderIntensity
import GaloisForLFunctions.HTGeometry.AnalyticJetFieldBridge
import GaloisForLFunctions.HTGeometry.MeromorphicFieldRealization
import GaloisForLFunctions.HTGeometry.AnalyticMeroPolynomialEval
import GaloisForLFunctions.HTGeometry.TranslationStableDifferentialAlgebraicity
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicFiniteTransitivity

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

theorem addTranslationMeroEquiv_analyticMeroElement
    (q : ℂ) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) :
    addTranslationMeroEquiv q (analyticMeroElement f hf) =
      analyticMeroElement (fun z => f (z + q))
        (analyticOnNhd_comp_addTranslation hf q) := by
  rw [analyticMeroElement, addTranslationMeroEquiv_algebraMap, analyticMeroElement]
  congr 1

def modifiedBesselKOrderMero (s : ℝ) (hs : 0 < s) :
    meroField (Set.univ : Set ℂ) :=
  analyticMeroElement (modifiedBesselKOrder s)
    (analyticOnNhd_modifiedBesselKOrder hs)

def modifiedBesselKOrderShiftMero (s : ℝ) (hs : 0 < s) (q : ℂ) :
    meroField (Set.univ : Set ℂ) :=
  analyticMeroElement (fun z => modifiedBesselKOrder s (z + q))
    (analyticOnNhd_comp_addTranslation (analyticOnNhd_modifiedBesselKOrder hs) q)

@[simp] theorem modifiedBesselKOrderShiftMero_zero (s : ℝ) (hs : 0 < s) :
    modifiedBesselKOrderShiftMero s hs 0 = modifiedBesselKOrderMero s hs := by
  rw [modifiedBesselKOrderShiftMero, modifiedBesselKOrderMero]
  congr 1
  funext z
  rw [add_zero]

def besselOrderLinearCoeffShiftMero (s : ℝ) (q : ℂ) :
    meroField (Set.univ : Set ℂ) :=
  analyticMeroElement (fun z : ℂ => 2 * (z + q) / s)
    (by
      have hnum : AnalyticOnNhd ℂ (fun z : ℂ => (2 : ℂ) * (z + q)) Set.univ :=
        analyticOnNhd_const.mul (analyticOnNhd_id.add analyticOnNhd_const)
      have hinv : AnalyticOnNhd ℂ (fun _ : ℂ => (s : ℂ)⁻¹) Set.univ :=
        analyticOnNhd_const
      simpa [div_eq_mul_inv] using hnum.mul hinv)

def besselOrderLinearCoeffPolynomial (s : ℝ) (q : ℂ) : Polynomial ℂ :=
  Polynomial.C (2 / (s : ℂ)) * (Polynomial.X + Polynomial.C q)

def besselOrderLinearCoeffRat (s : ℝ) (q : ℂ) : RatFunc ℂ :=
  algebraMap (Polynomial ℂ) (RatFunc ℂ) (besselOrderLinearCoeffPolynomial s q)

theorem besselOrderLinearCoeffShiftMero_eq_algebraMap
    (s : ℝ) (q : ℂ) :
    besselOrderLinearCoeffShiftMero s q =
      algebraMap (RatFunc ℂ) (meroField Set.univ)
        (besselOrderLinearCoeffRat s q) := by
  rw [besselOrderLinearCoeffShiftMero, besselOrderLinearCoeffRat]
  change analyticMeroElement (fun z : ℂ => 2 * (z + q) / s) _ =
    ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
      Set.infinite_univ
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) (besselOrderLinearCoeffPolynomial s q))
  rw [ratfuncToMero_algebraMap_polynomial]
  change algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (analyticFunctionElement (fun z : ℂ => 2 * (z + q) / s) _) =
    algebraMap (analyticSubring Set.univ) (meroField Set.univ)
      (polyToAnalytic Set.univ (besselOrderLinearCoeffPolynomial s q))
  congr 1
  apply Subtype.ext
  change Germ.ofFun (l := 𝓟 Set.univ) (fun z : ℂ => 2 * (z + q) / s) =
    Germ.ofFun (l := 𝓟 Set.univ)
      (fun z : ℂ => (besselOrderLinearCoeffPolynomial s q).eval z)
  rw [Germ.coe_eq]
  exact eventually_principal.mpr fun z _ => by
    simp [besselOrderLinearCoeffPolynomial]
    ring_nf

theorem besselOrderLinearCoeffRat_lead_ne_zero (s : ℝ) :
    1 + besselOrderLinearCoeffRat s 0 * besselOrderLinearCoeffRat s (-1) ≠ 0 := by
  let P : Polynomial ℂ :=
    1 + besselOrderLinearCoeffPolynomial s 0 *
      besselOrderLinearCoeffPolynomial s (-1)
  have hP : P ≠ 0 := by
    intro hzero
    have hval := congrArg (Polynomial.eval 0) hzero
    simp [P, besselOrderLinearCoeffPolynomial] at hval
  have hmap : algebraMap (Polynomial ℂ) (RatFunc ℂ) P ≠ 0 :=
    fun hzero => hP (RatFunc.algebraMap_injective ℂ (by simpa using hzero))
  simpa [P, besselOrderLinearCoeffRat, map_add, map_mul] using hmap

def besselOrderLinearCoeffMero (s : ℝ) : meroField (Set.univ : Set ℂ) :=
  besselOrderLinearCoeffShiftMero s 0

theorem addTranslationMeroEquiv_modifiedBesselKOrderMero
    (s : ℝ) (hs : 0 < s) (q : ℂ) :
    addTranslationMeroEquiv q (modifiedBesselKOrderMero s hs) =
      modifiedBesselKOrderShiftMero s hs q := by
  exact addTranslationMeroEquiv_analyticMeroElement q
    (analyticOnNhd_modifiedBesselKOrder hs)

theorem modifiedBesselKOrderShiftMero_recurrence
    (s : ℝ) (hs : 0 < s) (q : ℂ) :
    modifiedBesselKOrderShiftMero s hs (q + 1) =
      modifiedBesselKOrderShiftMero s hs (q - 1) +
        besselOrderLinearCoeffShiftMero s q *
          modifiedBesselKOrderShiftMero s hs q := by
  let hplus := analyticOnNhd_comp_addTranslation
    (analyticOnNhd_modifiedBesselKOrder hs) (q + 1)
  let hminus := analyticOnNhd_comp_addTranslation
    (analyticOnNhd_modifiedBesselKOrder hs) (q - 1)
  let hcoeff : AnalyticOnNhd ℂ (fun z : ℂ => 2 * (z + q) / s)
      (Set.univ : Set ℂ) :=
    by
      have hnum : AnalyticOnNhd ℂ (fun z : ℂ => (2 : ℂ) * (z + q)) Set.univ :=
        analyticOnNhd_const.mul (analyticOnNhd_id.add analyticOnNhd_const)
      have hinv : AnalyticOnNhd ℂ (fun _ : ℂ => (s : ℂ)⁻¹) Set.univ :=
        analyticOnNhd_const
      simpa [div_eq_mul_inv] using hnum.mul hinv
  let hy := analyticOnNhd_comp_addTranslation
    (analyticOnNhd_modifiedBesselKOrder hs) q
  let hprod := hcoeff.mul hy
  let hrhs := hminus.add hprod
  have hfun : (fun z => modifiedBesselKOrder s (z + (q + 1))) =
      fun z => modifiedBesselKOrder s (z + (q - 1)) +
        (2 * (z + q) / s) * modifiedBesselKOrder s (z + q) := by
    funext z
    rw [show z + (q + 1) = (z + q) + 1 by ring,
      show z + (q - 1) = (z + q) - 1 by ring]
    exact modifiedBesselKOrder_add_one hs (z + q)
  change analyticMeroElement (fun z => modifiedBesselKOrder s (z + (q + 1))) hplus = _
  calc
    _ = analyticMeroElement
        (fun z => modifiedBesselKOrder s (z + (q - 1)) +
          (2 * (z + q) / s) * modifiedBesselKOrder s (z + q))
        hrhs :=
      analyticMeroElement_congr hplus _ hfun
    _ = _ := by
      rw [analyticMeroElement_add hminus hprod, analyticMeroElement_mul hcoeff hy]
      rfl

theorem modifiedBesselKOrderMero_shift_recurrence
    (s : ℝ) (hs : 0 < s) :
    modifiedBesselKOrderShiftMero s hs 1 =
      modifiedBesselKOrderShiftMero s hs (-1) +
        besselOrderLinearCoeffMero s * modifiedBesselKOrderMero s hs := by
  simpa [besselOrderLinearCoeffMero, modifiedBesselKOrderShiftMero,
    modifiedBesselKOrderMero] using
    modifiedBesselKOrderShiftMero_recurrence s hs 0

def modifiedBesselOrderIntensityMero (s : ℝ) (hs : 0 < s) :
    meroField (Set.univ : Set ℂ) :=
  analyticMeroElement (modifiedBesselOrderIntensity s)
    (analyticOnNhd_modifiedBesselOrderIntensity hs)

def modifiedBesselOrderIntensityShiftMero (s : ℝ) (hs : 0 < s) (q : ℂ) :
    meroField (Set.univ : Set ℂ) :=
  analyticMeroElement (fun z => modifiedBesselOrderIntensity s (z + q))
    (analyticOnNhd_comp_addTranslation
      (analyticOnNhd_modifiedBesselOrderIntensity hs) q)

theorem modifiedBesselOrderIntensityMero_eq
    (s : ℝ) (hs : 0 < s) :
    modifiedBesselOrderIntensityMero s hs =
      modifiedBesselKOrderMero s hs * modifiedBesselKOrderShiftMero s hs (-2) := by
  rw [modifiedBesselOrderIntensityMero, modifiedBesselKOrderMero,
    modifiedBesselKOrderShiftMero, ← analyticMeroElement_mul]
  congr 1

theorem addTranslationMeroEquiv_modifiedBesselOrderIntensityMero
    (s : ℝ) (hs : 0 < s) (q : ℂ) :
    addTranslationMeroEquiv q (modifiedBesselOrderIntensityMero s hs) =
      modifiedBesselOrderIntensityShiftMero s hs q := by
  exact addTranslationMeroEquiv_analyticMeroElement q
    (analyticOnNhd_modifiedBesselOrderIntensity hs)

theorem modifiedBesselOrderIntensityShiftMero_eq
    (s : ℝ) (hs : 0 < s) (q : ℂ) :
    modifiedBesselOrderIntensityShiftMero s hs q =
      modifiedBesselKOrderShiftMero s hs q *
        modifiedBesselKOrderShiftMero s hs (q - 2) := by
  change analyticMeroElement (fun z => modifiedBesselOrderIntensity s (z + q)) _ =
    analyticMeroElement (fun z => modifiedBesselKOrder s (z + q)) _ *
      analyticMeroElement (fun z => modifiedBesselKOrder s (z + (q - 2))) _
  rw [← analyticMeroElement_mul]
  congr 1
  funext z
  simp only [modifiedBesselOrderIntensity]
  congr 1
  ring_nf

theorem quartic_elimination_of_two_quadratic_observations
    {R : Type*} [CommRing R] (a b y p I0 I1 : R)
    (h0 : I0 = y ^ (2 : ℕ) - b * y * p)
    (h1 : I1 = p ^ (2 : ℕ) + a * y * p) :
    (1 + a * b) * y ^ (4 : ℕ) - ((2 + a * b) * I0 + b ^ (2 : ℕ) * I1) * y ^ (2 : ℕ) + I0 ^ (2 : ℕ) = 0 := by
  rw [h0, h1]
  ring_nf

theorem modifiedBesselOrderIntensityMero_observation_zero
    (s : ℝ) (hs : 0 < s) :
    modifiedBesselOrderIntensityMero s hs =
      modifiedBesselKOrderMero s hs ^ (2 : ℕ) -
        besselOrderLinearCoeffShiftMero s (-1) *
          modifiedBesselKOrderMero s hs *
            modifiedBesselKOrderShiftMero s hs (-1) := by
  have hrec := modifiedBesselKOrderShiftMero_recurrence s hs (-1)
  rw [show (-1 : ℂ) + 1 = 0 by ring, show (-1 : ℂ) - 1 = -2 by ring] at hrec
  have hrec' : modifiedBesselKOrderMero s hs =
      modifiedBesselKOrderShiftMero s hs (-2) +
        besselOrderLinearCoeffShiftMero s (-1) *
          modifiedBesselKOrderShiftMero s hs (-1) := by
    simpa using hrec
  have hback : modifiedBesselKOrderShiftMero s hs (-2) =
      modifiedBesselKOrderMero s hs -
        besselOrderLinearCoeffShiftMero s (-1) *
          modifiedBesselKOrderShiftMero s hs (-1) :=
    (eq_sub_iff_add_eq).2 hrec'.symm
  rw [modifiedBesselOrderIntensityMero_eq, hback]
  ring_nf

theorem modifiedBesselOrderIntensityMero_observation_one
    (s : ℝ) (hs : 0 < s) :
    modifiedBesselOrderIntensityShiftMero s hs 1 =
      modifiedBesselKOrderShiftMero s hs (-1) ^ (2 : ℕ) +
        besselOrderLinearCoeffShiftMero s 0 *
          modifiedBesselKOrderMero s hs *
            modifiedBesselKOrderShiftMero s hs (-1) := by
  have hrec := modifiedBesselKOrderShiftMero_recurrence s hs 0
  have hrec' : modifiedBesselKOrderShiftMero s hs 1 =
      modifiedBesselKOrderShiftMero s hs (-1) +
        besselOrderLinearCoeffShiftMero s 0 *
          modifiedBesselKOrderMero s hs := by
    simpa using hrec
  rw [modifiedBesselOrderIntensityShiftMero_eq]
  convert congrArg (fun w => w * modifiedBesselKOrderShiftMero s hs (-1)) hrec' using 1 <;>
    ring_nf

theorem modifiedBesselOrderIntensityMero_quartic_relation
    (s : ℝ) (hs : 0 < s) :
    let a := besselOrderLinearCoeffShiftMero s 0
    let b := besselOrderLinearCoeffShiftMero s (-1)
    let y := modifiedBesselKOrderMero s hs
    let I0 := modifiedBesselOrderIntensityMero s hs
    let I1 := modifiedBesselOrderIntensityShiftMero s hs 1
    (1 + a * b) * y ^ (4 : ℕ) - ((2 + a * b) * I0 + b ^ (2 : ℕ) * I1) * y ^ (2 : ℕ) + I0 ^ (2 : ℕ) = 0 := by
  dsimp only
  exact quartic_elimination_of_two_quadratic_observations _ _ _ _ _ _
    (modifiedBesselOrderIntensityMero_observation_zero s hs)
    (modifiedBesselOrderIntensityMero_observation_one s hs)

theorem differentiallyAlgebraic_modifiedBesselKOrder_of_intensity
    (s : ℝ) (hs : 0 < s)
    (hI : DifferentiallyAlgebraic (modifiedBesselOrderIntensity s)) :
    DifferentiallyAlgebraic (modifiedBesselKOrder s) := by
  let E := meroField (Set.univ : Set ℂ)
  let F := RatFunc ℂ
  let y : E := modifiedBesselKOrderMero s hs
  let I0 : E := modifiedBesselOrderIntensityMero s hs
  let I1 : E := modifiedBesselOrderIntensityShiftMero s hs 1
  have hI0 : DifferentialAlgebraicOver F I0 := by
    dsimp only [F, I0, modifiedBesselOrderIntensityMero]
    exact differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic
      (analyticOnNhd_modifiedBesselOrderIntensity hs) hI
  have hI1 : DifferentialAlgebraicOver F I1 := by
    have hshift := differentialAlgebraicOver_addTranslationMeroEquiv 1 hI0
    rw [show I1 = addTranslationMeroEquiv 1 I0 by
      dsimp only [I0, I1]
      exact (addTranslationMeroEquiv_modifiedBesselOrderIntensityMero s hs 1).symm]
    exact hshift
  let obs : Fin 2 → E := ![I0, I1]
  let S := differentialAdjoin F (Set.range obs)
  have hI0mem : I0 ∈ S := by
    apply subset_differentialAdjoin F
    exact ⟨0, by simp [obs]⟩
  have hI1mem : I1 ∈ S := by
    apply subset_differentialAdjoin F
    exact ⟨1, by simp [obs]⟩
  let I0S : S := ⟨I0, hI0mem⟩
  let I1S : S := ⟨I1, hI1mem⟩
  let aR : F := besselOrderLinearCoeffRat s 0
  let bR : F := besselOrderLinearCoeffRat s (-1)
  let aS : S := algebraMap F S aR
  let bS : S := algebraMap F S bR
  have hleadR : 1 + aR * bR ≠ 0 := by
    exact besselOrderLinearCoeffRat_lead_ne_zero s
  have hleadS : 1 + aS * bS ≠ 0 := by
    rw [show 1 + aS * bS = algebraMap F S (1 + aR * bR) by
      simp [aS, bS]]
    exact (map_ne_zero (algebraMap F S)).2 hleadR
  let Q : MvPolynomial (Fin 1) S :=
    MvPolynomial.monomial (Finsupp.single 0 4) (1 + aS * bS) -
      MvPolynomial.monomial (Finsupp.single 0 2)
        ((2 + aS * bS) * I0S + bS ^ (2 : ℕ) * I1S) +
      MvPolynomial.monomial 0 (I0S ^ (2 : ℕ))
  have hQ : Q ≠ 0 := by
    intro hzero
    have hc := congrArg
      (MvPolynomial.coeff (Finsupp.single (0 : Fin 1) 4)) hzero
    have hindex : Finsupp.single (0 : Fin 1) 4 ≠ 0 := by
      intro h
      have h0 := congrArg (fun d : Fin 1 →₀ ℕ => d 0) h
      simp at h0
    have h24 : Finsupp.single (0 : Fin 1) 2 ≠ Finsupp.single 0 4 := by
      intro h
      have h0 := congrArg (fun d : Fin 1 →₀ ℕ => d 0) h
      simp at h0
    apply hleadS
    simp only [Q, MvPolynomial.coeff_add, MvPolynomial.coeff_sub,
      MvPolynomial.coeff_monomial] at hc
    simpa [hindex, hindex.symm, h24] using hc
  have hrel : MvPolynomial.aeval
      (fun j : Fin 1 => differentialJet (j : ℕ) y) Q = 0 := by
    have hquartic := modifiedBesselOrderIntensityMero_quartic_relation s hs
    rw [besselOrderLinearCoeffShiftMero_eq_algebraMap,
      besselOrderLinearCoeffShiftMero_eq_algebraMap] at hquartic
    have hj : (fun j : Fin 1 => differentialJet (j : ℕ) y) = fun _ => y := by
      funext j
      have hj0 : j = 0 := Fin.eq_zero j
      subst j
      simp
    rw [hj]
    rw [MvPolynomial.aeval_def]
    simp [Q, MvPolynomial.eval₂_monomial, aS, bS, I0S, I1S,
      y, I0, I1] at hquartic ⊢
    dsimp only [F, E, aR, bR] at hquartic ⊢
    ring_nf at hquartic ⊢
    exact hquartic
  have hyS : DifferentialAlgebraicOver S y :=
    differentialAlgebraicOver_of_finiteJetRelation hQ hrel
  have hobs : ∀ i, DifferentialAlgebraicOver F (obs i) := by
    intro i
    fin_cases i
    · exact hI0
    · exact hI1
  have hyF : DifferentialAlgebraicOver F y :=
    differentialAlgebraicOver_trans_fin_succ_narrow obs hobs y hyS
  apply differentiallyAlgebraic_of_differentialAlgebraicOver_analyticMeroElement
    (analyticOnNhd_modifiedBesselKOrder hs)
  simpa [F, y, modifiedBesselKOrderMero] using hyF

theorem hypertranscendental_modifiedBesselOrderIntensity_of_order
    (s : ℝ) (hs : 0 < s)
    (hK : Hypertranscendental (modifiedBesselKOrder s)) :
    Hypertranscendental (modifiedBesselOrderIntensity s) := by
  intro hI
  exact hK (differentiallyAlgebraic_modifiedBesselKOrder_of_intensity s hs hI)

end

end GaloisForLFunctions.HTGeometry
