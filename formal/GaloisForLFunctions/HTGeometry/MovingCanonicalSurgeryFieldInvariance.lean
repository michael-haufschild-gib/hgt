import GaloisForLFunctions.HTGeometry.MovingCanonicalSurgery
import GaloisForLFunctions.HTGeometry.MovingCanonicalUpperEndDifferentialIndependence
import GaloisForLFunctions.HTGeometry.UpperEndRatfuncDifferentialAlgebra
import GaloisForLFunctions.HTGeometry.DifferentialFamilyMatroidBaseGauge
import GaloisForLFunctions.HTGeometry.RatFuncTranslationFixedField

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Filter Set Topology Polynomial
open ClassicalAnalyticNevanlinnaCarrierFamily
open scoped Differential BigOperators

noncomputable section

/-- A complex simple-pole term in the rational coordinate field. -/
def complexPoleTermRatFunc (a c : ℂ) : RatFunc ℂ :=
  algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) /
    algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (Polynomial.C a - Polynomial.X)

/-- The same complex simple-pole term as an upper-end analytic germ. -/
def complexPoleTermUpperEndAnalytic
    (a c : ℂ) : upperEndAnalyticSubring := by
  refine
    ⟨(((fun z : ℂ => c / (a - z)) : ℂ → ℂ) :
        Germ upperEndFilter ℂ),
      (fun z : ℂ => c / (a - z)), a.im, ?_, rfl⟩
  refine AnalyticOnNhd.div analyticOnNhd_const
    (analyticOnNhd_const.sub analyticOnNhd_id) ?_
  intro z hz haz
  have him := congrArg Complex.im haz
  change a.im < z.im at hz
  simp only [Complex.sub_im] at him
  have him0 : a.im - z.im = 0 := by simpa using him
  linarith

@[simp]
theorem complexPoleTermUpperEndAnalytic_coe
    (a c : ℂ) :
    ((complexPoleTermUpperEndAnalytic a c :
      upperEndAnalyticSubring) :
      Germ upperEndFilter ℂ) =
      (((fun z : ℂ => c / (a - z)) : ℂ → ℂ) :
        Germ upperEndFilter ℂ) := rfl

theorem polynomial_C_sub_X_ne_zero_complex (a : ℂ) :
    Polynomial.C a - Polynomial.X ≠ 0 := by
  intro h
  have hcoeff :=
    congrArg (fun p : Polynomial ℂ => p.coeff 1) h
  simp at hcoeff

/-- The rational embedding of a complex pole term is its literal
upper-end analytic germ. -/
theorem upperEndRatfuncToMero_complexPoleTerm
    (a c : ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    upperEndRatfuncToMero (complexPoleTermRatFunc a c) =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (complexPoleTermUpperEndAnalytic a c) := by
  letI := isDomain_upperEndAnalyticSubring
  have hdenPoly :
      Polynomial.C a - Polynomial.X ≠ 0 :=
    polynomial_C_sub_X_ne_zero_complex a
  have hdenMero :
      upperEndPolyToMero
          (Polynomial.C a - Polynomial.X) ≠ 0 := by
    simpa only [map_zero] using
      upperEndPolyToMero_injective.ne hdenPoly
  have hmul :
      complexPoleTermUpperEndAnalytic a c *
          upperEndPolyToAnalytic
            (Polynomial.C a - Polynomial.X) =
        upperEndPolyToAnalytic (Polynomial.C c) := by
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    filter_upwards
      [upperEndFilter_basis.mem_iff.mpr
        ⟨a.im, trivial, Set.Subset.rfl⟩] with z hz
    have hne : a - z ≠ 0 := by
      intro haz
      have him := congrArg Complex.im haz
      change a.im < z.im at hz
      simp only [Complex.sub_im] at him
      have him0 : a.im - z.im = 0 := by simpa using him
      linarith
    simpa [upperEndPolyToAnalytic] using
      (div_mul_cancel₀ c hne)
  rw [complexPoleTermRatFunc, map_div₀,
    upperEndRatfuncToMero_algebraMap_polynomial,
    upperEndRatfuncToMero_algebraMap_polynomial]
  apply (div_eq_iff hdenMero).2
  have hmulMero := congrArg
    (algebraMap upperEndAnalyticSubring upperEndMeroField)
    hmul
  simpa [upperEndPolyToMero, map_mul] using
    hmulMero.symm

theorem upperEndRatfuncToMero_algebraMap_complex
    (c : ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    upperEndRatfuncToMero
        (algebraMap ℂ (RatFunc ℂ) c) =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (upperEndPolyToAnalytic (Polynomial.C c)) := by
  letI := isDomain_upperEndAnalyticSubring
  rw [show algebraMap ℂ (RatFunc ℂ) c =
      algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (Polynomial.C c) by
    rw [← Polynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply]]
  exact upperEndRatfuncToMero_algebraMap_polynomial _

/-- Rational correction which deletes selected real zeros, inserts
conjugate upper/lower zero pairs, and applies the exact real
normalizing constant from formula (9). -/
def movingCanonicalSurgeryGaugeRatFunc
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    RatFunc ℂ :=
  -(∑ n ∈ movingCanonicalSurgerySelectedIndices aIdx bIdx,
      (complexPoleTermRatFunc
        (movingCanonicalZero θ n : ℂ) 1 -
        algebraMap ℂ (RatFunc ℂ)
          ((movingCanonicalZero θ n : ℂ)⁻¹))) +
    ∑ i,
      (complexPoleTermRatFunc (t i) 1 +
        complexPoleTermRatFunc (star (t i)) 1) -
    algebraMap ℂ (RatFunc ℂ)
      (movingCanonicalSurgeryConstant θ aIdx bIdx : ℂ)

/-- Literal analytic-germ realization of the exact surgery rational
correction. -/
def movingCanonicalSurgeryGaugeUpperEndAnalytic
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    upperEndAnalyticSubring :=
  -(∑ n ∈ movingCanonicalSurgerySelectedIndices aIdx bIdx,
      (complexPoleTermUpperEndAnalytic
        (movingCanonicalZero θ n : ℂ) 1 -
        upperEndPolyToAnalytic
          (Polynomial.C
            ((movingCanonicalZero θ n : ℂ)⁻¹)))) +
    ∑ i,
      (complexPoleTermUpperEndAnalytic (t i) 1 +
        complexPoleTermUpperEndAnalytic (star (t i)) 1) -
    upperEndPolyToAnalytic
      (Polynomial.C
        (movingCanonicalSurgeryConstant θ aIdx bIdx : ℂ))

theorem upperEndRatfuncToMero_movingCanonicalSurgeryGauge
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    upperEndRatfuncToMero
        (movingCanonicalSurgeryGaugeRatFunc
          θ aIdx bIdx t) =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (movingCanonicalSurgeryGaugeUpperEndAnalytic
          θ aIdx bIdx t) := by
  letI := isDomain_upperEndAnalyticSubring
  simp only [movingCanonicalSurgeryGaugeRatFunc,
    movingCanonicalSurgeryGaugeUpperEndAnalytic,
    map_sub, map_add, map_neg, map_sum,
    upperEndRatfuncToMero_complexPoleTerm,
    upperEndRatfuncToMero_algebraMap_complex]

theorem movingCanonicalSurgeryGaugeUpperEndAnalytic_coe
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    ((movingCanonicalSurgeryGaugeUpperEndAnalytic
        θ aIdx bIdx t : upperEndAnalyticSubring) :
      Germ upperEndFilter ℂ) =
      ((fun z =>
        -(∑ n ∈
            movingCanonicalSurgerySelectedIndices aIdx bIdx,
            movingCanonicalRegularizedAtom θ n z) +
          multiPairCarrier t z -
          (movingCanonicalSurgeryConstant
            θ aIdx bIdx : ℂ)) :
        Germ upperEndFilter ℂ) := by
  let S :=
    movingCanonicalSurgerySelectedIndices aIdx bIdx
  have hpole (a : ℂ) :
      Subring.subtype upperEndAnalyticSubring
          (complexPoleTermUpperEndAnalytic a 1) =
        ((fun z : ℂ => (a - z)⁻¹) :
          Germ upperEndFilter ℂ) := by
    change
      (((fun z : ℂ => 1 / (a - z)) : ℂ → ℂ) :
          Germ upperEndFilter ℂ) =
        ((fun z : ℂ => (a - z)⁻¹) :
          Germ upperEndFilter ℂ)
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun z => by
      simp [one_div]
  have hconst (c : ℂ) :
      Subring.subtype upperEndAnalyticSubring
          (upperEndPolyToAnalytic (Polynomial.C c)) =
        ((fun _ : ℂ => c) :
          Germ upperEndFilter ℂ) := by
    change
      (((fun z : ℂ => (Polynomial.C c).eval z) :
          ℂ → ℂ) : Germ upperEndFilter ℂ) =
        ((fun _ : ℂ => c) :
          Germ upperEndFilter ℂ)
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun z => by simp
  have hreg (n : ℕ) :
      Subring.subtype upperEndAnalyticSubring
          (complexPoleTermUpperEndAnalytic
              (movingCanonicalZero θ n : ℂ) 1 -
            upperEndPolyToAnalytic
              (Polynomial.C
                ((movingCanonicalZero θ n : ℂ)⁻¹))) =
        (movingCanonicalRegularizedAtom θ n :
          Germ upperEndFilter ℂ) := by
    rw [map_sub, hpole, hconst,
      ← Filter.Germ.coe_sub]
    rfl
  have hselected :
      Subring.subtype upperEndAnalyticSubring
          (∑ n ∈ S,
            (complexPoleTermUpperEndAnalytic
                (movingCanonicalZero θ n : ℂ) 1 -
              upperEndPolyToAnalytic
                (Polynomial.C
                  ((movingCanonicalZero θ n : ℂ)⁻¹)))) =
        ((fun z =>
          ∑ n ∈ S,
            movingCanonicalRegularizedAtom θ n z) :
          Germ upperEndFilter ℂ) := by
    rw [map_sum]
    simp_rw [hreg]
    change
      (∑ n ∈ S,
        (Filter.Germ.coeRingHom upperEndFilter)
          (movingCanonicalRegularizedAtom θ n)) = _
    rw [← map_sum (Filter.Germ.coeRingHom
      upperEndFilter)]
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun z => by simp
  have hpair (i : Fin k) :
      Subring.subtype upperEndAnalyticSubring
          (complexPoleTermUpperEndAnalytic (t i) 1 +
            complexPoleTermUpperEndAnalytic
              (star (t i)) 1) =
        ((fun z =>
          (t i - z)⁻¹ +
            (star (t i) - z)⁻¹) :
          Germ upperEndFilter ℂ) := by
    rw [map_add, hpole, hpole,
      ← Filter.Germ.coe_add]
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun z => rfl
  have hpairs :
      Subring.subtype upperEndAnalyticSubring
          (∑ i,
            (complexPoleTermUpperEndAnalytic (t i) 1 +
              complexPoleTermUpperEndAnalytic
                (star (t i)) 1)) =
        ((fun z =>
          ∑ i,
            ((t i - z)⁻¹ +
              (star (t i) - z)⁻¹)) :
          Germ upperEndFilter ℂ) := by
    rw [map_sum]
    simp_rw [hpair]
    change
      (∑ i,
        (Filter.Germ.coeRingHom upperEndFilter)
          (fun z =>
            (t i - z)⁻¹ +
              (star (t i) - z)⁻¹)) = _
    rw [← map_sum (Filter.Germ.coeRingHom
      upperEndFilter)]
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun z => by simp
  change
    Subring.subtype upperEndAnalyticSubring
        (movingCanonicalSurgeryGaugeUpperEndAnalytic
          θ aIdx bIdx t) = _
  rw [movingCanonicalSurgeryGaugeUpperEndAnalytic]
  rw [map_sub, map_add, map_neg, hselected,
    hpairs, hconst, ← Filter.Germ.coe_neg,
    ← Filter.Germ.coe_add, ← Filter.Germ.coe_sub]
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z => by
    simp [S, multiPairCarrier]

/-- Exact surgery carrier as one upper-end analytic germ. -/
def movingCanonicalSurgeryCarrierUpperEndAnalytic
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    upperEndAnalyticSubring :=
  analyticUpperEndElement
      (movingCanonicalLogDerivative θ) 0
      (by
        simpa using
          analyticOnNhd_movingCanonicalLogDerivative_translate_upperTail
            θ 0) +
    movingCanonicalSurgeryGaugeUpperEndAnalytic
      θ aIdx bIdx t

theorem movingCanonicalSurgeryCarrierUpperEndAnalytic_coe
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    ((movingCanonicalSurgeryCarrierUpperEndAnalytic
        θ aIdx bIdx t : upperEndAnalyticSubring) :
      Germ upperEndFilter ℂ) =
      (movingCanonicalSurgeryCarrier
        θ aIdx bIdx t : Germ upperEndFilter ℂ) := by
  change
    Subring.subtype upperEndAnalyticSubring
        (movingCanonicalSurgeryCarrierUpperEndAnalytic
          θ aIdx bIdx t) = _
  rw [movingCanonicalSurgeryCarrierUpperEndAnalytic,
    map_add]
  rw [show
      Subring.subtype upperEndAnalyticSubring
          (movingCanonicalSurgeryGaugeUpperEndAnalytic
            θ aIdx bIdx t) =
        ((fun z =>
          -(∑ n ∈
              movingCanonicalSurgerySelectedIndices
                aIdx bIdx,
              movingCanonicalRegularizedAtom θ n z) +
            multiPairCarrier t z -
            (movingCanonicalSurgeryConstant
              θ aIdx bIdx : ℂ)) :
          Germ upperEndFilter ℂ) from
    movingCanonicalSurgeryGaugeUpperEndAnalytic_coe
      θ aIdx bIdx t]
  apply Filter.Germ.coe_eq.mpr
  filter_upwards
    [upperEndFilter_basis.mem_iff.mpr
      ⟨0, trivial, Set.Subset.rfl⟩] with z hz
  rw [movingCanonicalSurgeryCarrier,
    movingCanonicalComplementCarrier_eq_sub_sum θ
      (movingCanonicalSurgerySelectedIndices aIdx bIdx)
      hz]
  ring

/-- Exact upper-end meromorphic realization of the literal surgery
carrier. -/
def movingCanonicalSurgeryUpperEndMero
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  exact algebraMap upperEndAnalyticSubring upperEndMeroField
    (movingCanonicalSurgeryCarrierUpperEndAnalytic
      θ aIdx bIdx t)

theorem movingCanonicalTranslatedUpperEndMero_zero
    (θ : BoundedRealSequence) :
    letI := isDomain_upperEndAnalyticSubring
    movingCanonicalTranslatedUpperEndMero θ 0 =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (analyticUpperEndElement
          (movingCanonicalLogDerivative θ) 0
          (by
            simpa using
              analyticOnNhd_movingCanonicalLogDerivative_translate_upperTail
                θ 0)) := by
  letI := isDomain_upperEndAnalyticSubring
  rw [movingCanonicalTranslatedUpperEndMero,
    analyticUpperEndMero]
  congr 1
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z => by simp

theorem movingCanonicalSurgeryUpperEndMero_eq_add_rational
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    movingCanonicalSurgeryUpperEndMero θ aIdx bIdx t =
      movingCanonicalTranslatedUpperEndMero θ 0 +
        upperEndRatfuncToMero
          (movingCanonicalSurgeryGaugeRatFunc
            θ aIdx bIdx t) := by
  letI := isDomain_upperEndAnalyticSubring
  rw [movingCanonicalSurgeryUpperEndMero,
    movingCanonicalSurgeryCarrierUpperEndAnalytic,
    map_add,
    upperEndRatfuncToMero_movingCanonicalSurgeryGauge]
  rw [movingCanonicalTranslatedUpperEndMero_zero]

theorem upperEndTranslationMeroEquiv_polyToMero
    (h : ℂ) (p : Polynomial ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    upperEndTranslationMeroEquiv h
        (upperEndPolyToMero p) =
      upperEndPolyToMero
        (polyTranslationEquiv h p) := by
  letI := isDomain_upperEndAnalyticSubring
  change upperEndTranslationMeroEquiv h
      (algebraMap upperEndAnalyticSubring
        upperEndMeroField
        (upperEndPolyToAnalytic p)) =
    algebraMap upperEndAnalyticSubring
      upperEndMeroField
      (upperEndPolyToAnalytic
        (polyTranslationEquiv h p))
  rw [
    upperEndTranslationMeroEquiv_algebraMap]
  congr 1
  apply Subtype.ext
  rw [upperEndTranslationAnalyticEquiv_coe]
  change
    upperEndTranslateGerm h
        ((fun z : ℂ => p.eval z) :
          Germ upperEndFilter ℂ) =
      ((fun z : ℂ =>
        (polyTranslationEquiv h p).eval z) :
        Germ upperEndFilter ℂ)
  rw [upperEndTranslateGerm_coe]
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z => by
    change p.eval (z + h) =
      (polyTranslationHom h p).eval z
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        simp only [map_add, eval_add, hp, hq]
    | monomial n a =>
        simp [polyTranslationHom,
          Polynomial.aeval_def,
          Polynomial.eval_monomial]

/-- Translation of upper-end rational germs is substitution
`X ↦ X + h` in `ℂ(X)`. -/
theorem upperEndTranslationMeroEquiv_ratfuncToMero
    (h : ℂ) (r : RatFunc ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    upperEndTranslationMeroEquiv h
        (upperEndRatfuncToMero r) =
      upperEndRatfuncToMero
        (ratFuncTranslationEquiv h r) := by
  letI := isDomain_upperEndAnalyticSubring
  let left : RatFunc ℂ →+* upperEndMeroField :=
    (upperEndTranslationMeroEquiv h).toRingHom.comp
      upperEndRatfuncToMero
  let right : RatFunc ℂ →+* upperEndMeroField :=
    upperEndRatfuncToMero.comp
      (ratFuncTranslationEquiv h).toRingHom
  have hhom : left = right := by
    apply IsFractionRing.ringHom_ext
      (A := Polynomial ℂ)
    intro p
    dsimp only [left, right]
    rw [RingHom.comp_apply, RingHom.comp_apply,
      upperEndRatfuncToMero_algebraMap_polynomial]
    change
      upperEndTranslationMeroEquiv h
          (upperEndPolyToMero p) =
        upperEndRatfuncToMero
          (ratFuncTranslationEquiv h
            (algebraMap (Polynomial ℂ)
              (RatFunc ℂ) p))
    rw [
      ratFuncTranslationEquiv_algebraMap,
      upperEndRatfuncToMero_algebraMap_polynomial,
      upperEndTranslationMeroEquiv_polyToMero]
  exact RingHom.congr_fun hhom r

theorem movingCanonicalTranslatedUpperEndMero_eq_translation
    (θ : BoundedRealSequence) (h : ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    movingCanonicalTranslatedUpperEndMero θ h =
      upperEndTranslationMeroEquiv h
        (movingCanonicalTranslatedUpperEndMero θ 0) := by
  letI := isDomain_upperEndAnalyticSubring
  rw [movingCanonicalTranslatedUpperEndMero_zero,
    upperEndTranslationMeroEquiv_algebraMap]
  rw [movingCanonicalTranslatedUpperEndMero,
    analyticUpperEndMero]
  congr 1

/-- Actual full complex translation orbit of the exact surgery
carrier. -/
def movingCanonicalSurgeryTranslateFamily
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (h : ℂ) : upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  exact upperEndTranslationMeroEquiv h
    (movingCanonicalSurgeryUpperEndMero
      θ aIdx bIdx t)

/-- Every translated surgery carrier is its corresponding canonical
translate plus a translated rational coordinate correction. -/
theorem movingCanonicalSurgeryTranslateFamily_eq_add_rational
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ)
    (h : ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    movingCanonicalSurgeryTranslateFamily
        θ aIdx bIdx t h =
      movingCanonicalTranslatedUpperEndMero θ h +
        upperEndRatfuncToMero
          (ratFuncTranslationEquiv h
            (movingCanonicalSurgeryGaugeRatFunc
              θ aIdx bIdx t)) := by
  letI := isDomain_upperEndAnalyticSubring
  rw [movingCanonicalSurgeryTranslateFamily,
    movingCanonicalSurgeryUpperEndMero_eq_add_rational,
    map_add,
    upperEndTranslationMeroEquiv_ratfuncToMero]
  rw [← movingCanonicalTranslatedUpperEndMero_eq_translation
    θ h]

/-- Canonical-product surgery preserves differential independence of
the complete complex translation orbit in both directions. -/
theorem
    movingCanonicalSurgeryTranslateFamily_differentialIndependent_iff
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
        (movingCanonicalSurgeryTranslateFamily
          θ aIdx bIdx t) ↔
      DifferentialIndependent (RatFunc ℂ)
        (movingCanonicalTranslatedUpperEndMero θ) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  rw [show
      movingCanonicalSurgeryTranslateFamily
          θ aIdx bIdx t =
        fun h =>
          movingCanonicalTranslatedUpperEndMero θ h +
            upperEndRatfuncToMero
              (ratFuncTranslationEquiv h
                (movingCanonicalSurgeryGaugeRatFunc
                  θ aIdx bIdx t)) by
    funext h
    exact
      movingCanonicalSurgeryTranslateFamily_eq_add_rational
        θ aIdx bIdx t h]
  exact differentialIndependent_addUpperEndRatfunc_iff
    (movingCanonicalTranslatedUpperEndMero θ)
    (fun h =>
      ratFuncTranslationEquiv h
        (movingCanonicalSurgeryGaugeRatFunc
          θ aIdx bIdx t))

/-- Canonical-product surgery leaves the embedded differential field
generated by the full translation orbit unchanged. -/
theorem movingCanonicalSurgeryTranslateFamily_differentialAdjoin_eq
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncToMero.toAlgebra
    letI := ratFuncCoordinateDifferential
    letI := upperEndMeroFieldDifferential
    letI : DifferentialAlgebra
        (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncDifferentialAlgebra
    differentialAdjoin (RatFunc ℂ)
        (Set.range
          (movingCanonicalSurgeryTranslateFamily
            θ aIdx bIdx t)) =
      differentialAdjoin (RatFunc ℂ)
        (Set.range
          (movingCanonicalTranslatedUpperEndMero θ)) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncToMero.toAlgebra
  letI : Differential (RatFunc ℂ) :=
    ratFuncCoordinateDifferential
  letI := upperEndMeroFieldDifferential
  letI : DifferentialAlgebra
      (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncDifferentialAlgebra
  rw [show
      movingCanonicalSurgeryTranslateFamily
          θ aIdx bIdx t =
        fun h =>
          movingCanonicalTranslatedUpperEndMero θ h +
            algebraMap (RatFunc ℂ) upperEndMeroField
              (ratFuncTranslationEquiv h
                (movingCanonicalSurgeryGaugeRatFunc
                  θ aIdx bIdx t)) by
    funext h
    exact
      movingCanonicalSurgeryTranslateFamily_eq_add_rational
        θ aIdx bIdx t h]
  simpa using differentialAdjoin_range_affineBase_eq
    (movingCanonicalTranslatedUpperEndMero θ)
    (fun _ : ℂ => 1)
    (fun h =>
      ratFuncTranslationEquiv h
        (movingCanonicalSurgeryGaugeRatFunc
          θ aIdx bIdx t))
    (fun _ => one_ne_zero)

/-- Canonical-product surgery leaves the entire represented
differential matroid of the full translation orbit unchanged. -/
theorem
    movingCanonicalSurgeryTranslateFamily_differentialFamilyMatroid_eq
    {k : ℕ} (θ : BoundedRealSequence)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncToMero.toAlgebra
    letI := ratFuncCoordinateDifferential
    letI := upperEndMeroFieldDifferential
    letI : DifferentialAlgebra
        (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncDifferentialAlgebra
    letI : CharZero upperEndMeroField :=
      charZero_of_injective_ringHom
        upperEndRatfuncToMero.injective
    differentialFamilyMatroid (F := RatFunc ℂ)
        (movingCanonicalSurgeryTranslateFamily
          θ aIdx bIdx t) =
      differentialFamilyMatroid (F := RatFunc ℂ)
        (movingCanonicalTranslatedUpperEndMero θ) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncToMero.toAlgebra
  letI : Differential (RatFunc ℂ) :=
    ratFuncCoordinateDifferential
  letI := upperEndMeroFieldDifferential
  letI : DifferentialAlgebra
      (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncDifferentialAlgebra
  letI : CharZero upperEndMeroField :=
    charZero_of_injective_ringHom
      upperEndRatfuncToMero.injective
  rw [show
      movingCanonicalSurgeryTranslateFamily
          θ aIdx bIdx t =
        fun h =>
          movingCanonicalTranslatedUpperEndMero θ h +
            algebraMap (RatFunc ℂ) upperEndMeroField
              (ratFuncTranslationEquiv h
                (movingCanonicalSurgeryGaugeRatFunc
                  θ aIdx bIdx t)) by
    funext h
    exact
      movingCanonicalSurgeryTranslateFamily_eq_add_rational
        θ aIdx bIdx t h]
  exact differentialFamilyMatroid_addBase_eq
    (movingCanonicalTranslatedUpperEndMero θ)
    (fun h =>
      ratFuncTranslationEquiv h
        (movingCanonicalSurgeryGaugeRatFunc
          θ aIdx bIdx t))

/-- Every canonical phase with functional translation freeness retains
genuine field-level translation differential independence after exact
finite surgery. -/
theorem
    movingCanonicalSurgeryTranslateFamily_differentialIndependent
    {k : ℕ} (θ : BoundedRealSequence)
    (hfree : ∀ (p : FiniteDifferentialPattern ℕ)
      (shift :
        InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff :
        CarrierPatternMonomial p ×
          Fin (p.coefficientDegree + 1) → ℂ),
      movingCanonicalExpandedPatternRelationHolds
        (row := CarrierPatternRow p)
        p.coefficientDegree p.orders
        (carrierPatternExponent p) θ shift coeff →
      ∀ col, coeff col = 0)
    (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (movingCanonicalSurgeryTranslateFamily
        θ aIdx bIdx t) := by
  exact
    (movingCanonicalSurgeryTranslateFamily_differentialIndependent_iff
      θ aIdx bIdx t).2
      (movingCanonicalTranslation_upperEnd_differentialIndependent
        θ hfree)

/-- Dense residual canonical phases retain full complex-translation
differential independence after any fixed exact finite surgery. -/
theorem
    movingCanonicalSurgery_fullTranslationUpperEndDifferentialIndependence_denseResidual
    {k : ℕ} (aIdx bIdx : Fin k → ℕ) (t : Fin k → ℂ) :
    let universalPhase : Set BoundedRealSequence := {θ |
      ∀ (p : FiniteDifferentialPattern ℕ)
        (shift :
          InjectiveShiftConfiguration (CarrierPatternShift p))
        (coeff :
          CarrierPatternMonomial p ×
            Fin (p.coefficientDegree + 1) → ℂ),
        movingCanonicalExpandedPatternRelationHolds
          (row := CarrierPatternRow p)
          p.coefficientDegree p.orders
          (carrierPatternExponent p) θ shift coeff →
        ∀ col, coeff col = 0}
    Dense universalPhase ∧
      universalPhase ∈ residual BoundedRealSequence ∧
      ∀ θ ∈ universalPhase,
        letI := isDomain_upperEndAnalyticSubring
        letI : Algebra (RatFunc ℂ) upperEndMeroField :=
          upperEndRatfuncToMero.toAlgebra
        letI := upperEndMeroFieldDifferential
        DifferentialIndependent (RatFunc ℂ)
          (movingCanonicalSurgeryTranslateFamily
            θ aIdx bIdx t) := by
  dsimp only
  have hphase :=
    movingCanonical_fullTranslationFreeness_denseResidual
  dsimp only at hphase
  refine ⟨hphase.1, hphase.2.1, ?_⟩
  intro θ hθ
  exact
    movingCanonicalSurgeryTranslateFamily_differentialIndependent
      θ hθ aIdx bIdx t

/-- No invariant of the unpointed generated differential field can
recover the surgery count: every finite surgery has exactly the same
field as the unsurgered carrier. -/
theorem no_movingCanonicalSurgeryCount_selector_of_differentialAdjoin
    (θ : BoundedRealSequence) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncToMero.toAlgebra
    letI := ratFuncCoordinateDifferential
    letI := upperEndMeroFieldDifferential
    letI : DifferentialAlgebra
        (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncDifferentialAlgebra
    ¬ ∃ S :
        IntermediateField (RatFunc ℂ)
          upperEndMeroField → ℕ,
      ∀ (k : ℕ) (aIdx bIdx : Fin k → ℕ)
        (t : Fin k → ℂ),
        S (differentialAdjoin (RatFunc ℂ)
          (Set.range
            (movingCanonicalSurgeryTranslateFamily
              θ aIdx bIdx t))) = k := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncToMero.toAlgebra
  letI : Differential (RatFunc ℂ) :=
    ratFuncCoordinateDifferential
  letI := upperEndMeroFieldDifferential
  letI : DifferentialAlgebra
      (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncDifferentialAlgebra
  rintro ⟨S, hS⟩
  let a0 : Fin 0 → ℕ := fun i => Fin.elim0 i
  let b0 : Fin 0 → ℕ := fun i => Fin.elim0 i
  let t0 : Fin 0 → ℂ := fun i => Fin.elim0 i
  let a1 : Fin 1 → ℕ := fun _ => 0
  let b1 : Fin 1 → ℕ := fun _ => 1
  let t1 : Fin 1 → ℂ := fun _ => Complex.I
  have h0 := hS 0 a0 b0 t0
  have h1 := hS 1 a1 b1 t1
  rw [movingCanonicalSurgeryTranslateFamily_differentialAdjoin_eq
      θ a0 b0 t0] at h0
  rw [movingCanonicalSurgeryTranslateFamily_differentialAdjoin_eq
      θ a1 b1 t1] at h1
  omega

end

end GaloisForLFunctions.HTGeometry
