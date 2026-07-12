import GaloisForLFunctions.HTGeometry.UpperEndPrimeLogJets
import GaloisForLFunctions.HTGeometry.RationalCoefficientDifferentialFreeness

/-!
# Differential independence in the upper-end meromorphic field

This file closes the source-carrier interface.  It proves that the abstract field jets of actual
translated prime-log Herglotz elements evaluate exactly as the functional jet packets used by the
countable Baire theorem.  Field vanishing is cleared canonically, descends faithfully to an
eventual analytic germ, and propagates across the whole common translated upper domain by the
identity theorem.

Every finite jet rectangle is therefore algebraically independent over `ℂ(z)`; finitary assembly
then proves genuine differential independence of the complete shift family.  The exact
`Q(i)+∑ Zω_v` palette used by facet sewing receives an unconditional existence theorem.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set Function Polynomial
open BoundedContinuousFunction
open scoped Differential

noncomputable section

def upperEndAnalyticJetAssignment
    {Γ : Type*} {m : ℕ} (shiftValue : Γ → ℂ) (shiftCode : Fin m → Γ)
    (orders : Fin m → ℕ) (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) :
    (Σ i, Fin (orders i)) → upperEndAnalyticSubring :=
  fun s => upperEndTranslationAnalyticEquiv (shiftValue (shiftCode s.1))
    (primeLogHerglotzUpperEndAnalyticJet u C hu s.2.1)

def primeLogPolynomialRelationFunction
    {Γ : Type*} {m : ℕ} (shiftValue : Γ → ℂ) (shiftCode : Fin m → Γ)
    (orders : Fin m → ℕ) (u : Nat.Primes → ℝ)
    (P : MvPolynomial (Σ i, Fin (orders i)) ℂ[X]) (z : ℂ) : ℂ :=
  MvPolynomial.eval
    (primeLogDifferentialJetPacket u
      (fun i => z + shiftValue (shiftCode i)) orders)
    (specializePolynomialCoefficients z P)

def commonTranslatedUpperDomain
    {Γ : Type*} {m : ℕ} (shiftValue : Γ → ℂ) (shiftCode : Fin m → Γ) : Set ℂ :=
  {z | ∀ i : Fin m, 0 < (z + shiftValue (shiftCode i)).im}

theorem commonTranslatedUpperDomain_eq_iInter_upperTail
    {Γ : Type*} {m : ℕ} (shiftValue : Γ → ℂ) (shiftCode : Fin m → Γ) :
    commonTranslatedUpperDomain shiftValue shiftCode =
      ⋂ i : Fin m, upperTail (-(shiftValue (shiftCode i)).im) := by
  ext z
  simp only [commonTranslatedUpperDomain, mem_setOf_eq, mem_iInter, upperTail]
  constructor
  · intro hz i
    have hi := hz i
    simp only [Complex.add_im] at hi ⊢
    linarith
  · intro hz i
    have hi := hz i
    simp only [Complex.add_im] at hi ⊢
    linarith

theorem commonTranslatedUpperDomain_isPreconnected
    {Γ : Type*} {m : ℕ} (shiftValue : Γ → ℂ) (shiftCode : Fin m → Γ) :
    IsPreconnected (commonTranslatedUpperDomain shiftValue shiftCode) := by
  rw [commonTranslatedUpperDomain_eq_iInter_upperTail]
  exact (convex_iInter fun i =>
    convex_halfSpace_im_gt (-(shiftValue (shiftCode i)).im)).isPreconnected

theorem commonTranslatedUpperDomain_nonempty
    {Γ : Type*} {m : ℕ} (shiftValue : Γ → ℂ) (shiftCode : Fin m → Γ) :
    (commonTranslatedUpperDomain shiftValue shiftCode).Nonempty := by
  obtain ⟨H, hH⟩ := finite_complex_family_has_imaginary_lower_bound
    (fun i => shiftValue (shiftCode i))
  refine ⟨(((H + 1 : ℝ) : ℂ) * Complex.I), ?_⟩
  intro i
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
  linarith [hH i]

theorem analyticOnNhd_polyEval_univ (p : ℂ[X]) :
    AnalyticOnNhd ℂ (fun z => p.eval z) (Set.univ : Set ℂ) := by
  have h : AnalyticOnNhd ℂ (fun z => aeval z p) (Set.univ : Set ℂ) :=
    analyticOnNhd_id.aeval_polynomial p
  simpa [aeval_def] using h

theorem analyticOnNhd_primeLogDifferentialJetCoordinate
    {Γ : Type*} {m : ℕ} (shiftValue : Γ → ℂ) (shiftCode : Fin m → Γ)
    (orders : Fin m → ℕ) (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (s : Σ i, Fin (orders i)) :
    AnalyticOnNhd ℂ
      (fun z => primeLogDifferentialJetPacket u
        (fun i => z + shiftValue (shiftCode i)) orders s)
      (commonTranslatedUpperDomain shiftValue shiftCode) := by
  have hf := analyticOnNhd_iteratedDeriv
    (analyticOnNhd_primeLogHerglotz_upperHalfPlane u C hu) s.2.1
  exact hf.comp (analyticOnNhd_id.add analyticOnNhd_const) (by
    intro z hz
    exact hz s.1)

theorem analyticOnNhd_primeLogPolynomialRelationFunction
    {Γ : Type*} {m : ℕ} (shiftValue : Γ → ℂ) (shiftCode : Fin m → Γ)
    (orders : Fin m → ℕ) (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (P : MvPolynomial (Σ i, Fin (orders i)) ℂ[X]) :
    AnalyticOnNhd ℂ
      (primeLogPolynomialRelationFunction shiftValue shiftCode orders u P)
      (commonTranslatedUpperDomain shiftValue shiftCode) := by
  induction P using MvPolynomial.induction_on with
  | C p =>
      have heq : primeLogPolynomialRelationFunction shiftValue shiftCode orders u
          (MvPolynomial.C p) = fun z => p.eval z := by
        funext z
        simp [primeLogPolynomialRelationFunction, specializePolynomialCoefficients]
      rw [heq]
      exact (analyticOnNhd_polyEval_univ p).mono
        (subset_univ (commonTranslatedUpperDomain shiftValue shiftCode))
  | add P Q hP hQ =>
      have heq : primeLogPolynomialRelationFunction shiftValue shiftCode orders u (P + Q) =
          primeLogPolynomialRelationFunction shiftValue shiftCode orders u P +
            primeLogPolynomialRelationFunction shiftValue shiftCode orders u Q := by
        funext z
        simp [primeLogPolynomialRelationFunction, specializePolynomialCoefficients]
      rw [heq]
      exact hP.add hQ
  | mul_X P s hP =>
      have heq : primeLogPolynomialRelationFunction shiftValue shiftCode orders u
          (P * MvPolynomial.X s) =
          fun z => primeLogPolynomialRelationFunction shiftValue shiftCode orders u P z *
            primeLogDifferentialJetPacket u
              (fun i => z + shiftValue (shiftCode i)) orders s := by
        funext z
        simp [primeLogPolynomialRelationFunction, specializePolynomialCoefficients]
      rw [heq]
      exact hP.mul (analyticOnNhd_primeLogDifferentialJetCoordinate
        shiftValue shiftCode orders u C hu s)

theorem upperEndAnalyticJetAssignment_coe
    {Γ : Type*} {m : ℕ} (shiftValue : Γ → ℂ) (shiftCode : Fin m → Γ)
    (orders : Fin m → ℕ) (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (s : Σ i, Fin (orders i)) :
    ((upperEndAnalyticJetAssignment shiftValue shiftCode orders u C hu s :
        upperEndAnalyticSubring) : Germ upperEndFilter ℂ) =
      ((fun z => primeLogDifferentialJetPacket u
        (fun i => z + shiftValue (shiftCode i)) orders s) :
          Germ upperEndFilter ℂ) := by
  unfold upperEndAnalyticJetAssignment
  rw [upperEndTranslationAnalyticEquiv_coe]
  change upperEndTranslateGerm (shiftValue (shiftCode s.1))
      (iteratedDeriv s.2.1 (primeLogHerglotz u) : Germ upperEndFilter ℂ) = _
  rw [upperEndTranslateGerm_coe]
  rfl

theorem upperEndAnalyticRelation_coe
    {Γ : Type*} {m : ℕ} (shiftValue : Γ → ℂ) (shiftCode : Fin m → Γ)
    (orders : Fin m → ℕ) (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (P : MvPolynomial (Σ i, Fin (orders i)) ℂ[X]) :
    ((MvPolynomial.eval₂ upperEndPolyToAnalytic
        (upperEndAnalyticJetAssignment shiftValue shiftCode orders u C hu) P :
          upperEndAnalyticSubring) : Germ upperEndFilter ℂ) =
      (primeLogPolynomialRelationFunction shiftValue shiftCode orders u P :
        Germ upperEndFilter ℂ) := by
  induction P using MvPolynomial.induction_on with
  | C p =>
      rw [MvPolynomial.eval₂_C]
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun z => by
        simp [primeLogPolynomialRelationFunction,
          specializePolynomialCoefficients]
  | add P Q hP hQ =>
      rw [MvPolynomial.eval₂_add]
      change
        ((MvPolynomial.eval₂ upperEndPolyToAnalytic
          (upperEndAnalyticJetAssignment shiftValue shiftCode orders u C hu) P :
            upperEndAnalyticSubring) : Germ upperEndFilter ℂ) +
        ((MvPolynomial.eval₂ upperEndPolyToAnalytic
          (upperEndAnalyticJetAssignment shiftValue shiftCode orders u C hu) Q :
            upperEndAnalyticSubring) : Germ upperEndFilter ℂ) = _
      rw [hP, hQ, ← Germ.coe_add]
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun z => by
        simp [primeLogPolynomialRelationFunction, specializePolynomialCoefficients]

  | mul_X P s hP =>
      rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
      change
        ((MvPolynomial.eval₂ upperEndPolyToAnalytic
          (upperEndAnalyticJetAssignment shiftValue shiftCode orders u C hu) P :
            upperEndAnalyticSubring) : Germ upperEndFilter ℂ) *
          (upperEndAnalyticJetAssignment shiftValue shiftCode orders u C hu s :
            Germ upperEndFilter ℂ) = _
      rw [hP, upperEndAnalyticJetAssignment_coe, ← Germ.coe_mul]
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun z => by
        simp [primeLogPolynomialRelationFunction, specializePolynomialCoefficients]

theorem primeLogPolynomialRelationFunction_eq_zero_of_upperEnd_eq_zero
    {Γ : Type*} {m : ℕ} (shiftValue : Γ → ℂ) (shiftCode : Fin m → Γ)
    (orders : Fin m → ℕ) (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (P : MvPolynomial (Σ i, Fin (orders i)) ℂ[X])
    (hzero : MvPolynomial.eval₂ upperEndPolyToAnalytic
      (upperEndAnalyticJetAssignment shiftValue shiftCode orders u C hu) P = 0) :
    ∀ z ∈ commonTranslatedUpperDomain shiftValue shiftCode,
      primeLogPolynomialRelationFunction shiftValue shiftCode orders u P z = 0 := by
  let F := primeLogPolynomialRelationFunction shiftValue shiftCode orders u P
  have hgerm : (F : Germ upperEndFilter ℂ) = 0 := by
    rw [← upperEndAnalyticRelation_coe shiftValue shiftCode orders u C hu P]
    exact congrArg Subtype.val hzero
  rw [← Germ.coe_zero, Germ.coe_eq] at hgerm
  change ∀ᶠ z in upperEndFilter, F z = 0 at hgerm
  rw [upperEndFilter_basis.eventually_iff] at hgerm
  obtain ⟨L, -, hL⟩ := hgerm
  obtain ⟨H, hH⟩ := finite_complex_family_has_imaginary_lower_bound
    (fun i => shiftValue (shiftCode i))
  let w : ℂ := ((max H L + 1 : ℝ) : ℂ) * Complex.I
  have hwL : w ∈ upperTail L := by
    simp only [w, upperTail, mem_setOf_eq, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    linarith [le_max_right H L]
  have hwU : w ∈ commonTranslatedUpperDomain shiftValue shiftCode := by
    intro i
    simp only [w, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    linarith [hH i, le_max_left H L]
  have hlocal : F =ᶠ[nhds w] 0 := by
    filter_upwards [(upperTail_isOpen L).mem_nhds hwL] with z hz
    exact hL hz
  have hF : AnalyticOnNhd ℂ F
      (commonTranslatedUpperDomain shiftValue shiftCode) :=
    analyticOnNhd_primeLogPolynomialRelationFunction
      shiftValue shiftCode orders u C hu P
  have hall := hF.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    (commonTranslatedUpperDomain_isPreconnected shiftValue shiftCode) hwU hlocal
  exact hall

def upperEndFieldJetAssignment
    {Γ : Type*} {m : ℕ} (shiftValue : Γ → ℂ) (shiftCode : Fin m → Γ)
    (orders : Fin m → ℕ) (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) :
    (Σ i, Fin (orders i)) → upperEndMeroField :=
  fun s =>
    letI := isDomain_upperEndAnalyticSubring
    letI := upperEndMeroFieldDifferential
    differentialJet s.2.1
      (translatedPrimeLogHerglotzUpperEndMero u C hu
        (shiftValue (shiftCode s.1)))

theorem upperEndFieldJetAssignment_eq_algebraMap
    {Γ : Type*} {m : ℕ} (shiftValue : Γ → ℂ) (shiftCode : Fin m → Γ)
    (orders : Fin m → ℕ) (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (s : Σ i, Fin (orders i)) :
    letI := isDomain_upperEndAnalyticSubring
    letI := upperEndMeroFieldDifferential
    upperEndFieldJetAssignment shiftValue shiftCode orders u C hu s =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (upperEndAnalyticJetAssignment shiftValue shiftCode orders u C hu s) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI := upperEndMeroFieldDifferential
  exact differentialJet_translatedPrimeLogHerglotzUpperEndMero_algebraMap
    u C hu (shiftValue (shiftCode s.1)) s.2.1

theorem upperEndPolyToMero_eq_comp :
    letI := isDomain_upperEndAnalyticSubring
    upperEndPolyToMero =
      upperEndRatfuncToMero.comp (algebraMap ℂ[X] (RatFunc ℂ)) := by
  letI := isDomain_upperEndAnalyticSubring
  apply DFunLike.ext _ _
  intro p
  exact (upperEndRatfuncToMero_algebraMap_polynomial p).symm

theorem upperEndClearedAnalyticRelation_eq_zero_of_fieldRelation_eq_zero
    {Γ : Type*} {m : ℕ} (shiftValue : Γ → ℂ) (shiftCode : Fin m → Γ)
    (orders : Fin m → ℕ) (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (Q : MvPolynomial (Σ i, Fin (orders i)) (RatFunc ℂ))
    (hzero :
      letI := isDomain_upperEndAnalyticSubring
      letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
      letI := upperEndMeroFieldDifferential
      MvPolynomial.eval₂ upperEndRatfuncToMero
        (upperEndFieldJetAssignment shiftValue shiftCode orders u C hu) Q = 0) :
    MvPolynomial.eval₂ upperEndPolyToAnalytic
      (upperEndAnalyticJetAssignment shiftValue shiftCode orders u C hu)
      (clearRatFuncCoefficients Q) = 0 := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  let fieldJet := upperEndFieldJetAssignment shiftValue shiftCode orders u C hu
  let analyticJet := upperEndAnalyticJetAssignment shiftValue shiftCode orders u C hu
  have hclearField : MvPolynomial.eval₂ upperEndPolyToMero fieldJet
      (clearRatFuncCoefficients Q) = 0 := by
    calc
      MvPolynomial.eval₂ upperEndPolyToMero fieldJet (clearRatFuncCoefficients Q) =
          MvPolynomial.eval₂ upperEndRatfuncToMero fieldJet
            (MvPolynomial.map (algebraMap ℂ[X] (RatFunc ℂ))
              (clearRatFuncCoefficients Q)) := by
            rw [MvPolynomial.eval₂_map]
            rw [← upperEndPolyToMero_eq_comp]
      _ = MvPolynomial.eval₂ upperEndRatfuncToMero fieldJet
          (MvPolynomial.C
            (algebraMap ℂ[X] (RatFunc ℂ) (ratFuncCommonDenominator Q)) * Q) := by
            rw [map_clearRatFuncCoefficients]
      _ = 0 := by
        rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, hzero, mul_zero]
  have hmap : algebraMap upperEndAnalyticSubring upperEndMeroField
      (MvPolynomial.eval₂ upperEndPolyToAnalytic analyticJet
        (clearRatFuncCoefficients Q)) = 0 := by
    rw [MvPolynomial.eval₂_comp_right]
    rw [MvPolynomial.eval₂_map]
    change MvPolynomial.eval₂ upperEndPolyToMero
      (fun s => algebraMap upperEndAnalyticSubring upperEndMeroField (analyticJet s))
      (clearRatFuncCoefficients Q) = 0
    rw [show (fun s => algebraMap upperEndAnalyticSubring upperEndMeroField
      (analyticJet s)) = fieldJet by
        funext s
        exact (upperEndFieldJetAssignment_eq_algebraMap
          shiftValue shiftCode orders u C hu s).symm]
    exact hclearField
  exact (IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField)
    (by simpa using hmap)

theorem rationalCoefficientDifferentialRelationHolds_of_upperEndFieldRelation
    {Γ : Type*} {m : ℕ} (shiftValue : Γ → ℂ) (shiftCode : Fin m → Γ)
    (orders : Fin m → ℕ) (u : PrimeLogBoundedGauge)
    (Q : MvPolynomial (Σ i, Fin (orders i)) (RatFunc ℂ))
    (hzero :
      letI := isDomain_upperEndAnalyticSubring
      letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
      letI := upperEndMeroFieldDifferential
      MvPolynomial.eval₂ upperEndRatfuncToMero
        (upperEndFieldJetAssignment shiftValue shiftCode orders
          (fun p => u p) ‖u‖
          (fun p => (le_abs_self (u p)).trans (norm_coe_le_norm u p))) Q = 0) :
    RationalCoefficientDifferentialRelationHolds
      shiftValue shiftCode orders u Q := by
  let hu : ∀ p, u p ≤ ‖u‖ := fun p =>
    (le_abs_self (u p)).trans (norm_coe_le_norm u p)
  have hclear := upperEndClearedAnalyticRelation_eq_zero_of_fieldRelation_eq_zero
    shiftValue shiftCode orders (fun p => u p) ‖u‖ hu Q hzero
  have hall := primeLogPolynomialRelationFunction_eq_zero_of_upperEnd_eq_zero
    shiftValue shiftCode orders (fun p => u p) ‖u‖ hu
      (clearRatFuncCoefficients Q) hclear
  intro z hz
  exact hall z hz

/-- A canonically free gauge has no nonzero rational-coefficient relation when the same relation is
evaluated inside the upper-end meromorphic differential field. -/
theorem upperEndRationalFieldRelation_eq_zero
    {Γ : Type*} {m : ℕ} (shiftValue : Γ → ℂ)
    (shiftCode : Fin m → Γ) (hshiftCode : Function.Injective shiftCode)
    (orders : Fin m → ℕ) (u : PrimeLogBoundedGauge)
    (hfree : CountableShiftPolynomialDifferentialFree shiftValue u)
    (Q : MvPolynomial (Σ i, Fin (orders i)) (RatFunc ℂ))
    (hzero :
      letI := isDomain_upperEndAnalyticSubring
      letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
      letI := upperEndMeroFieldDifferential
      MvPolynomial.eval₂ upperEndRatfuncToMero
        (upperEndFieldJetAssignment shiftValue shiftCode orders
          (fun p => u p) ‖u‖
          (fun p => (le_abs_self (u p)).trans (norm_coe_le_norm u p))) Q = 0) :
    Q = 0 := by
  exact rationalCoefficientDifferentialRelation_eq_zero
    shiftValue shiftCode hshiftCode orders u hfree Q
      (rationalCoefficientDifferentialRelationHolds_of_upperEndFieldRelation
        shiftValue shiftCode orders u Q hzero)

/-- Every finite translated jet rectangle is algebraically independent over the faithfully
embedded rational coordinate field. -/
theorem upperEndFiniteRectangle_algebraicIndependent
    {Γ : Type*} {m : ℕ} (shiftValue : Γ → ℂ)
    (shiftCode : Fin m → Γ) (hshiftCode : Function.Injective shiftCode)
    (orders : Fin m → ℕ) (u : PrimeLogBoundedGauge)
    (hfree : CountableShiftPolynomialDifferentialFree shiftValue u) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    AlgebraicIndependent (RatFunc ℂ)
      (upperEndFieldJetAssignment shiftValue shiftCode orders
        (fun p => u p) ‖u‖
        (fun p => (le_abs_self (u p)).trans (norm_coe_le_norm u p))) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  rw [algebraicIndependent_iff]
  intro Q hQ
  apply upperEndRationalFieldRelation_eq_zero
    shiftValue shiftCode hshiftCode orders u hfree Q
  simpa [MvPolynomial.aeval_def, RingHom.algebraMap_toAlgebra] using hQ

def boundedGaugeTranslatedPrimeLogUpperEnd
    {Γ : Type*} (shiftValue : Γ → ℂ) (u : PrimeLogBoundedGauge) (γ : Γ) :
    upperEndMeroField :=
  translatedPrimeLogHerglotzUpperEndMero (fun p => u p) ‖u‖
    (fun p => (le_abs_self (u p)).trans (norm_coe_le_norm u p)) (shiftValue γ)

/-- Every finite injective shift packet of a canonically free gauge is genuinely differentially
independent over `C(z)` in the upper-end field. -/
theorem upperEndFiniteShift_differentialIndependent
    {Γ : Type*} {m : ℕ} (shiftValue : Γ → ℂ)
    (shiftCode : Fin m → Γ) (hshiftCode : Function.Injective shiftCode)
    (u : PrimeLogBoundedGauge)
    (hfree : CountableShiftPolynomialDifferentialFree shiftValue u) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (fun i => boundedGaugeTranslatedPrimeLogUpperEnd shiftValue u (shiftCode i)) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  unfold DifferentialIndependent
  apply algebraicIndependent_of_finite_type
  intro t ht
  let orders : Fin m → ℕ := fun i =>
    1 + ∑ p ∈ ht.toFinset, if p.1 = i then p.2 else 0
  have horder : ∀ p : t, p.1.2 < orders p.1.1 := by
    intro p
    have hpMem : p.1 ∈ ht.toFinset := by simpa using p.2
    have hle : p.1.2 ≤ ∑ q ∈ ht.toFinset,
        if q.1 = p.1.1 then q.2 else 0 := by
      let f : Fin m × ℕ → ℕ := fun q => if q.1 = p.1.1 then q.2 else 0
      have hs := Finset.single_le_sum (s := ht.toFinset) (f := f)
        (fun q hq => Nat.zero_le _) hpMem
      simpa [f] using hs
    dsimp [orders]
    omega
  let e : t → Σ i, Fin (orders i) := fun p => ⟨p.1.1, ⟨p.1.2, horder p⟩⟩
  have he : Function.Injective e := by
    intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Sigma.fst hpq
    · exact congrArg (fun s => s.2.1) hpq
  have hrect := upperEndFiniteRectangle_algebraicIndependent
    shiftValue shiftCode hshiftCode orders u hfree
  have hcomp := hrect.comp e he
  simpa [e, upperEndFieldJetAssignment, boundedGaugeTranslatedPrimeLogUpperEnd] using hcomp

/-- **Countable-shift upper-end differential independence.** Functional pattern freeness is exactly
genuine differential independence of the complete translated source family in the upper-end
meromorphic field. -/
theorem upperEndShift_differentialIndependent
    {Γ : Type*} (shiftValue : Γ → ℂ) (u : PrimeLogBoundedGauge)
    (hfree : CountableShiftPolynomialDifferentialFree shiftValue u) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (boundedGaugeTranslatedPrimeLogUpperEnd shiftValue u) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  unfold DifferentialIndependent
  apply algebraicIndependent_of_finite_type
  intro t ht
  let s : Set Γ := Prod.fst '' t
  have hs : s.Finite := ht.image Prod.fst
  letI : Finite s := hs
  letI : Fintype s := Fintype.ofFinite s
  let eΓ : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let shiftCode : Fin (Fintype.card s) → Γ := fun i => (eΓ.symm i).1
  have hshiftCode : Function.Injective shiftCode := by
    intro i j hij
    apply eΓ.symm.injective
    exact Subtype.ext hij
  have hfin := upperEndFiniteShift_differentialIndependent
    shiftValue shiftCode hshiftCode u hfree
  have hsDI : DifferentialIndependent (RatFunc ℂ)
      (fun γ : s => boundedGaugeTranslatedPrimeLogUpperEnd shiftValue u γ.1) := by
    have hcomp := hfin.comp eΓ eΓ.injective
    simpa [shiftCode, Function.comp_def] using hcomp
  unfold DifferentialIndependent at hsDI
  let et : t → s × ℕ := fun p =>
    (⟨p.1.1, ⟨p.1, p.2, rfl⟩⟩, p.1.2)
  have het : Function.Injective et := by
    intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun x : s × ℕ => x.1.1) hpq
    · exact congrArg (fun x : s × ℕ => x.2) hpq
  have hcomp := hsDI.comp et het
  simpa [et, s] using hcomp

/-- Every countable injective shift palette admits a bounded prime-log source whose entire
translation family is differentially independent over `C(z)` in the upper-end field. -/
theorem exists_upperEndShift_differentialIndependent
    {Γ : Type*} [Countable Γ] (shiftValue : Γ → ℂ)
    (hshiftValue : Function.Injective shiftValue) :
    ∃ u : PrimeLogBoundedGauge,
      letI := isDomain_upperEndAnalyticSubring
      letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
      letI := upperEndMeroFieldDifferential
      DifferentialIndependent (RatFunc ℂ)
        (boundedGaugeTranslatedPrimeLogUpperEnd shiftValue u) := by
  obtain ⟨u, hu⟩ := exists_countableShiftPolynomialDifferentialFree
    shiftValue hshiftValue
  exact ⟨u, upperEndShift_differentialIndependent shiftValue u hu⟩

/-- The exact rational-lattice palette used by the facet-sewn construction has a genuine
upper-end meromorphic realization with a differentially independent full translation family. -/
theorem exists_rationalLatticeShift_upperEnd_differentialIndependent
    {V : Type*} [Fintype V] (omega : V → ℝ) :
    ∃ u : PrimeLogBoundedGauge,
      letI := isDomain_upperEndAnalyticSubring
      letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
      letI := upperEndMeroFieldDifferential
      DifferentialIndependent (RatFunc ℂ)
        (boundedGaugeTranslatedPrimeLogUpperEnd
          ((↑) : rationalLatticeShiftSet omega → ℂ) u) :=
  exists_upperEndShift_differentialIndependent
    ((↑) : rationalLatticeShiftSet omega → ℂ) Subtype.val_injective

end

end GaloisForLFunctions.HTGeometry
