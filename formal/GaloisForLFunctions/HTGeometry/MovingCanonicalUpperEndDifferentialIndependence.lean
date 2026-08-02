import GaloisForLFunctions.HTGeometry.UpperEndRationalGauge
import GaloisForLFunctions.HTGeometry.UpperEndPrimeLogJets
import GaloisForLFunctions.HTGeometry.FamilyJetReshape
import GaloisForLFunctions.HTGeometry.MovingCanonicalFullTranslationFreeness
import GaloisForLFunctions.HTGeometry.MovingEvenCanonicalFullTranslationFreeness

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Filter Set Topology Function Polynomial
open ClassicalAnalyticNevanlinnaCarrierFamily
open scoped Differential

noncomputable section

/-- An analytic function on an upper tail, represented in the upper-end analytic ring. -/
def analyticUpperEndElement
    (f : ℂ → ℂ) (H : ℝ)
    (hf : AnalyticOnNhd ℂ f (upperTail H)) :
    upperEndAnalyticSubring :=
  ⟨Germ.coeRingHom upperEndFilter f, f, H, hf, rfl⟩

/-- The corresponding element of the upper-end meromorphic field. -/
def analyticUpperEndMero
    (f : ℂ → ℂ) (H : ℝ)
    (hf : AnalyticOnNhd ℂ f (upperTail H)) :
    upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  exact algebraMap upperEndAnalyticSubring upperEndMeroField
    (analyticUpperEndElement f H hf)

/-- Genuine iterated derivatives of an upper-tail analytic function. -/
def analyticUpperEndJet
    (f : ℂ → ℂ) (H : ℝ)
    (hf : AnalyticOnNhd ℂ f (upperTail H))
    (n : ℕ) : upperEndAnalyticSubring :=
  analyticUpperEndElement (iteratedDeriv n f) H
    (analyticOnNhd_iteratedDeriv hf n)

theorem upperEndAnalyticDeriv_analyticUpperEndJet
    (f : ℂ → ℂ) (H : ℝ)
    (hf : AnalyticOnNhd ℂ f (upperTail H))
    (n : ℕ) :
    upperEndAnalyticDeriv
        (analyticUpperEndJet f H hf n) =
      analyticUpperEndJet f H hf (n + 1) := by
  apply Subtype.ext
  change
    (deriv (iteratedDeriv n f) :
        Germ upperEndFilter ℂ) =
      (iteratedDeriv (n + 1) f :
        Germ upperEndFilter ℂ)
  rw [iteratedDeriv_succ]

theorem differentialJet_analyticUpperEndMero
    (f : ℂ → ℂ) (H : ℝ)
    (hf : AnalyticOnNhd ℂ f (upperTail H))
    (n : ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI := upperEndMeroFieldDifferential
    differentialJet n (analyticUpperEndMero f H hf) =
      algebraMap upperEndAnalyticSubring
        upperEndMeroField
        (analyticUpperEndJet f H hf n) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring :=
    Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField :=
    Ring.toIntAlgebra _
  letI := upperEndMeroFieldDifferential
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show n + 1 = n + 1 by rfl,
        differentialJet_succ, ih,
        upperEndMeroFieldDifferential_algebraMap,
        upperEndAnalyticDeriv_analyticUpperEndJet]

theorem familyReshapeJet_comp_familyReshapeJetInv
    (m n : ℕ) :
    (familyReshapeJet m n).comp
        (familyReshapeJetInv m n) =
      RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        simp only [map_add, hp, hq]
    | monomial k c =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial]
        simp [familyReshapeJet, familyReshapeJetInv]
  · intro s
    simp [familyReshapeJet,
      familyReshapeJetInv]

theorem familyReshapeJetInv_injective
    (m n : ℕ) :
    Function.Injective (familyReshapeJetInv m n) := by
  intro P Q hPQ
  have hP := RingHom.congr_fun
    (familyReshapeJet_comp_familyReshapeJetInv m n) P
  have hQ := RingHom.congr_fun
    (familyReshapeJet_comp_familyReshapeJetInv m n) Q
  rw [RingHom.comp_apply, RingHom.id_apply] at hP hQ
  rw [← hP, ← hQ, hPQ]

/-- Genuine analytic family jets as elements of the upper-end analytic ring. -/
def analyticUpperEndFamilyJetAssignment
    {m n : ℕ} (g : Fin m → ℂ → ℂ)
    (H : Fin m → ℝ)
    (hg : ∀ i,
      AnalyticOnNhd ℂ (g i) (upperTail (H i))) :
    Fin m × Fin (n + 1) →
      upperEndAnalyticSubring :=
  fun s =>
    analyticUpperEndJet
      (g s.1) (H s.1) (hg s.1) s.2.1

/-- Differential-field family jets in the upper-end meromorphic field. -/
def analyticUpperEndFamilyFieldJet
    {m n : ℕ} (g : Fin m → ℂ → ℂ)
    (H : Fin m → ℝ)
    (hg : ∀ i,
      AnalyticOnNhd ℂ (g i) (upperTail (H i))) :
    Fin m × Fin (n + 1) →
      upperEndMeroField :=
  fun s =>
    letI := isDomain_upperEndAnalyticSubring
    letI := upperEndMeroFieldDifferential
    differentialJet s.2.1
      (analyticUpperEndMero
        (g s.1) (H s.1) (hg s.1))

theorem analyticUpperEndFamilyFieldJet_eq_algebraMap
    {m n : ℕ} (g : Fin m → ℂ → ℂ)
    (H : Fin m → ℝ)
    (hg : ∀ i,
      AnalyticOnNhd ℂ (g i) (upperTail (H i)))
    (s : Fin m × Fin (n + 1)) :
    letI := isDomain_upperEndAnalyticSubring
    letI := upperEndMeroFieldDifferential
    analyticUpperEndFamilyFieldJet g H hg s =
      algebraMap upperEndAnalyticSubring
        upperEndMeroField
        (analyticUpperEndFamilyJetAssignment
          g H hg s) := by
  letI := isDomain_upperEndAnalyticSubring
  letI := upperEndMeroFieldDifferential
  exact differentialJet_analyticUpperEndMero
    (g s.1) (H s.1) (hg s.1) s.2.1

/-- Polynomial-coefficient evaluation on genuine family jets. -/
def analyticFamilyPolynomialCoefficientRelation
    {m n : ℕ} (g : Fin m → ℂ → ℂ)
    (Q : MvPolynomial
      (Fin m × Fin (n + 1)) (Polynomial ℂ))
    (z : ℂ) : ℂ :=
  MvPolynomial.eval
    (fun s => iteratedDeriv s.2.1 (g s.1) z)
    (specializePolynomialCoefficients z Q)

theorem analyticUpperEndFamilyRelation_coe
    {m n : ℕ} (g : Fin m → ℂ → ℂ)
    (H : Fin m → ℝ)
    (hg : ∀ i,
      AnalyticOnNhd ℂ (g i) (upperTail (H i)))
    (Q : MvPolynomial
      (Fin m × Fin (n + 1)) (Polynomial ℂ)) :
    ((MvPolynomial.eval₂ upperEndPolyToAnalytic
        (analyticUpperEndFamilyJetAssignment
          g H hg) Q :
        upperEndAnalyticSubring) :
      Germ upperEndFilter ℂ) =
      (analyticFamilyPolynomialCoefficientRelation
        g Q : Germ upperEndFilter ℂ) := by
  induction Q using MvPolynomial.induction_on with
  | C p =>
      rw [MvPolynomial.eval₂_C]
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun z => by
        simp [analyticFamilyPolynomialCoefficientRelation,
          specializePolynomialCoefficients]
  | add P Q hP hQ =>
      rw [MvPolynomial.eval₂_add]
      change
        ((MvPolynomial.eval₂ upperEndPolyToAnalytic
          (analyticUpperEndFamilyJetAssignment
            g H hg) P :
          upperEndAnalyticSubring) :
            Germ upperEndFilter ℂ) +
        ((MvPolynomial.eval₂ upperEndPolyToAnalytic
          (analyticUpperEndFamilyJetAssignment
            g H hg) Q :
          upperEndAnalyticSubring) :
            Germ upperEndFilter ℂ) = _
      rw [hP, hQ, ← Germ.coe_add]
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun z => by
        simp [analyticFamilyPolynomialCoefficientRelation,
          specializePolynomialCoefficients]
  | mul_X P s hP =>
      rw [MvPolynomial.eval₂_mul,
        MvPolynomial.eval₂_X]
      change
        ((MvPolynomial.eval₂ upperEndPolyToAnalytic
          (analyticUpperEndFamilyJetAssignment
            g H hg) P :
          upperEndAnalyticSubring) :
            Germ upperEndFilter ℂ) *
        (analyticUpperEndFamilyJetAssignment
            g H hg s :
          Germ upperEndFilter ℂ) = _
      rw [hP]
      change
        (analyticFamilyPolynomialCoefficientRelation
            g P : Germ upperEndFilter ℂ) *
          (iteratedDeriv s.2.1 (g s.1) :
            Germ upperEndFilter ℂ) =
          (analyticFamilyPolynomialCoefficientRelation
            g (P * MvPolynomial.X s) :
              Germ upperEndFilter ℂ)
      rw [← Germ.coe_mul]
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun z => by
        simp [analyticFamilyPolynomialCoefficientRelation,
          specializePolynomialCoefficients]

/-- Polynomial evaluation in the upper-end field factors through the
embedded rational coordinate field. -/
theorem analyticUpperEndPolyToMero_eq_comp :
    letI := isDomain_upperEndAnalyticSubring
    upperEndPolyToMero =
      upperEndRatfuncToMero.comp
        (algebraMap ℂ[X] (RatFunc ℂ)) := by
  letI := isDomain_upperEndAnalyticSubring
  apply DFunLike.ext _ _
  intro p
  exact
    (upperEndRatfuncToMero_algebraMap_polynomial p).symm

/-- A rational-coefficient relation in the upper-end field clears to a
polynomial-coefficient relation in the upper-end analytic ring. -/
theorem analyticUpperEndClearedRelation_eq_zero_of_fieldRelation_eq_zero
    {m n : ℕ} (g : Fin m → ℂ → ℂ)
    (H : Fin m → ℝ)
    (hg : ∀ i,
      AnalyticOnNhd ℂ (g i) (upperTail (H i)))
    (Q : MvPolynomial
      (Fin m × Fin (n + 1)) (RatFunc ℂ))
    (hzero :
      letI := isDomain_upperEndAnalyticSubring
      letI : Algebra (RatFunc ℂ) upperEndMeroField :=
        upperEndRatfuncToMero.toAlgebra
      letI := upperEndMeroFieldDifferential
      MvPolynomial.eval₂ upperEndRatfuncToMero
        (analyticUpperEndFamilyFieldJet g H hg) Q = 0) :
    MvPolynomial.eval₂ upperEndPolyToAnalytic
      (analyticUpperEndFamilyJetAssignment g H hg)
      (clearRatFuncCoefficients Q) = 0 := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring :=
    Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField :=
    Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  let fieldJet :
      Fin m × Fin (n + 1) → upperEndMeroField :=
    analyticUpperEndFamilyFieldJet g H hg
  let analyticJet :
      Fin m × Fin (n + 1) →
        upperEndAnalyticSubring :=
    analyticUpperEndFamilyJetAssignment g H hg
  have hclearField :
      MvPolynomial.eval₂ upperEndPolyToMero fieldJet
        (clearRatFuncCoefficients Q) = 0 := by
    calc
      MvPolynomial.eval₂ upperEndPolyToMero fieldJet
          (clearRatFuncCoefficients Q) =
          MvPolynomial.eval₂ upperEndRatfuncToMero fieldJet
            (MvPolynomial.map
              (algebraMap ℂ[X] (RatFunc ℂ))
              (clearRatFuncCoefficients Q)) := by
            rw [MvPolynomial.eval₂_map]
            rw [← analyticUpperEndPolyToMero_eq_comp]
      _ = MvPolynomial.eval₂ upperEndRatfuncToMero fieldJet
          (MvPolynomial.C
            (algebraMap ℂ[X] (RatFunc ℂ)
              (ratFuncCommonDenominator Q)) * Q) := by
            rw [map_clearRatFuncCoefficients]
      _ = 0 := by
        rw [MvPolynomial.eval₂_mul,
          MvPolynomial.eval₂_C, hzero, mul_zero]
  have hmap :
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (MvPolynomial.eval₂ upperEndPolyToAnalytic
          analyticJet (clearRatFuncCoefficients Q)) = 0 := by
    rw [MvPolynomial.eval₂_comp_right]
    rw [MvPolynomial.eval₂_map]
    change
      MvPolynomial.eval₂ upperEndPolyToMero
        (fun s =>
          algebraMap upperEndAnalyticSubring
            upperEndMeroField (analyticJet s))
        (clearRatFuncCoefficients Q) = 0
    rw [show
        (fun s =>
          algebraMap upperEndAnalyticSubring
            upperEndMeroField (analyticJet s)) =
          fieldJet by
        funext s
        exact
          (analyticUpperEndFamilyFieldJet_eq_algebraMap
            g H hg s).symm]
    exact hclearField
  exact
    (IsFractionRing.injective
      upperEndAnalyticSubring upperEndMeroField)
      (by simpa using hmap)

/-- A nonzero rational-coefficient upper-end field relation propagates
to a genuine polynomial differential relation on every connected
analytic domain which meets every upper tail. -/
theorem familyDifferentiallyAlgebraicOn_of_upperEndFieldRelation
    {m n : ℕ} {U : Set ℂ}
    (g : Fin m → ℂ → ℂ)
    (H : Fin m → ℝ)
    (hg : ∀ i,
      AnalyticOnNhd ℂ (g i) (upperTail (H i)))
    (hgU : ∀ i, AnalyticOnNhd ℂ (g i) U)
    (hUpre : IsPreconnected U)
    (hUcofinal :
      ∀ L : ℝ, ∃ z ∈ U, z ∈ upperTail L)
    (Q : MvPolynomial
      (Fin m × Fin (n + 1)) (RatFunc ℂ))
    (hQ : Q ≠ 0)
    (hzero :
      letI := isDomain_upperEndAnalyticSubring
      letI : Algebra (RatFunc ℂ) upperEndMeroField :=
        upperEndRatfuncToMero.toAlgebra
      letI := upperEndMeroFieldDifferential
      MvPolynomial.eval₂ upperEndRatfuncToMero
        (analyticUpperEndFamilyFieldJet g H hg) Q = 0) :
    FamilyDifferentiallyAlgebraicOn g U := by
  let Qclear :
      MvPolynomial
        (Fin m × Fin (n + 1)) (Polynomial ℂ) :=
    clearRatFuncCoefficients Q
  let P : MvPolynomial (FamilyJetIndex m n) ℂ :=
    familyReshapeJetInv m n Qclear
  have hQclear : Qclear ≠ 0 :=
    clearRatFuncCoefficients_ne_zero Q hQ
  have hP : P ≠ 0 := by
    intro hP0
    exact hQclear
      (familyReshapeJetInv_injective m n
        (by simpa [P] using hP0))
  have hreshape :
      familyReshapeJet m n P = Qclear := by
    exact RingHom.congr_fun
      (familyReshapeJet_comp_familyReshapeJetInv m n)
      Qclear
  have hclear :
      MvPolynomial.eval₂ upperEndPolyToAnalytic
        (analyticUpperEndFamilyJetAssignment g H hg)
        Qclear = 0 := by
    exact
      analyticUpperEndClearedRelation_eq_zero_of_fieldRelation_eq_zero
        g H hg Q hzero
  have hgerm :
      (analyticFamilyPolynomialCoefficientRelation
          g Qclear : Germ upperEndFilter ℂ) = 0 := by
    rw [← analyticUpperEndFamilyRelation_coe g H hg]
    exact congrArg Subtype.val hclear
  rw [← Germ.coe_zero, Germ.coe_eq] at hgerm
  change
    ∀ᶠ z in upperEndFilter,
      analyticFamilyPolynomialCoefficientRelation
        g Qclear z = 0 at hgerm
  rw [upperEndFilter_basis.eventually_iff] at hgerm
  obtain ⟨L, -, hL⟩ := hgerm
  obtain ⟨w, hwU, hwL⟩ := hUcofinal L
  let F : ℂ → ℂ :=
    fun z => MvPolynomial.eval (familyJetVec g z) P
  have hrelation (z : ℂ) :
      analyticFamilyPolynomialCoefficientRelation
          g Qclear z = F z := by
    rw [← hreshape]
    simpa [F, analyticFamilyPolynomialCoefficientRelation,
      familyJetVec] using
      (eval_specialize_familyReshapeJet m n z
        (fun s =>
          iteratedDeriv s.2.1 (g s.1) z) P)
  have hlocal : F =ᶠ[nhds w] 0 := by
    filter_upwards
      [(upperTail_isOpen L).mem_nhds hwL] with z hz
    rw [← hrelation]
    exact hL hz
  have hcoords :
      ∀ s : FamilyJetIndex m n,
        AnalyticOnNhd ℂ
          (fun z => familyJetVec g z s) U := by
    intro s
    cases s with
    | inl x =>
        cases x
        simpa [familyJetVec] using
          (analyticOnNhd_id :
            AnalyticOnNhd ℂ (id : ℂ → ℂ) U)
    | inr s =>
        simpa [familyJetVec] using
          analyticOnNhd_iteratedDeriv
            (hgU s.1) s.2.1
  have hF : AnalyticOnNhd ℂ F U := by
    simpa [F, MvPolynomial.aeval_def] using
      (AnalyticOnNhd.aeval_mvPolynomial hcoords P)
  have hall : Set.EqOn F 0 U :=
    hF.eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const hUpre hwU hlocal
  exact ⟨n, P, hP, hall⟩

/-- Functional differential freeness on a connected cofinal analytic
domain gives genuine differential independence of the corresponding
finite family in the upper-end meromorphic field. -/
theorem analyticUpperEndFiniteFamily_differentialIndependent
    {m : ℕ} {U : Set ℂ}
    (g : Fin m → ℂ → ℂ)
    (H : Fin m → ℝ)
    (hg : ∀ i,
      AnalyticOnNhd ℂ (g i) (upperTail (H i)))
    (hgU : ∀ i, AnalyticOnNhd ℂ (g i) U)
    (hUpre : IsPreconnected U)
    (hUcofinal :
      ∀ L : ℝ, ∃ z ∈ U, z ∈ upperTail L)
    (hfree : ¬ FamilyDifferentiallyAlgebraicOn g U) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (fun i => analyticUpperEndMero
        (g i) (H i) (hg i)) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring :=
    Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField :=
    Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  unfold DifferentialIndependent
  apply algebraicIndependent_of_finite_type
  intro t ht
  let n : ℕ :=
    ∑ p ∈ ht.toFinset, p.2
  have horder : ∀ p : t, p.1.2 < n + 1 := by
    intro p
    have hpMem : p.1 ∈ ht.toFinset :=
      ht.mem_toFinset.mpr p.2
    have hle :
        p.1.2 ≤ ∑ q ∈ ht.toFinset, q.2 := by
      exact Finset.single_le_sum
        (fun q _ => Nat.zero_le q.2) hpMem
    dsimp [n]
    omega
  let e : t → Fin m × Fin (n + 1) :=
    fun p => (p.1.1, ⟨p.1.2, horder p⟩)
  have he : Function.Injective e := by
    intro p q hpq
    change
      (p.1.1, (⟨p.1.2, horder p⟩ :
        Fin (n + 1))) =
        (q.1.1, (⟨q.1.2, horder q⟩ :
          Fin (n + 1))) at hpq
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg
        (fun s : Fin m × Fin (n + 1) => s.1) hpq
    · exact congrArg
        (fun s : Fin m × Fin (n + 1) => s.2.1) hpq
  have hrect :
      AlgebraicIndependent (RatFunc ℂ)
        (analyticUpperEndFamilyFieldJet
          (n := n) g H hg) := by
    rw [algebraicIndependent_iff]
    intro Q hQeval
    by_contra hQ
    apply hfree
    apply
      familyDifferentiallyAlgebraicOn_of_upperEndFieldRelation
        g H hg hgU hUpre hUcofinal Q hQ
    simpa [MvPolynomial.aeval_def,
      RingHom.algebraMap_toAlgebra] using hQeval
  have hcomp := hrect.comp e he
  simpa [e, analyticUpperEndFamilyFieldJet] using! hcomp

theorem commonUpperTranslationDomain_isPreconnected
    {m : ℕ}
    (shift : InjectiveShiftConfiguration (Fin m)) :
    IsPreconnected (commonUpperTranslationDomain shift) := by
  rw [show commonUpperTranslationDomain shift =
      ⋂ i : Fin m, upperTail (-(shift.1 i).im) by
    ext z
    simp only [commonUpperTranslationDomain,
      mem_setOf_eq, mem_iInter, upperTail]
    constructor
    · intro hz i
      have hi := hz i
      simp only [Complex.add_im] at hi ⊢
      linarith
    · intro hz i
      have hi := hz i
      simp only [Complex.add_im] at hi ⊢
      linarith]
  exact
    (convex_iInter fun i =>
      convex_halfSpace_im_gt (-(shift.1 i).im)).isPreconnected

theorem commonUpperTranslationDomain_meets_upperTail
    {m : ℕ}
    (shift : InjectiveShiftConfiguration (Fin m))
    (L : ℝ) :
    ∃ z ∈ commonUpperTranslationDomain shift,
      z ∈ upperTail L := by
  obtain ⟨H, hH⟩ :=
    finite_complex_family_has_imaginary_lower_bound shift.1
  let z : ℂ := ((max H L + 1 : ℝ) : ℂ) * Complex.I
  refine ⟨z, ?_, ?_⟩
  · intro i
    simp only [z, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero,
      add_zero]
    linarith [hH i, le_max_left H L]
  · simp only [z, upperTail, mem_setOf_eq,
      Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero]
    linarith [le_max_right H L]

theorem analyticOnNhd_movingCanonicalLogDerivative_translate_upperTail
    (θ : BoundedRealSequence) (h : ℂ) :
    AnalyticOnNhd ℂ
      (fun z => movingCanonicalLogDerivative θ (z + h))
      (upperTail (-h.im)) := by
  intro z hz
  change -h.im < z.im at hz
  have hpos : 0 < (z + h).im := by
    rw [Complex.add_im]
    linarith
  change AnalyticAt ℂ
    (movingCanonicalLogDerivative θ ∘
      fun w : ℂ => w + h) z
  exact AnalyticAt.comp (x := z)
    (analyticAt_movingCanonicalLogDerivative θ hpos)
    (analyticAt_id.add analyticAt_const)

/-- A translated canonical logarithmic derivative as an upper-end
meromorphic element. -/
def movingCanonicalTranslatedUpperEndMero
    (θ : BoundedRealSequence) (h : ℂ) :
    upperEndMeroField :=
  analyticUpperEndMero
    (fun z => movingCanonicalLogDerivative θ (z + h))
    (-h.im)
    (analyticOnNhd_movingCanonicalLogDerivative_translate_upperTail
      θ h)

/-- Every finite injective translation packet of a canonically free
phase is genuinely differentially independent over `ℂ(z)` in the
upper-end meromorphic field. -/
theorem movingCanonicalFiniteTranslation_upperEnd_differentialIndependent
    {m : ℕ} (θ : BoundedRealSequence)
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
    (shift : InjectiveShiftConfiguration (Fin m)) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (fun i =>
        movingCanonicalTranslatedUpperEndMero
          θ (shift.1 i)) := by
  let g : Fin m → ℂ → ℂ :=
    fun i z =>
      movingCanonicalLogDerivative θ (z + shift.1 i)
  let H : Fin m → ℝ :=
    fun i => -(shift.1 i).im
  have hg :
      ∀ i, AnalyticOnNhd ℂ (g i) (upperTail (H i)) := by
    intro i
    exact
      analyticOnNhd_movingCanonicalLogDerivative_translate_upperTail
        θ (shift.1 i)
  have hgU :
      ∀ i,
        AnalyticOnNhd ℂ (g i)
          (commonUpperTranslationDomain shift) := by
    intro i z hz
    have hpos : 0 < (z + shift.1 i).im := hz i
    change AnalyticAt ℂ
      (movingCanonicalLogDerivative θ ∘
        fun w : ℂ => w + shift.1 i) z
    exact AnalyticAt.comp (x := z)
      (analyticAt_movingCanonicalLogDerivative θ hpos)
      (analyticAt_id.add analyticAt_const)
  have hfunctional :
      ¬ FamilyDifferentiallyAlgebraicOn g
        (commonUpperTranslationDomain shift) := by
    exact
      not_familyDifferentiallyAlgebraicOn_movingCanonicalLogDerivative_of_relationFree
        m θ hfree shift
  simpa [g, H, movingCanonicalTranslatedUpperEndMero] using
    analyticUpperEndFiniteFamily_differentialIndependent
      g H hg hgU
      (commonUpperTranslationDomain_isPreconnected shift)
      (commonUpperTranslationDomain_meets_upperTail shift)
      hfunctional

/-- A canonically free phase has a genuinely differentially independent
full complex-translation family in the upper-end meromorphic field. -/
theorem movingCanonicalTranslation_upperEnd_differentialIndependent
    (θ : BoundedRealSequence)
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
      ∀ col, coeff col = 0) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (movingCanonicalTranslatedUpperEndMero θ) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring :=
    Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField :=
    Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  unfold DifferentialIndependent
  apply algebraicIndependent_of_finite_type
  intro t ht
  let s : Set ℂ := Prod.fst '' t
  have hs : s.Finite := ht.image Prod.fst
  letI : Finite s := hs
  letI : Fintype s := Fintype.ofFinite s
  let eShift : s ≃ Fin (Fintype.card s) :=
    Fintype.equivFin s
  let shift :
      InjectiveShiftConfiguration
        (Fin (Fintype.card s)) :=
    ⟨fun i => (eShift.symm i).1, by
      intro i j hij
      apply eShift.symm.injective
      exact Subtype.ext hij⟩
  have hfin :=
    movingCanonicalFiniteTranslation_upperEnd_differentialIndependent
      θ hfree shift
  have hsDI : DifferentialIndependent (RatFunc ℂ)
      (fun h : s =>
        movingCanonicalTranslatedUpperEndMero θ h.1) := by
    have hcomp := hfin.comp eShift eShift.injective
    simpa [shift, Function.comp_def] using hcomp
  unfold DifferentialIndependent at hsDI
  let et : t → s × ℕ :=
    fun p =>
      (⟨p.1.1, ⟨p.1, p.2, rfl⟩⟩, p.1.2)
  have het : Function.Injective et := by
    intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg
        (fun x : s × ℕ => x.1.1) hpq
    · exact congrArg
        (fun x : s × ℕ => x.2) hpq
  have hcomp := hsDI.comp et het
  simpa [et, s] using! hcomp

/-- Dense residual canonical phases have full complex-translation
differential independence over `ℂ(z)` in the upper-end field. -/
theorem
    movingCanonical_fullTranslationUpperEndDifferentialIndependence_denseResidual :
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
          (movingCanonicalTranslatedUpperEndMero θ) := by
  dsimp only
  have hphase :=
    movingCanonical_fullTranslationFreeness_denseResidual
  dsimp only at hphase
  refine ⟨hphase.1, hphase.2.1, ?_⟩
  intro θ hθ
  exact
    movingCanonicalTranslation_upperEnd_differentialIndependent
      θ hθ

theorem analyticOnNhd_movingEvenCanonicalCarrier_translate_upperTail
    (θ : BoundedRealSequence) (h : ℂ) :
    AnalyticOnNhd ℂ
      (fun z => movingEvenCanonicalCarrier θ (z + h))
      (upperTail (-h.im)) := by
  intro z hz
  change -h.im < z.im at hz
  have hpos : 0 < (z + h).im := by
    rw [Complex.add_im]
    linarith
  have hneg : (-(z + h)).im ≠ 0 := by
    simp only [Complex.neg_im]
    exact (neg_ne_zero.mpr (ne_of_gt hpos))
  change AnalyticAt ℂ
    ((fun w =>
      movingCanonicalLogDerivative θ w -
        movingCanonicalLogDerivative θ (-w)) ∘
      fun w : ℂ => w + h) z
  apply AnalyticAt.comp (x := z)
  · exact
      (analyticAt_movingCanonicalLogDerivative θ hpos).sub
        ((analyticAt_movingCanonicalLogDerivative_of_im_ne_zero
          θ hneg).comp (by fun_prop))
  · exact analyticAt_id.add analyticAt_const

/-- A translated even canonical carrier as an upper-end meromorphic
element. -/
def movingEvenCanonicalTranslatedUpperEndMero
    (θ : BoundedRealSequence) (h : ℂ) :
    upperEndMeroField :=
  analyticUpperEndMero
    (fun z => movingEvenCanonicalCarrier θ (z + h))
    (-h.im)
    (analyticOnNhd_movingEvenCanonicalCarrier_translate_upperTail
      θ h)

theorem
    movingEvenCanonicalFiniteTranslation_upperEnd_differentialIndependent
    {m : ℕ} (θ : BoundedRealSequence)
    (hfree : ∀ (p : FiniteDifferentialPattern ℕ)
      (shift :
        InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff :
        CarrierPatternMonomial p ×
          Fin (p.coefficientDegree + 1) → ℂ),
      movingEvenCanonicalExpandedPatternRelationHolds
        (row := CarrierPatternRow p)
        p.coefficientDegree p.orders
        (carrierPatternExponent p) θ shift coeff →
      ∀ col, coeff col = 0)
    (shift : InjectiveShiftConfiguration (Fin m)) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (fun i =>
        movingEvenCanonicalTranslatedUpperEndMero
          θ (shift.1 i)) := by
  let g : Fin m → ℂ → ℂ :=
    fun i z =>
      movingEvenCanonicalCarrier θ (z + shift.1 i)
  let H : Fin m → ℝ :=
    fun i => -(shift.1 i).im
  have hg :
      ∀ i, AnalyticOnNhd ℂ (g i) (upperTail (H i)) := by
    intro i
    exact
      analyticOnNhd_movingEvenCanonicalCarrier_translate_upperTail
        θ (shift.1 i)
  have hgU :
      ∀ i,
        AnalyticOnNhd ℂ (g i)
          (commonUpperTranslationDomain shift) := by
    intro i z hz
    have hpos : 0 < (z + shift.1 i).im := hz i
    have hneg : (-(z + shift.1 i)).im ≠ 0 := by
      simp only [Complex.neg_im]
      exact neg_ne_zero.mpr (ne_of_gt hpos)
    change AnalyticAt ℂ
      ((fun w =>
        movingCanonicalLogDerivative θ w -
          movingCanonicalLogDerivative θ (-w)) ∘
        fun w : ℂ => w + shift.1 i) z
    apply AnalyticAt.comp (x := z)
    · exact
        (analyticAt_movingCanonicalLogDerivative θ hpos).sub
          ((analyticAt_movingCanonicalLogDerivative_of_im_ne_zero
            θ hneg).comp (by fun_prop))
    · exact analyticAt_id.add analyticAt_const
  have hfunctional :
      ¬ FamilyDifferentiallyAlgebraicOn g
        (commonUpperTranslationDomain shift) := by
    exact
      not_familyDifferentiallyAlgebraicOn_movingEvenCanonicalCarrier_of_relationFree
        m θ hfree shift
  simpa [g, H,
    movingEvenCanonicalTranslatedUpperEndMero] using
    analyticUpperEndFiniteFamily_differentialIndependent
      g H hg hgU
      (commonUpperTranslationDomain_isPreconnected shift)
      (commonUpperTranslationDomain_meets_upperTail shift)
      hfunctional

theorem
    movingEvenCanonicalTranslation_upperEnd_differentialIndependent
    (θ : BoundedRealSequence)
    (hfree : ∀ (p : FiniteDifferentialPattern ℕ)
      (shift :
        InjectiveShiftConfiguration (CarrierPatternShift p))
      (coeff :
        CarrierPatternMonomial p ×
          Fin (p.coefficientDegree + 1) → ℂ),
      movingEvenCanonicalExpandedPatternRelationHolds
        (row := CarrierPatternRow p)
        p.coefficientDegree p.orders
        (carrierPatternExponent p) θ shift coeff →
      ∀ col, coeff col = 0) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField :=
      upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (movingEvenCanonicalTranslatedUpperEndMero θ) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring :=
    Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField :=
    Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  unfold DifferentialIndependent
  apply algebraicIndependent_of_finite_type
  intro t ht
  let s : Set ℂ := Prod.fst '' t
  have hs : s.Finite := ht.image Prod.fst
  letI : Finite s := hs
  letI : Fintype s := Fintype.ofFinite s
  let eShift : s ≃ Fin (Fintype.card s) :=
    Fintype.equivFin s
  let shift :
      InjectiveShiftConfiguration
        (Fin (Fintype.card s)) :=
    ⟨fun i => (eShift.symm i).1, by
      intro i j hij
      apply eShift.symm.injective
      exact Subtype.ext hij⟩
  have hfin :=
    movingEvenCanonicalFiniteTranslation_upperEnd_differentialIndependent
      θ hfree shift
  have hsDI : DifferentialIndependent (RatFunc ℂ)
      (fun h : s =>
        movingEvenCanonicalTranslatedUpperEndMero θ h.1) := by
    have hcomp := hfin.comp eShift eShift.injective
    simpa [shift, Function.comp_def] using hcomp
  unfold DifferentialIndependent at hsDI
  let et : t → s × ℕ :=
    fun p =>
      (⟨p.1.1, ⟨p.1, p.2, rfl⟩⟩, p.1.2)
  have het : Function.Injective et := by
    intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg
        (fun x : s × ℕ => x.1.1) hpq
    · exact congrArg
        (fun x : s × ℕ => x.2) hpq
  have hcomp := hsDI.comp et het
  simpa [et, s] using! hcomp

theorem
    movingEvenCanonical_fullTranslationUpperEndDifferentialIndependence_denseResidual :
    let universalPhase : Set BoundedRealSequence := {θ |
      ∀ (p : FiniteDifferentialPattern ℕ)
        (shift :
          InjectiveShiftConfiguration (CarrierPatternShift p))
        (coeff :
          CarrierPatternMonomial p ×
            Fin (p.coefficientDegree + 1) → ℂ),
        movingEvenCanonicalExpandedPatternRelationHolds
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
          (movingEvenCanonicalTranslatedUpperEndMero θ) := by
  dsimp only
  have hphase :=
    movingEvenCanonical_fullTranslationFreeness_denseResidual
  dsimp only at hphase
  refine ⟨hphase.1, hphase.2.1, ?_⟩
  intro θ hθ
  exact
    movingEvenCanonicalTranslation_upperEnd_differentialIndependent
      θ hθ

end

end GaloisForLFunctions.HTGeometry
