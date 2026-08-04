import GaloisForLFunctions.HTGeometry.JetAdjoinField
import GaloisForLFunctions.HTGeometry.DifferentialLurothVariableSupport

/-!
# A differential relation as a univariate polynomial over the jet prefix field

Singling out the top jet turns a scalar differential relation of order `m` into a univariate
polynomial whose coefficients, evaluated at the lower jets, lie in the jet prefix field.  The
resulting univariate polynomial annihilates the top jet, its degree is the leader degree, and its
leading coefficient is the evaluated initial.
-/

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]

section

variable (B : IntermediateField F E) (y : E) (m : ℕ)

/-- Evaluation of the non-leader variables of a relation of order `m`: jets below `m` are
substituted, higher jets are irrelevant and are sent to zero. -/
def jetCoeffEval : MvPolynomial {j : Unit × ℕ // j ≠ ((), m)} B →+* E :=
  (MvPolynomial.aeval fun j : {j : Unit × ℕ // j ≠ ((), m)} =>
      if (j : Unit × ℕ).2 < m then differentialJet (j : Unit × ℕ).2 y else 0).toRingHom

theorem jetCoeffEval_apply (c : MvPolynomial {j : Unit × ℕ // j ≠ ((), m)} B) :
    jetCoeffEval B y m c =
      MvPolynomial.aeval (fun j : {j : Unit × ℕ // j ≠ ((), m)} =>
        if (j : Unit × ℕ).2 < m then differentialJet (j : Unit × ℕ).2 y else 0) c := rfl

/-- Coefficient evaluation lands in the jet prefix field. -/
theorem jetCoeffEval_mem (c : MvPolynomial {j : Unit × ℕ // j ≠ ((), m)} B) :
    jetCoeffEval B y m c ∈ jetAdjoin B y m := by
  classical
  set g : {j : Unit × ℕ // j ≠ ((), m)} → E := fun j =>
    if (j : Unit × ℕ).2 < m then differentialJet (j : Unit × ℕ).2 y else 0 with hg
  have hrange : Set.range g ⊆ (jetAdjoinOver B y m : Set E) := by
    rintro x ⟨j, rfl⟩
    rw [SetLike.mem_coe]
    by_cases hjm : (j : Unit × ℕ).2 < m
    · rw [hg]
      simp only [if_pos hjm]
      exact differentialJet_mem_jetAdjoinOver B y hjm
    · rw [hg]
      simp only [if_neg hjm]
      exact (jetAdjoinOver B y m).zero_mem
  have hle : Algebra.adjoin B (Set.range g) ≤ (jetAdjoinOver B y m).toSubalgebra :=
    Algebra.adjoin_le hrange
  refine hle ?_
  rw [Algebra.adjoin_range_eq_range_aeval]
  exact ⟨c, rfl⟩

/-- Coefficient evaluation, corestricted to the jet prefix field. -/
def jetCoeffHom : MvPolynomial {j : Unit × ℕ // j ≠ ((), m)} B →+* jetAdjoin B y m :=
  RingHom.codRestrict (jetCoeffEval B y m) (jetAdjoin B y m) (jetCoeffEval_mem B y m)

@[simp]
theorem algebraMap_jetCoeffHom (c : MvPolynomial {j : Unit × ℕ // j ≠ ((), m)} B) :
    (algebraMap (jetAdjoin B y m) E) (jetCoeffHom B y m c) = jetCoeffEval B y m c := rfl

/-- The univariate polynomial over the jet prefix field attached to a scalar differential
polynomial: single out the top jet and evaluate the remaining variables. -/
def jetPrefixPolynomial (Q : DifferentialPolynomial Unit B) :
    Polynomial (jetAdjoin B y m) :=
  Polynomial.map (jetCoeffHom B y m) (mvPolynomialPolynomialEquivAt ((), m) Q)

/-- The composite ring map on differential polynomials: single out the top jet, evaluate the other
variables at the low jets, then substitute the top jet. -/
theorem eval₂_equivAt_eq_eval₂Hom (Q : DifferentialPolynomial Unit B) :
    Polynomial.eval₂ (jetCoeffEval B y m) (differentialJet m y)
        (mvPolynomialPolynomialEquivAt ((), m) Q) =
      MvPolynomial.eval₂Hom (algebraMap B E)
        (fun q : Unit × ℕ => if q.2 < m then differentialJet q.2 y else
          if q = ((), m) then differentialJet m y else 0) Q := by
  classical
  set g : Unit × ℕ → E := fun q => if q.2 < m then differentialJet q.2 y else
    if q = ((), m) then differentialJet m y else 0 with hg
  have hext : ((Polynomial.eval₂RingHom (jetCoeffEval B y m) (differentialJet m y)).comp
      ((mvPolynomialPolynomialEquivAt (K := B) ((), m)) :
        MvPolynomial (Unit × ℕ) B ≃ₐ[B] _).toAlgHom.toRingHom) =
      MvPolynomial.eval₂Hom (algebraMap B E) g := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro r
      show Polynomial.eval₂ (jetCoeffEval B y m) (differentialJet m y)
          (mvPolynomialPolynomialEquivAt ((), m) (MvPolynomial.C r)) =
        MvPolynomial.eval₂Hom (algebraMap B E) g (MvPolynomial.C r)
      have hC : (mvPolynomialPolynomialEquivAt (K := B) ((), m)) (MvPolynomial.C r)
          = Polynomial.C (MvPolynomial.C r) := by
        simpa using (mvPolynomialPolynomialEquivAt (K := B) ((), m)).commutes r
      rw [hC, Polynomial.eval₂_C, MvPolynomial.eval₂Hom_C, jetCoeffEval_apply,
        MvPolynomial.aeval_C]
    · intro q
      show Polynomial.eval₂ (jetCoeffEval B y m) (differentialJet m y)
          (mvPolynomialPolynomialEquivAt ((), m) (MvPolynomial.X q)) =
        MvPolynomial.eval₂Hom (algebraMap B E) g (MvPolynomial.X q)
      rw [MvPolynomial.eval₂Hom_X']
      by_cases hq : q = ((), m)
      · subst hq
        rw [mvPolynomialPolynomialEquivAt_X_self, Polynomial.eval₂_X]
        simp only [hg]
        simp
      · rw [mvPolynomialPolynomialEquivAt_X_ne hq, Polynomial.eval₂_C, jetCoeffEval_apply,
          MvPolynomial.aeval_X]
        simp only [hg]
        by_cases hq2 : q.2 < m
        · simp only [if_pos hq2]
        · simp only [if_neg hq2, if_neg hq]
  exact congrArg (fun f : MvPolynomial (Unit × ℕ) B →+* E => f Q) hext

/-- **The attached univariate polynomial computes the relation.**  For a differential polynomial
whose variables all have order at most `m`, substituting the top jet into the attached univariate
polynomial reproduces the evaluation of the relation. -/
theorem aeval_jetPrefixPolynomial {Q : DifferentialPolynomial Unit B}
    (hQ : ∀ q ∈ Q.vars, q.2 ≤ m) :
    Polynomial.aeval (differentialJet m y) (jetPrefixPolynomial B y m Q) =
      differentialPolynomialEvalOver (K := B) (fun _ : Unit ↦ y) Q := by
  classical
  rw [jetPrefixPolynomial, Polynomial.aeval_def, Polynomial.eval₂_map]
  have hcomp : (algebraMap (jetAdjoin B y m) E).comp (jetCoeffHom B y m) =
      jetCoeffEval B y m := rfl
  rw [hcomp, eval₂_equivAt_eq_eval₂Hom]
  simp only [MvPolynomial.coe_eval₂Hom, ← MvPolynomial.aeval_def]
  refine MvPolynomial.aeval_congr_of_vars ?_
  intro q hq
  rcases lt_or_eq_of_le (hQ q hq) with hlt | heq
  · simp only [if_pos hlt]
  · have hqeq : q = ((), m) := Prod.ext (Subsingleton.elim _ _) heq
    subst hqeq
    simp


/-- The degree of the attached polynomial is bounded by the degree in the top jet. -/
theorem natDegree_jetPrefixPolynomial_le (Q : DifferentialPolynomial Unit B) :
    (jetPrefixPolynomial B y m Q).natDegree ≤ MvPolynomial.degreeOf ((), m) Q := by
  rw [mvPolynomial_degreeOf_eq_natDegree_asPolynomialAt, jetPrefixPolynomial,
    mvPolynomialPolynomialEquivAt_apply]
  exact Polynomial.natDegree_map_le

/-- **The leading coefficient of the attached polynomial is the evaluated initial.** -/
theorem jetCoeffEval_leadingCoeff {Q : DifferentialPolynomial Unit B}
    (hQ : ∀ q ∈ Q.vars, q.2 ≤ m) :
    jetCoeffEval B y m (mvPolynomialAsPolynomialAt ((), m) Q).leadingCoeff =
      differentialPolynomialEvalOver (K := B) (fun _ : Unit ↦ y)
        (mvPolynomialInitialAt ((), m) Q) := by
  classical
  have h := eval₂_equivAt_eq_eval₂Hom B y m (mvPolynomialInitialAt ((), m) Q)
  rw [mvPolynomialPolynomialEquivAt_initial, Polynomial.eval₂_C] at h
  rw [h]
  simp only [MvPolynomial.coe_eval₂Hom, ← MvPolynomial.aeval_def]
  refine MvPolynomial.aeval_congr_of_vars ?_
  intro q hq
  rcases lt_or_eq_of_le (hQ q (mvPolynomialInitialAt_vars_subset ((), m) Q hq)) with hlt | heq
  · simp only [if_pos hlt]
  · have hqeq : q = ((), m) := Prod.ext (Subsingleton.elim _ _) heq
    subst hqeq
    simp

/-- If the initial does not vanish at the element, the attached polynomial has exactly the degree
in the top jet, and in particular is nonzero. -/
theorem natDegree_jetPrefixPolynomial {Q : DifferentialPolynomial Unit B}
    (hQ : ∀ q ∈ Q.vars, q.2 ≤ m)
    (hinit : differentialPolynomialEvalOver (K := B) (fun _ : Unit ↦ y)
      (mvPolynomialInitialAt ((), m) Q) ≠ 0) :
    (jetPrefixPolynomial B y m Q).natDegree = MvPolynomial.degreeOf ((), m) Q := by
  classical
  have hlead : jetCoeffHom B y m (mvPolynomialAsPolynomialAt ((), m) Q).leadingCoeff ≠ 0 := by
    intro h
    apply hinit
    rw [← jetCoeffEval_leadingCoeff B y m hQ, ← algebraMap_jetCoeffHom B y m, h, map_zero]
  rw [mvPolynomial_degreeOf_eq_natDegree_asPolynomialAt, jetPrefixPolynomial,
    mvPolynomialPolynomialEquivAt_apply]
  exact Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hlead

theorem jetPrefixPolynomial_ne_zero {Q : DifferentialPolynomial Unit B}
    (hQ : ∀ q ∈ Q.vars, q.2 ≤ m)
    (hinit : differentialPolynomialEvalOver (K := B) (fun _ : Unit ↦ y)
      (mvPolynomialInitialAt ((), m) Q) ≠ 0) :
    jetPrefixPolynomial B y m Q ≠ 0 := by
  intro h
  apply hinit
  rw [← jetCoeffEval_leadingCoeff B y m hQ, ← algebraMap_jetCoeffHom B y m]
  have : jetCoeffHom B y m (mvPolynomialAsPolynomialAt ((), m) Q).leadingCoeff = 0 := by
    have hcoeff : (jetPrefixPolynomial B y m Q).coeff
        (mvPolynomialAsPolynomialAt ((), m) Q).natDegree = 0 := by
      rw [h]
      simp
    rwa [jetPrefixPolynomial, mvPolynomialPolynomialEquivAt_apply, Polynomial.coeff_map] at hcoeff
  rw [this, map_zero]

end

section

variable {B : IntermediateField F E} {y : E} {P : DifferentialPolynomial Unit B}

omit [Differential E] in
/-- The variables of a scalar differential polynomial have order at most its order. -/
theorem scalarDifferentialPolynomial_vars_le :
    ∀ q ∈ P.vars, q.2 ≤ scalarDifferentialPolynomialOrder P :=
  fun _ hq => scalarDifferentialPolynomial_var_order_le hq

/-- **The characteristic gives a univariate relation of the top jet over the jet prefix field.** -/
theorem aeval_jetPrefixPolynomial_characteristic
    (hP : P ∈ differentialIntermediateRelationIdeal B y) :
    Polynomial.aeval (differentialJet (scalarDifferentialPolynomialOrder P) y)
      (jetPrefixPolynomial B y (scalarDifferentialPolynomialOrder P) P) = 0 := by
  rw [aeval_jetPrefixPolynomial B y _ scalarDifferentialPolynomial_vars_le]
  exact hP

/-- The top jet is algebraic over the jet prefix field. -/
theorem isIntegral_differentialJet_of_minimal
    (hmin : IsMinimalScalarDifferentialPolynomialRank
      (differentialIntermediateRelationIdeal B y : Set _) P) :
    IsIntegral (jetAdjoin B y (scalarDifferentialPolynomialOrder P))
      (differentialJet (scalarDifferentialPolynomialOrder P) y) := by
  have hinit : differentialPolynomialEvalOver (K := B) (fun _ : Unit ↦ y)
      (mvPolynomialInitialAt ((), scalarDifferentialPolynomialOrder P) P) ≠ 0 := by
    intro h
    exact hmin.initial_not_mem (differentialIntermediateRelationIdeal_ne_top B y)
      ((mem_differentialIntermediateRelationIdeal_iff B y _).2 h)
  refine (IsAlgebraic.isIntegral ?_)
  exact ⟨jetPrefixPolynomial B y _ P,
    jetPrefixPolynomial_ne_zero B y _ scalarDifferentialPolynomial_vars_le hinit,
    aeval_jetPrefixPolynomial_characteristic hmin.1⟩

/-- **Upper bound for Ritt's degree equality.**  The minimal polynomial of the top jet over the jet
prefix field has degree at most the leader degree of the characteristic. -/
theorem minpoly_natDegree_le_leaderDegree
    (hmin : IsMinimalScalarDifferentialPolynomialRank
      (differentialIntermediateRelationIdeal B y : Set _) P) :
    (minpoly (jetAdjoin B y (scalarDifferentialPolynomialOrder P))
        (differentialJet (scalarDifferentialPolynomialOrder P) y)).natDegree ≤
      scalarDifferentialPolynomialLeaderDegree P := by
  have hinit : differentialPolynomialEvalOver (K := B) (fun _ : Unit ↦ y)
      (mvPolynomialInitialAt ((), scalarDifferentialPolynomialOrder P) P) ≠ 0 := by
    intro h
    exact hmin.initial_not_mem (differentialIntermediateRelationIdeal_ne_top B y)
      ((mem_differentialIntermediateRelationIdeal_iff B y _).2 h)
  have hne := jetPrefixPolynomial_ne_zero B y _ scalarDifferentialPolynomial_vars_le hinit
  have hdvd := minpoly.dvd (jetAdjoin B y (scalarDifferentialPolynomialOrder P))
    (differentialJet (scalarDifferentialPolynomialOrder P) y)
    (aeval_jetPrefixPolynomial_characteristic hmin.1)
  refine (Polynomial.natDegree_le_of_dvd hdvd hne).trans ?_
  rw [natDegree_jetPrefixPolynomial B y _ scalarDifferentialPolynomial_vars_le hinit]
  exact le_of_eq rfl

end

end

end GaloisForLFunctions
