import GaloisForLFunctions.HTGeometry.TwoBlockInitialSeparant

/-!
# Coefficients of a split two-block polynomial

Reading a two-block polynomial as a polynomial in the right block over the ring of the left block
splits each monomial into its two halves.  Consequently the coefficient of a right-block monomial has
its own coefficients among those of the original polynomial, and therefore involves no left-block jet
beyond those of the polynomial and no higher degree in any of them.

These bounds are what allows a coefficient of the cleared characteristic to be used as a generator:
the single-generator criterion needs a numerator and a denominator of order and leader degree bounded
by the characteristic's.
-/

namespace GaloisForLFunctions

noncomputable section

variable {F : Type*} [CommRing F]

/-- Assemble a two-block jet monomial from a left-block and a right-block monomial. -/
def twoBlockMonomial (νL νR : (Unit × ℕ) →₀ ℕ) : ((Unit ⊕ Unit) × ℕ) →₀ ℕ :=
  νL.mapDomain (fun p : Unit × ℕ ↦ ((Sum.inl p.1 : Unit ⊕ Unit), p.2)) +
    νR.mapDomain (fun p : Unit × ℕ ↦ ((Sum.inr p.1 : Unit ⊕ Unit), p.2))

theorem twoBlockMonomial_apply_inl (νL νR : (Unit × ℕ) →₀ ℕ) (u : Unit) (k : ℕ) :
    twoBlockMonomial νL νR ((Sum.inl u : Unit ⊕ Unit), k) = νL (u, k) := by
  classical
  have hinjL : Function.Injective
      (fun p : Unit × ℕ ↦ ((Sum.inl p.1 : Unit ⊕ Unit), p.2)) := by
    rintro ⟨a, i⟩ ⟨b, j⟩ h
    simpa using h
  have hL : (νL.mapDomain (fun p : Unit × ℕ ↦ ((Sum.inl p.1 : Unit ⊕ Unit), p.2)))
      ((Sum.inl u : Unit ⊕ Unit), k) = νL (u, k) := by
    have := Finsupp.mapDomain_apply hinjL νL (u, k)
    simpa using this
  have hR : (νR.mapDomain (fun p : Unit × ℕ ↦ ((Sum.inr p.1 : Unit ⊕ Unit), p.2)))
      ((Sum.inl u : Unit ⊕ Unit), k) = 0 := by
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨⟨b, j⟩, hb⟩
    simp at hb
  simp [twoBlockMonomial, hL, hR]

theorem twoBlockMonomial_apply_inr (νL νR : (Unit × ℕ) →₀ ℕ) (u : Unit) (k : ℕ) :
    twoBlockMonomial νL νR ((Sum.inr u : Unit ⊕ Unit), k) = νR (u, k) := by
  classical
  have hinjR : Function.Injective
      (fun p : Unit × ℕ ↦ ((Sum.inr p.1 : Unit ⊕ Unit), p.2)) := by
    rintro ⟨a, i⟩ ⟨b, j⟩ h
    simpa using h
  have hR : (νR.mapDomain (fun p : Unit × ℕ ↦ ((Sum.inr p.1 : Unit ⊕ Unit), p.2)))
      ((Sum.inr u : Unit ⊕ Unit), k) = νR (u, k) := by
    have := Finsupp.mapDomain_apply hinjR νR (u, k)
    simpa using this
  have hL : (νL.mapDomain (fun p : Unit × ℕ ↦ ((Sum.inl p.1 : Unit ⊕ Unit), p.2)))
      ((Sum.inr u : Unit ⊕ Unit), k) = 0 := by
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨⟨b, j⟩, hb⟩
    simp at hb
  simp [twoBlockMonomial, hL, hR]

/-- **The two-block splitting on monomials.** -/
theorem differentialPolynomialTwoBlockEquiv_monomial (νL νR : (Unit × ℕ) →₀ ℕ) (a : F) :
    differentialPolynomialTwoBlockEquiv F
        (MvPolynomial.monomial (twoBlockMonomial νL νR) a) =
      MvPolynomial.monomial νR (MvPolynomial.monomial νL a) := by
  classical
  have hsplit : (MvPolynomial.monomial (twoBlockMonomial νL νR) a :
        DifferentialPolynomial (Unit ⊕ Unit) F) =
      differentialPolynomialLeft (κ := Unit) (MvPolynomial.monomial νL a) *
        differentialPolynomialRight (ι := Unit) (MvPolynomial.monomial νR 1) := by
    rw [differentialPolynomialLeft, differentialPolynomialRight,
      MvPolynomial.rename_monomial, MvPolynomial.rename_monomial,
      MvPolynomial.monomial_mul, mul_one]
    rfl
  rw [hsplit, map_mul, differentialPolynomialTwoBlockEquiv_left,
    differentialPolynomialTwoBlockEquiv_right, MvPolynomial.map_monomial, map_one,
    MvPolynomial.C_mul_monomial, mul_one]

/-- Split a two-block jet monomial into its two halves. -/
theorem exists_twoBlockMonomial (ν : ((Unit ⊕ Unit) × ℕ) →₀ ℕ) :
    ∃ νL νR : (Unit × ℕ) →₀ ℕ, ν = twoBlockMonomial νL νR := by
  classical
  refine ⟨ν.comapDomain (fun p : Unit × ℕ ↦ ((Sum.inl p.1 : Unit ⊕ Unit), p.2))
      (by rintro ⟨a, i⟩ _ ⟨b, j⟩ _ h; simpa using h),
    ν.comapDomain (fun p : Unit × ℕ ↦ ((Sum.inr p.1 : Unit ⊕ Unit), p.2))
      (by rintro ⟨a, i⟩ _ ⟨b, j⟩ _ h; simpa using h), ?_⟩
  refine Finsupp.ext ?_
  rintro ⟨u, k⟩
  cases u with
  | inl u =>
      obtain rfl : u = () := Subsingleton.elim _ _
      rw [twoBlockMonomial_apply_inl]
      simp [Finsupp.comapDomain_apply]
  | inr u =>
      obtain rfl : u = () := Subsingleton.elim _ _
      rw [twoBlockMonomial_apply_inr]
      simp [Finsupp.comapDomain_apply]

/-- **The double coefficient formula.**  The coefficient of a left-block monomial in the coefficient
of a right-block monomial is the coefficient of the assembled two-block monomial. -/
theorem coeff_coeff_twoBlockEquiv (X : DifferentialPolynomial (Unit ⊕ Unit) F)
    (νL νR : (Unit × ℕ) →₀ ℕ) :
    MvPolynomial.coeff νL (MvPolynomial.coeff νR
        (differentialPolynomialTwoBlockEquiv F X)) =
      MvPolynomial.coeff (twoBlockMonomial νL νR) X := by
  classical
  induction X using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial ν a =>
      obtain ⟨μL, μR, rfl⟩ := exists_twoBlockMonomial ν
      rw [differentialPolynomialTwoBlockEquiv_monomial, MvPolynomial.coeff_monomial,
        MvPolynomial.coeff_monomial]
      by_cases hR : νR = μR
      · subst hR
        rw [if_pos rfl, MvPolynomial.coeff_monomial]
        by_cases hL : νL = μL
        · subst hL
          rw [if_pos rfl, if_pos rfl]
        · rw [if_neg (Ne.symm hL)]
          refine (if_neg ?_).symm
          intro heq
          exact hL (by
            refine Finsupp.ext ?_
            rintro ⟨u, k⟩
            obtain rfl : u = () := Subsingleton.elim _ _
            have := congrArg (fun s => s ((Sum.inl () : Unit ⊕ Unit), k)) heq
            rw [twoBlockMonomial_apply_inl, twoBlockMonomial_apply_inl] at this
            exact this.symm)
      · rw [if_neg (Ne.symm hR), MvPolynomial.coeff_zero]
        refine (if_neg ?_).symm
        intro heq
        exact hR (by
          refine Finsupp.ext ?_
          rintro ⟨u, k⟩
          obtain rfl : u = () := Subsingleton.elim _ _
          have := congrArg (fun s => s ((Sum.inr () : Unit ⊕ Unit), k)) heq
          rw [twoBlockMonomial_apply_inr, twoBlockMonomial_apply_inr] at this
          exact this.symm)

/-- **A coefficient of the split polynomial has no larger jet degree than the polynomial.** -/
theorem degreeOf_twoBlockCoefficient_le (X : DifferentialPolynomial (Unit ⊕ Unit) F)
    (νR : (Unit × ℕ) →₀ ℕ) (k : ℕ) :
    MvPolynomial.degreeOf (((), k) : Unit × ℕ)
        (differentialPolynomialTwoBlockCoefficient νR X) ≤
      MvPolynomial.degreeOf ((Sum.inl () : Unit ⊕ Unit), k) X := by
  classical
  refine MvPolynomial.degreeOf_le_iff.2 ?_
  intro νL hνL
  have hne : MvPolynomial.coeff (twoBlockMonomial νL νR) X ≠ 0 := by
    rw [← coeff_coeff_twoBlockEquiv]
    exact MvPolynomial.mem_support_iff.mp hνL
  have hmem : twoBlockMonomial νL νR ∈ X.support := MvPolynomial.mem_support_iff.mpr hne
  have hval : twoBlockMonomial νL νR ((Sum.inl () : Unit ⊕ Unit), k) = νL ((), k) :=
    twoBlockMonomial_apply_inl νL νR () k
  calc νL ((), k) = twoBlockMonomial νL νR ((Sum.inl () : Unit ⊕ Unit), k) := hval.symm
    _ ≤ MvPolynomial.degreeOf ((Sum.inl () : Unit ⊕ Unit), k) X := by
        rw [MvPolynomial.degreeOf_eq_sup]
        exact Finset.le_sup (f := fun d : ((Unit ⊕ Unit) × ℕ) →₀ ℕ ↦
          d ((Sum.inl () : Unit ⊕ Unit), k)) hmem

end

end GaloisForLFunctions
