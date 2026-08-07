/-
The pseudo-reduction certificate needs neither a field nor the univariate transport.

Three pseudo-division layers coexist in the tree.

* `mvPolynomialPseudoReductionAt` builds an `MvPolynomialPseudoReductionAt` certificate over a
  **field**, by transporting the univariate construction through
  `mvPolynomialPolynomialEquivAt`.
* `supportedMvPolynomialPseudoReductionAt` builds the stronger, support-recording
  `SupportedMvPolynomialPseudoReductionAt` certificate, still over a **field**, by recursing inside
  the multivariable ring.
* `supportedMvPolynomialPseudoReductionAtOfCommRing` builds the *same* stronger certificate over an
  arbitrary **commutative ring**.

So the third construction already subsumes the other two: forgetting its support bounds gives the
first certificate, and its hypotheses are strictly weaker.  This file records the forgetful map and
the resulting field-free, transport-free constructions, and upgrades the existence statement
`exists_mvPolynomial_pseudoDivision` with the support bounds it was missing.

Nothing is reproved: every declaration below is the existing commutative-ring construction with a
premise dropped or a field forgotten.
-/
import GaloisForLFunctions.HTGeometry.PseudoDivisionCommRing

namespace GaloisForLFunctions

noncomputable section

/-- **Forgetting the support bounds.**  A support-recording pseudo-reduction certificate is in
particular a pseudo-reduction certificate. -/
def SupportedMvPolynomialPseudoReductionAt.toMvPolynomialPseudoReductionAt
    {K σ : Type*} [CommRing K] [DecidableEq σ] {i : σ} {Q D : MvPolynomial σ K}
    (d : SupportedMvPolynomialPseudoReductionAt i Q D) :
    MvPolynomialPseudoReductionAt i Q D where
  exponent := d.exponent
  quotient := d.quotient
  remainder := d.remainder
  eq_mul_add := d.eq_mul_add
  remainder_degree_lt := d.remainder_degree_lt

@[simp] theorem SupportedMvPolynomialPseudoReductionAt.exponent_toMvPolynomialPseudoReductionAt
    {K σ : Type*} [CommRing K] [DecidableEq σ] {i : σ} {Q D : MvPolynomial σ K}
    (d : SupportedMvPolynomialPseudoReductionAt i Q D) :
    d.toMvPolynomialPseudoReductionAt.exponent = d.exponent := rfl

@[simp] theorem SupportedMvPolynomialPseudoReductionAt.quotient_toMvPolynomialPseudoReductionAt
    {K σ : Type*} [CommRing K] [DecidableEq σ] {i : σ} {Q D : MvPolynomial σ K}
    (d : SupportedMvPolynomialPseudoReductionAt i Q D) :
    d.toMvPolynomialPseudoReductionAt.quotient = d.quotient := rfl

@[simp] theorem SupportedMvPolynomialPseudoReductionAt.remainder_toMvPolynomialPseudoReductionAt
    {K σ : Type*} [CommRing K] [DecidableEq σ] {i : σ} {Q D : MvPolynomial σ K}
    (d : SupportedMvPolynomialPseudoReductionAt i Q D) :
    d.toMvPolynomialPseudoReductionAt.remainder = d.remainder := rfl

/-- **The pseudo-reduction certificate over a commutative ring.**  The field hypothesis of
`mvPolynomialPseudoReductionAt` and its passage through the univariate equivalence are both
unnecessary: the support-preserving multivariable recursion already produces the certificate over
any commutative ring, and the decidable-equality instance it uses is supplied classically. -/
def mvPolynomialPseudoReductionAtOfCommRing
    {K σ : Type*} [CommRing K] (i : σ) (Q D : MvPolynomial σ K)
    (hDdegree : MvPolynomial.degreeOf i D ≠ 0) :
    MvPolynomialPseudoReductionAt i Q D := by
  classical
  exact (supportedMvPolynomialPseudoReductionAtOfCommRing i Q D
    hDdegree).toMvPolynomialPseudoReductionAt

/-- **The support-recording certificate over a commutative ring, as an inhabitation statement.** -/
theorem nonempty_supportedMvPolynomialPseudoReductionAt_of_commRing
    {K σ : Type*} [CommRing K] [DecidableEq σ] (i : σ) (Q D : MvPolynomial σ K)
    (hDdegree : MvPolynomial.degreeOf i D ≠ 0) :
    Nonempty (SupportedMvPolynomialPseudoReductionAt i Q D) :=
  ⟨supportedMvPolynomialPseudoReductionAtOfCommRing i Q D hDdegree⟩

/-- **Pseudo-division at a distinguished variable over a commutative ring, with support control.**
This is `exists_mvPolynomial_pseudoDivision` with the two variable bounds the transported proof
could not supply: neither the quotient nor the remainder introduces a variable absent from the
dividend and the divisor. -/
theorem exists_mvPolynomial_pseudoDivision_vars_subset
    {R σ : Type*} [CommRing R] [DecidableEq σ] (i : σ)
    (Q D : MvPolynomial σ R) (hD : 0 < MvPolynomial.degreeOf i D) :
    ∃ (e : ℕ) (a b : MvPolynomial σ R),
      mvPolynomialInitialAt i D ^ e * Q = D * a + b ∧
        MvPolynomial.degreeOf i b < MvPolynomial.degreeOf i D ∧
        a.vars ⊆ Q.vars ∪ D.vars ∧ b.vars ⊆ Q.vars ∪ D.vars := by
  obtain ⟨d⟩ :=
    nonempty_supportedMvPolynomialPseudoReductionAt_of_commRing i Q D (by omega)
  exact ⟨d.exponent, d.quotient, d.remainder, d.eq_mul_add, d.remainder_degree_lt,
    d.quotient_vars_subset, d.remainder_vars_subset⟩

end

end GaloisForLFunctions
