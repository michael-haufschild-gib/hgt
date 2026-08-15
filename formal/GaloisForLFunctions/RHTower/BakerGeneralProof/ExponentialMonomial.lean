import GaloisForLFunctions.RHTower.BakerGeneralProof.IteratedAnalyticTransport

/-!
# Diagonal component action on exponential monomials for Baker's theorem

The exponential subalgebra of the auxiliary polynomial ring is invariant under every solved
component operator.  More precisely, each monomial in its exponential variables is a simultaneous
eigenvector.  The eigenvalues are algebraic integers after the already-available common component
scale.  This is the algebraic interface used to turn component jets into a Siegel matrix.
-/

open scoped Classical

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

/-- A bounded exponent vector for the exponential variables of an auxiliary polynomial. -/
abbrev SolvedRelation.ExponentialColumn (R : SolvedRelation) (L : ℕ) :=
  Fin R.n → Fin L

/-- An exponential monomial, with no additive-variable factor. -/
noncomputable def SolvedRelation.exponentialMonomial
    (R : SolvedRelation) {L : ℕ} (m : R.ExponentialColumn L) :
    MvPolynomial R.Variable R.CoefficientField :=
  ∏ i, MvPolynomial.X (some i) ^ (m i : ℕ)

/-- The coefficient by which a component differentiates one exponential generator. -/
noncomputable def SolvedRelation.componentEigenCoordinate
    (R : SolvedRelation) (c : ℤ) (d : R.Direction) (i : Fin R.n) :
    R.CoefficientField :=
  match d with
  | none => if i = R.pivot then R.scaledComponentCoeff c none else 0
  | some j =>
      (if i = j then R.integerScalar c else 0) +
        if i = R.pivot then R.scaledComponentCoeff c (some j) else 0

@[simp] theorem SolvedRelation.componentVector_exponential
    (R : SolvedRelation) (c : ℤ) (d : R.Direction) (i : Fin R.n) :
    R.componentVector c d (some i) =
      MvPolynomial.C (R.componentEigenCoordinate c d i) * MvPolynomial.X (some i) := by
  cases d <;>
    simp [SolvedRelation.componentVector, SolvedRelation.componentEigenCoordinate] <;>
    split_ifs <;>
    simp [add_mul]

/-- A finite-support exponential monomial, useful for the induction proving diagonal action. -/
noncomputable def SolvedRelation.exponentialMonomialOn
    (R : SolvedRelation) {L : ℕ} (s : Finset (Fin R.n)) (m : R.ExponentialColumn L) :
    MvPolynomial R.Variable R.CoefficientField :=
  ∏ i ∈ s, MvPolynomial.X (some i) ^ (m i : ℕ)

/-- Eigenvalue of a component on a finite-support exponential monomial. -/
noncomputable def SolvedRelation.componentEigenvalueOn
    (R : SolvedRelation) (c : ℤ) (d : R.Direction) {L : ℕ}
    (s : Finset (Fin R.n)) (m : R.ExponentialColumn L) : R.CoefficientField :=
  ∑ i ∈ s, (m i : R.CoefficientField) * R.componentEigenCoordinate c d i

private theorem diagonal_X_pow
    {K σ ι : Type*} [CommSemiring K]
    (D : Derivation K (MvPolynomial σ K) (MvPolynomial σ K))
    (x : ι → σ) (w : ι → K)
    (hX : ∀ i, D (MvPolynomial.X (x i)) =
      MvPolynomial.C (w i) * MvPolynomial.X (x i))
    (i : ι) (e : ℕ) :
    D (MvPolynomial.X (x i) ^ e) =
      MvPolynomial.C ((e : K) * w i) * MvPolynomial.X (x i) ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
      rw [pow_succ, D.leibniz, ih, hX i]
      simp only [smul_eq_mul, Nat.cast_succ, add_mul,
        MvPolynomial.C_add, MvPolynomial.C_mul, one_mul]
      ac_rfl

private theorem diagonal_finset_prod_X_pow
    {K σ ι : Type*} [CommSemiring K]
    (D : Derivation K (MvPolynomial σ K) (MvPolynomial σ K))
    (x : ι → σ) (w : ι → K)
    (hX : ∀ i, D (MvPolynomial.X (x i)) =
      MvPolynomial.C (w i) * MvPolynomial.X (x i))
    (m : ι → ℕ) (s : Finset ι) :
    D (∏ i ∈ s, MvPolynomial.X (x i) ^ m i) =
      MvPolynomial.C (∑ i ∈ s, (m i : K) * w i) *
        ∏ i ∈ s, MvPolynomial.X (x i) ^ m i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
      simp only [Finset.prod_insert his, Finset.sum_insert his]
      rw [D.leibniz, diagonal_X_pow D x w hX i (m i), ih]
      simp only [smul_eq_mul, MvPolynomial.C_add, add_mul]
      ring

/-- A component acts diagonally on every finite-support exponential monomial. -/
theorem SolvedRelation.componentDerivation_exponentialMonomialOn
    (R : SolvedRelation) (c : ℤ) (d : R.Direction) {L : ℕ}
    (s : Finset (Fin R.n)) (m : R.ExponentialColumn L) :
    R.componentDerivation c d (R.exponentialMonomialOn s m) =
      MvPolynomial.C (R.componentEigenvalueOn c d s m) * R.exponentialMonomialOn s m := by
  apply diagonal_finset_prod_X_pow (R.componentDerivation c d)
    (fun i => some i) (R.componentEigenCoordinate c d)
  intro i
  rw [R.componentDerivation_X, R.componentVector_exponential]

/-- Eigenvalue of a component on a full exponential monomial. -/
noncomputable def SolvedRelation.componentEigenvalue
    (R : SolvedRelation) (c : ℤ) (d : R.Direction) {L : ℕ}
    (m : R.ExponentialColumn L) : R.CoefficientField :=
  R.componentEigenvalueOn c d Finset.univ m

theorem SolvedRelation.exponentialMonomial_eq_on_univ
    (R : SolvedRelation) {L : ℕ} (m : R.ExponentialColumn L) :
    R.exponentialMonomial m = R.exponentialMonomialOn Finset.univ m := rfl

/-- A component acts diagonally on every full exponential monomial. -/
theorem SolvedRelation.componentDerivation_exponentialMonomial
    (R : SolvedRelation) (c : ℤ) (d : R.Direction) {L : ℕ}
    (m : R.ExponentialColumn L) :
    R.componentDerivation c d (R.exponentialMonomial m) =
      MvPolynomial.C (R.componentEigenvalue c d m) * R.exponentialMonomial m := by
  exact R.componentDerivation_exponentialMonomialOn c d Finset.univ m

/-- Component eigen-coordinates are integral when the scaled solved coefficients are integral. -/
theorem SolvedRelation.componentEigenCoordinate_isIntegral
    (R : SolvedRelation) (c : ℤ) (hint : ∀ d, IsIntegral ℤ (R.scaledComponentCoeff c d))
    (d : R.Direction) (i : Fin R.n) :
    IsIntegral ℤ (R.componentEigenCoordinate c d i) := by
  rcases d with _ | j
  · by_cases hi : i = R.pivot
    · subst i
      simpa [SolvedRelation.componentEigenCoordinate] using hint none
    · rw [SolvedRelation.componentEigenCoordinate, if_neg hi]
      exact isIntegral_zero
  · by_cases hij : i = j
    · subst i
      rw [SolvedRelation.componentEigenCoordinate, if_pos rfl,
        if_neg j.property, add_zero]
      change IsIntegral ℤ (c • (1 : R.CoefficientField))
      exact isIntegral_one.zsmul c
    · by_cases hip : i = R.pivot
      · subst i
        simpa [SolvedRelation.componentEigenCoordinate, hij] using hint (some j)
      · rw [SolvedRelation.componentEigenCoordinate, if_neg hij, if_neg hip]
        simpa using (isIntegral_zero : IsIntegral ℤ (0 : R.CoefficientField))

/-- Component eigenvalues are integral when the scaled solved coefficients are integral. -/
theorem SolvedRelation.componentEigenvalueOn_isIntegral
    (R : SolvedRelation) (c : ℤ) (hint : ∀ d, IsIntegral ℤ (R.scaledComponentCoeff c d))
    (d : R.Direction) {L : ℕ} (s : Finset (Fin R.n)) (m : R.ExponentialColumn L) :
    IsIntegral ℤ (R.componentEigenvalueOn c d s m) := by
  unfold SolvedRelation.componentEigenvalueOn
  apply IsIntegral.sum
  intro i _
  have hm : IsIntegral ℤ ((m i : ℕ) • (1 : R.CoefficientField)) :=
    isIntegral_one.nsmul (m i)
  simpa using hm.mul (R.componentEigenCoordinate_isIntegral c hint d i)

/-- Full component eigenvalues are integral under the common component scale. -/
theorem SolvedRelation.componentEigenvalue_isIntegral
    (R : SolvedRelation) (c : ℤ) (hint : ∀ d, IsIntegral ℤ (R.scaledComponentCoeff c d))
    (d : R.Direction) {L : ℕ} (m : R.ExponentialColumn L) :
    IsIntegral ℤ (R.componentEigenvalue c d m) :=
  R.componentEigenvalueOn_isIntegral c hint d Finset.univ m

end GaloisForLFunctions.RHTower.BakerGeneralProof
