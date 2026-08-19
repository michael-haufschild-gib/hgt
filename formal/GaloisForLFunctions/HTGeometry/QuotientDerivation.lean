import GaloisForLFunctions.HTGeometry.ParameterizedDifferenceGalois

/-!
# A derivation descends to the quotient by a differential ideal

The parameterized theory needs the quotient of a `σ`-`δ` ring by an ideal stable under both
operators to be a `σ`-`δ` ring again.  The difference operator descends because the ideal is a
`σ`-ideal; this file supplies the other half, which mathlib does not have: a derivation of a
commutative ring descends to the quotient by any ideal it preserves.

The construction is the universal property of the quotient applied to `x ↦ [δ x]`, which kills the
ideal exactly because the ideal is `δ`-stable; the Leibniz rule then transfers on representatives.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R : Type*} [CommRing R] [Differential R]

/-- The descended derivation, as a function on the quotient. -/
def quotDerivFun (I : Ideal R) (hI : ∀ x ∈ I, Differential.deriv x ∈ I) (z : R ⧸ I) : R ⧸ I :=
  Quotient.liftOn' z (fun x : R => (Ideal.Quotient.mk I) (Differential.deriv x))
    (by
      intro a b hab
      have hmem : a - b ∈ I := by
        rwa [Submodule.quotientRel_def] at hab
      have hderiv : Differential.deriv a - Differential.deriv b ∈ I := by
        have := hI _ hmem
        rwa [map_sub] at this
      exact (Ideal.Quotient.eq).mpr hderiv)

@[simp] theorem quotDerivFun_mk (I : Ideal R) (hI : ∀ x ∈ I, Differential.deriv x ∈ I) (x : R) :
    quotDerivFun I hI (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (Differential.deriv x) := rfl

/-- The descended derivation, as an additive homomorphism. -/
def quotDerivAddHom (I : Ideal R) (hI : ∀ x ∈ I, Differential.deriv x ∈ I) :
    (R ⧸ I) →+ (R ⧸ I) :=
  AddMonoidHom.mk' (quotDerivFun I hI)
    (by
      intro z w
      induction z using Quotient.inductionOn' with
      | h a =>
        induction w using Quotient.inductionOn' with
        | h b =>
          show quotDerivFun I hI (Ideal.Quotient.mk I (a + b))
            = quotDerivFun I hI (Ideal.Quotient.mk I a)
              + quotDerivFun I hI (Ideal.Quotient.mk I b)
          rw [quotDerivFun_mk, quotDerivFun_mk, quotDerivFun_mk, map_add, map_add])

/-- **A derivation descends to the quotient by a differential ideal.** -/
def quotDeriv (I : Ideal R) (hI : ∀ x ∈ I, Differential.deriv x ∈ I) :
    Derivation ℤ (R ⧸ I) (R ⧸ I) where
  toLinearMap := (quotDerivAddHom I hI).toIntLinearMap
  map_one_eq_zero' := by
    show quotDerivFun I hI (Ideal.Quotient.mk I 1) = 0
    rw [quotDerivFun_mk, Derivation.map_one_eq_zero, map_zero]
  leibniz' := by
    intro z w
    induction z using Quotient.inductionOn' with
    | h a =>
      induction w using Quotient.inductionOn' with
      | h b =>
        show quotDerivFun I hI (Ideal.Quotient.mk I (a * b))
          = Ideal.Quotient.mk I a • quotDerivFun I hI (Ideal.Quotient.mk I b)
            + Ideal.Quotient.mk I b • quotDerivFun I hI (Ideal.Quotient.mk I a)
        rw [quotDerivFun_mk, quotDerivFun_mk, quotDerivFun_mk, Derivation.leibniz, map_add]
        simp only [smul_eq_mul, map_mul]

/-- The quotient of a differential ring by a differential ideal is a differential ring. -/
@[reducible] def quotientDifferential (I : Ideal R) (hI : ∀ x ∈ I, Differential.deriv x ∈ I) :
    Differential (R ⧸ I) := ⟨quotDeriv I hI⟩

theorem quotientDifferential_deriv_mk (I : Ideal R) (hI : ∀ x ∈ I, Differential.deriv x ∈ I)
    (x : R) :
    @Differential.deriv _ _ (quotientDifferential I hI) (Ideal.Quotient.mk I x)
      = Ideal.Quotient.mk I (Differential.deriv x) := rfl

/-- **The quotient by a maximal doubly stable ideal is a difference-differential ring.**  The
difference operator descends because the ideal is a `σ`-ideal in both directions, and the derivation
descends because the ideal is a `δ`-ideal; the two descended operators still commute. -/
theorem quotientDifferential_commutesDeriv {σ : R ≃+* R} (hσ : CommutesDeriv σ)
    (I : Ideal R) (hI : IsSigmaDeltaIdeal σ I) (hI' : IsSigmaIdeal σ.symm I) :
    @CommutesDeriv (R ⧸ I) _ (quotientDifferential I hI.2)
      (sigmaQuotientEquiv σ I hI.1 hI') := by
  intro z
  induction z using Quotient.inductionOn' with
  | h a =>
    show sigmaQuotientEquiv σ I hI.1 hI'
        (@Differential.deriv _ _ (quotientDifferential I hI.2) (Ideal.Quotient.mk I a))
      = @Differential.deriv _ _ (quotientDifferential I hI.2)
        (sigmaQuotientEquiv σ I hI.1 hI' (Ideal.Quotient.mk I a))
    rw [quotientDifferential_deriv_mk, sigmaQuotientEquiv_mk, sigmaQuotientEquiv_mk,
      quotientDifferential_deriv_mk, hσ a]

end

end GaloisForLFunctions.HTGeometry
