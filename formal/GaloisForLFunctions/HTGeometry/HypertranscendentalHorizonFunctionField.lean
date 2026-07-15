import GaloisForLFunctions.HTGeometry.ProjectiveJetHorizon

/-!
# The finite jet of a hypertranscendental source is the universal function-field point

Hypertranscendence says more than the absence of one chosen differential equation: every finite
jet tuple is algebraically independent.  Consequently, evaluation at that tuple identifies the
universal rational function field in finitely many jet coordinates with the actual field generated
by those jets.  Any finite algebraic horizon construction made functorially from the coordinates
therefore transfers without specialization collapse.

This module certifies the generic-point/function-field core.  Degree and normal-closure monodromy
of a particular rational horizon map remain in the corresponding algebraic-geometric theorem.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The first `L` differential jets of one source. -/
def finiteDifferentialJet
    {E : Type*} [Field E] [Differential E] (x : E) (L : ℕ) : Fin L → E :=
  fun i => differentialJet (i : ℕ) x

/-- Every finite jet packet of a hypertranscendental element is algebraically independent. -/
theorem finiteDifferentialJet_algebraicIndependent_of_hypertranscendentalOver
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (L : ℕ) :
    AlgebraicIndependent F (finiteDifferentialJet x L) := by
  exact (algebraicIndependent_differentialJet_of_hypertranscendentalOver hx).comp
    (fun i : Fin L => (i : ℕ)) (by
      intro i j hij
      exact Fin.ext hij)

/-- No nonzero finite multivariate polynomial vanishes on the finite jet of an HT source. -/
theorem finiteDifferentialJet_aeval_injective_of_hypertranscendentalOver
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (L : ℕ) :
    Function.Injective
      (MvPolynomial.aeval (finiteDifferentialJet x L) : MvPolynomial (Fin L) F → E) :=
  algebraicIndependent_iff_injective_aeval.mp
    (finiteDifferentialJet_algebraicIndependent_of_hypertranscendentalOver hx L)

/-- Evaluation at the finite jet of an HT source identifies the universal rational function
field with the actual finite-jet field. -/
def hypertranscendentalFiniteJetParametrization
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (L : ℕ) :
    FractionRing (MvPolynomial (Fin L) F) ≃ₐ[F]
      IntermediateField.adjoin F (Set.range (finiteDifferentialJet x L)) :=
  (finiteDifferentialJet_algebraicIndependent_of_hypertranscendentalOver hx L).aevalEquivField

/-- The finite-jet parametrization sends each universal coordinate to the corresponding actual
differential jet. -/
@[simp]
theorem hypertranscendentalFiniteJetParametrization_X
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (L : ℕ) (i : Fin L) :
    hypertranscendentalFiniteJetParametrization hx L
        (algebraMap (MvPolynomial (Fin L) F)
          (FractionRing (MvPolynomial (Fin L) F)) (MvPolynomial.X i)) =
      ⟨finiteDifferentialJet x L i,
        IntermediateField.subset_adjoin F _ (Set.mem_range_self i)⟩ := by
  apply Subtype.ext
  simp [hypertranscendentalFiniteJetParametrization]

end

end GaloisForLFunctions.HTGeometry
