import GaloisForLFunctions.HTGeometry.FormalMahlerIntegerNormalization

/-!
# Formal leading-coefficient specialization

A finite algebraic differential relation depending polynomially on a formal parameter specializes
to a relation on the constant coefficients, provided the specialized relation is nonzero.  This is
the algebraic core of transporting differential algebraicity from a cosmological total-energy
Laurent germ to its leading flat-space coefficient.

The normalization step that clears rational parameter denominators and removes the common lowest
parameter power is deliberately separate: this file proves the exact specialization receiver once
that normalized polynomial relation is supplied.
-/

open PowerSeries MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Specialize the polynomial coefficient parameter to zero. -/
def formalParameterSpecialization
    {F ι : Type*} [CommRing F]
    (P : MvPolynomial ι (Polynomial F)) : MvPolynomial ι F :=
  MvPolynomial.map (Polynomial.evalRingHom 0) P

/-- Interpret a polynomial in the formal parameter as a power series after mapping its scalar
coefficients into the target algebra. -/
def polynomialFormalParameterMap
    {F K : Type*} [CommRing F] [CommRing K] [Algebra F K] :
    Polynomial F →+* PowerSeries K :=
  Polynomial.eval₂RingHom (algebraMap F (PowerSeries K)) PowerSeries.X

theorem constantCoeff_comp_polynomialFormalParameterMap
    {F K : Type*} [CommRing F] [CommRing K] [Algebra F K] :
    PowerSeries.constantCoeff.comp
        (polynomialFormalParameterMap (F := F) (K := K)) =
      Polynomial.eval₂RingHom (algebraMap F K) 0 := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [polynomialFormalParameterMap, PowerSeries.algebraMap_apply]
  · simp [polynomialFormalParameterMap]

theorem algebraMap_comp_evalRingHom_zero
    {F K : Type*} [CommRing F] [CommRing K] [Algebra F K] :
    (algebraMap F K).comp (Polynomial.evalRingHom 0) =
      Polynomial.eval₂RingHom (algebraMap F K) 0 := by
  apply Polynomial.ringHom_ext
  · intro a
    simp
  · simp

/-- Constant-term extraction from a formal-parameter relation is evaluation of the coefficient
parameter at zero and of every response variable at its constant coefficient. -/
theorem constantCoeff_eval₂_polynomialFormalParameterMap
    {F K ι : Type*} [CommRing F] [CommRing K] [Algebra F K]
    (jets : ι → PowerSeries K) (P : MvPolynomial ι (Polynomial F)) :
    PowerSeries.constantCoeff
        (MvPolynomial.eval₂ polynomialFormalParameterMap jets P) =
      MvPolynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap F K) 0)
        (fun i ↦ PowerSeries.constantCoeff (jets i)) P := by
  let lhs : MvPolynomial ι (Polynomial F) →+* K :=
    PowerSeries.constantCoeff.comp
      (MvPolynomial.eval₂Hom polynomialFormalParameterMap jets)
  let rhs : MvPolynomial ι (Polynomial F) →+* K :=
    MvPolynomial.eval₂Hom (Polynomial.eval₂RingHom (algebraMap F K) 0)
      (fun i ↦ PowerSeries.constantCoeff (jets i))
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro p
      simpa [lhs, rhs] using RingHom.congr_fun
        (constantCoeff_comp_polynomialFormalParameterMap (F := F) (K := K)) p
    · intro i
      simp [lhs, rhs]
  exact DFunLike.congr_fun hhom P

/-- Evaluation of the zero-parameter specialization equals the constant term of the original
formal-parameter evaluation. -/
theorem aeval_formalParameterSpecialization_eq_constantCoeff
    {F K ι : Type*} [CommRing F] [CommRing K] [Algebra F K]
    (jets : ι → PowerSeries K) (P : MvPolynomial ι (Polynomial F)) :
    MvPolynomial.aeval (fun i ↦ PowerSeries.constantCoeff (jets i))
        (formalParameterSpecialization P) =
      PowerSeries.constantCoeff
        (MvPolynomial.eval₂ polynomialFormalParameterMap jets P) := by
  rw [MvPolynomial.aeval_def, formalParameterSpecialization,
    MvPolynomial.eval₂_map]
  rw [constantCoeff_eval₂_polynomialFormalParameterMap]
  rw [algebraMap_comp_evalRingHom_zero]

/-- A normalized nonzero formal-parameter relation on power-series lifts of finitely many jets
forces an algebraic differential relation on their constant coefficient. -/
theorem differentialAlgebraicOver_of_normalized_formalParameterRelation
    {F K : Type*} [CommRing F] [CommRing K] [Algebra F K] [Differential K]
    {x : K} {n : ℕ} {P : MvPolynomial (Fin (n + 1)) (Polynomial F)}
    (formalJets : Fin (n + 1) → PowerSeries K)
    (hconstant : ∀ j, PowerSeries.constantCoeff (formalJets j) =
      GaloisForLFunctions.differentialJet (j : ℕ) x)
    (hP : formalParameterSpecialization P ≠ 0)
    (hann : MvPolynomial.eval₂ polynomialFormalParameterMap formalJets P = 0) :
    GaloisForLFunctions.DifferentialAlgebraicOver F x := by
  apply GaloisForLFunctions.differentialAlgebraicOver_of_finiteJetRelation hP
  have hspecialized := congrArg PowerSeries.constantCoeff hann
  rw [map_zero] at hspecialized
  rw [← aeval_formalParameterSpecialization_eq_constantCoeff formalJets P]
    at hspecialized
  simpa only [hconstant] using hspecialized

end

end GaloisForLFunctions.HTGeometry
