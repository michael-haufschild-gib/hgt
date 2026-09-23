import GaloisForLFunctions.RHTower.StaticChoiComplexityAlternationLaw
import GaloisForLFunctions.HTGeometry.FiniteAndersonProjectiveGenericityLaw

/-!
# Operational complexity alternation for finite Anderson Hamiltonians

The abstract static Choi alternation law is specialized here to a standard
local Hamiltonian family: arbitrary finite Hermitian hopping plus real onsite
potential.  The relevant onsite set is already proved dense, residual, and of
full Lebesgue measure.  Every Hamiltonian in that set alternates forever
between operational recurrence and bounded-circuit hardness.
-/

open Set

noncomputable section

namespace RHTower

/-- **Local-Hamiltonian operational alternation law.** Every finite Anderson
Hamiltonian in the dense residual full-measure maximal-projective set obeys
the ordered trace-distance recurrence--complexity--recurrence law. -/
theorem finiteAnderson_pureChoiComplexity_alternates_syndetically
    {d : ℕ}
    (T : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hT : T.IsHermitian) (onsite : Fin (d + 1) → ℝ)
    (honsite : onsite ∈
      GaloisForLFunctions.HTGeometry.finiteAndersonProjectiveMaximalSet T hT)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (htarget : ∀ w, ‖target w‖ = 1)
    (identityWord : PaddedCircuitWord gate s)
    (hidentity : target identityWord =
      fullUniformPhaseChoiVector (d + 1)
        (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle)))
    {ε : ℝ} (hε : 0 < ε)
    (hentropy :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt
              (Real.pi * (2 * (Real.sqrt 2 * ε) ^ (2 : ℕ)) / 2) ^
                ((d + 1 : ℕ) - 1)) < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a : ℝ,
      ∃ tLow ∈ Set.Icc a (a + L),
      ∃ tHigh ∈ Set.Ioc tLow (tLow + L),
      ∃ tLow' ∈ Set.Ioc tHigh (tHigh + L),
        pureStateTraceDistance
            (fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d
                (projectivePhysicalPhaseFlow
                  (GaloisForLFunctions.HTGeometry.finiteAndersonHamiltonian_isHermitian
                    T hT onsite).eigenvalues tLow)))
            (fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle))) < ε ∧
        (∀ w : PaddedCircuitWord gate s,
          ε < pureStateTraceDistance
            (fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d
                (projectivePhysicalPhaseFlow
                  (GaloisForLFunctions.HTGeometry.finiteAndersonHamiltonian_isHermitian
                    T hT onsite).eigenvalues tHigh)))
            (target w)) ∧
        pureStateTraceDistance
            (fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d
                (projectivePhysicalPhaseFlow
                  (GaloisForLFunctions.HTGeometry.finiteAndersonHamiltonian_isHermitian
                    T hT onsite).eigenvalues tLow')))
            (fullUniformPhaseChoiVector (d + 1)
              (zeroAnchoredPhase d (0 : Fin d → UnitAddCircle))) < ε := by
  exact maximallyProjective_pureChoiComplexity_alternates_syndetically
    (GaloisForLFunctions.HTGeometry.finiteAndersonHamiltonian_isHermitian
      T hT onsite).eigenvalues honsite s target htarget identityWord hidentity hε hentropy

end RHTower
