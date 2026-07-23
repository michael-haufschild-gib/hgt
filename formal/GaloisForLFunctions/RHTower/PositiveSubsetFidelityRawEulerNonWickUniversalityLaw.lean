import GaloisForLFunctions.RHTower.CCMSubsetFidelityReadoutRigidity
import GaloisForLFunctions.RHTower.EulerSquarefreeWickDefect

/-!
# Positive subset fidelity forces raw-Euler non-Wick behavior

Exact recovery of the four-coordinate full product by a nonnegative subset-channel mixture forces
all mixture weight onto the full subset.  The surviving channel is therefore the raw squarefree
Euler top atom.  At any nonzero four-local realization, its Wick defect is the nonvanishing
shared-Rademacher fourth cumulant `-2 a₀ a₁ a₂ a₃`.

Consequently positive subset redistribution cannot turn exact multiplicative Euler fidelity into a
Gaussian pair-matching source.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- **Positive-fidelity/raw-Euler non-Wick universality law.**  Any nonnegative four-coordinate
subset mixture with exact full-product fidelity is the top atom, whose every nonzero local
realization has the exact shared-Rademacher non-Wick defect. -/
theorem positiveFullProductFidelity_forces_rawEulerNonWick
    (weight : Finset (Fin 4) → ℝ)
    (hweight : ∀ T, T ⊆ (Finset.univ : Finset (Fin 4)) → 0 ≤ weight T)
    (hfidelity : ∀ S, S ⊆ (Finset.univ : Finset (Fin 4)) →
      positiveSquarefreeSubsetMixture Finset.univ weight S =
        GaloisForLFunctions.RHProofLab.squarefreeMonomial
          (booleanSubsetPoint S) Finset.univ)
    (a : Fin 4 → ℂ) (ha : ∀ i, a i ≠ 0) :
    (∀ S, S ⊆ (Finset.univ : Finset (Fin 4)) →
      weight S = if S = Finset.univ then 1 else 0) ∧
    GaloisForLFunctions.RHTower.eulerSquarefreeWickFourDefect a =
      -2 * a 0 * a 1 * a 2 * a 3 ∧
    GaloisForLFunctions.RHTower.eulerSquarefreeWickFourDefect a =
      GaloisForLFunctions.RHTower.sharedRademacherMoment a {0, 1, 2, 3} -
        (GaloisForLFunctions.RHTower.sharedRademacherMoment a {0, 1} *
            GaloisForLFunctions.RHTower.sharedRademacherMoment a {2, 3} +
          GaloisForLFunctions.RHTower.sharedRademacherMoment a {0, 2} *
            GaloisForLFunctions.RHTower.sharedRademacherMoment a {1, 3} +
          GaloisForLFunctions.RHTower.sharedRademacherMoment a {0, 3} *
            GaloisForLFunctions.RHTower.sharedRademacherMoment a {1, 2}) ∧
    ¬ GaloisForLFunctions.RHTower.eulerSquarefreeWickFourLaw a := by
  exact
    ⟨positiveSquarefreeSubsetMixture_eq_fullAtom_of_topMonomialFidelity
      Finset.univ weight hweight hfidelity,
     GaloisForLFunctions.RHTower.eulerSquarefreeWickFourDefect_eq a,
     GaloisForLFunctions.RHTower.eulerSquarefreeWickFourDefect_eq_sharedRademacherCumulant a,
     GaloisForLFunctions.RHTower.not_eulerSquarefreeWickFourLaw_of_nonzero a ha⟩

end

end RHTower
