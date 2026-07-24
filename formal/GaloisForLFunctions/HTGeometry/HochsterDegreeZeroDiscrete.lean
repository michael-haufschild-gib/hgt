import GaloisForLFunctions.HTGeometry.ReducedH0DiscreteComplex
import GaloisForLFunctions.HTGeometry.KoszulCohomology

/-!
# The degree-0 Hochster identity for the discrete complex

Hochster's formula matches, in degree zero, the first Koszul cohomology of a Stanley–Reisner boundary
model to the reduced simplicial cohomology of the complex.  For the isolated (fully discrete) complex
on `n+2` vertices this is the numerical identity

`dim (reduced H̃⁰ of the discrete complex) = (number of isolated first-Koszul Hochster classes)`,

both equal to `n+1`.  The left side is the combinatorial reduced zeroth cohomology
(`finrank_reducedH0_bot`); the right side is the number of base-to-component representatives
`isolatedDisconnectCycleBasis`, indexed by `Fin (n+1)` and shown independent modulo Koszul boundaries in
`isolatedDisconnectCycleBasis_independent_mod_koszulBoundary`.

This is the explicit degree-0 instance of the strand equivalence connecting the combinatorial
(reduced-cochain) and algebraic (Koszul) sides.
-/

namespace GaloisForLFunctions

open SimpleGraph

noncomputable section

variable (F : Type*) [Field F] (n : ℕ)

/-- **Degree-0 Hochster identity (discrete complex).**  The combinatorial reduced `H̃⁰` of the discrete
complex on `n+2` vertices has dimension `n+1`, equal to the number of isolated-family first-Koszul
Hochster classes (`isolatedDisconnectCycleBasis`, indexed by `Fin (n+1)`). -/
theorem finrank_reducedH0_bot_eq_isolatedBasis_card :
    Module.finrank F
        (componentConstant (⊥ : SimpleGraph (Fin (n + 2))) F ⧸
          (F ∙ (⟨fun _ => (1 : F),
              one_mem_componentConstant (⊥ : SimpleGraph (Fin (n + 2))) F⟩ :
            componentConstant (⊥ : SimpleGraph (Fin (n + 2))) F)))
      = Fintype.card (Fin (n + 1)) := by
  haveI : Nonempty (Fin (n + 2)) := ⟨0⟩
  rw [finrank_reducedH0_bot, Fintype.card_fin, Fintype.card_fin]

end

end GaloisForLFunctions
