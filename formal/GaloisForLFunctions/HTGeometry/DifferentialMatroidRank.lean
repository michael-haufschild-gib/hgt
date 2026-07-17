import GaloisForLFunctions.HTGeometry.DifferentialMatroid
import GaloisForLFunctions.HTGeometry.MatroidNatRank

/-!
# Differential transcendence rank for the gluing engine

The genuine differential matroid supplies the natural rank used by the orbit-gluing theorems.
Consequently, `Rank.IndepSet` for this rank is exactly differential independence, rather than an
abstract rank hypothesis.
-/

open scoped Classical Differential

namespace GaloisForLFunctions

open Set
open MatroidGluing

noncomputable section

universe u

/-- Differential transcendence rank on finite subsets of a differential field extension. -/
def differentialRank
    (F E : Type u) [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    [DecidableEq E] : Rank E :=
  matroidRank (differentialMatroid F E)

/-- Independence in the differential rank is exactly differential independence. -/
theorem differentialRank_indepSet_iff
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    [DecidableEq E] {S : Set E} :
    (differentialRank F E).IndepSet S ↔ DiffIndepOn F S := by
  rw [differentialRank, matroidRank_indepSet_iff, differentialMatroid_indep_iff]

/-- The six-face gluing theorem specialized to genuine differential independence.  The remaining
hypotheses are precisely the analytic star-freeness and off-star differential-algebraicity inputs. -/
theorem differentialRank_orderThree_sixFace_diffIndepOn
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    [DecidableEq E]
    (O : Fin 4 × Fin 4 → Set E) (σ : Fin 4 → Equiv.Perm E)
    (hStar : ∀ q : Fin 4, (differentialRank F E).FreeIndepOrbit (σ q)
      (⋃ e ∈ (Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2)).filter
        (fun p => q = p.1 ∨ q = p.2), O e))
    (hOff : ∀ q : Fin 4, (differentialRank F E).CrossNeutral (σ q)
      (⋃ e ∈ (Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2)).filter
        (fun p => ¬ (q = p.1 ∨ q = p.2)), O e)) :
    DiffIndepOn F
      (⋃ e ∈ Finset.univ.filter (fun p : Fin 4 × Fin 4 => p.1 < p.2), O e) := by
  rw [← differentialRank_indepSet_iff]
  exact Rank.orderThree_sixFace_indep (differentialRank F E) O σ hStar hOff

end

end GaloisForLFunctions
