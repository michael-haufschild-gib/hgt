import GaloisForLFunctions.RHTower.ArtinMonomialCharacter
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Concrete Brauer-elementary subgroup data

Brauer induction uses induced linear characters from `p`-elementary subgroups.  This module makes
that carrier concrete: it records internal cyclic `p'` and `p` parts together with an actual
multiplication equivalence.  It does not assume or prove Brauer induction.
-/

noncomputable section

universe u

namespace GaloisForLFunctions

/-- Data witnessing that a subgroup is Brauer `p`-elementary.  The factorization is internal to
the subgroup carrier and its equivalence is required to agree with multiplication. -/
structure BrauerElementarySubgroup (G : Type u) [Group G] where
  subgroup : Subgroup G
  p : ℕ
  p_prime : Nat.Prime p
  cyclicPart : Subgroup subgroup
  pPart : Subgroup subgroup
  cyclicPart_cyclic : IsCyclic cyclicPart
  cyclicPart_coprime : Nat.Coprime (Nat.card cyclicPart) p
  pPart_isPGroup : IsPGroup p pPart
  multiplicationEquiv : cyclicPart × pPart ≃* subgroup
  multiplicationEquiv_apply (c : cyclicPart) (q : pPart) :
    multiplicationEquiv (c, q) = (c : subgroup) * (q : subgroup)

/-- Concrete indices for the induced-linear generators allowed by integral Brauer induction. -/
def brauerElementaryMonomialIndex (G : Type u) [Group G] :=
  Σ E : BrauerElementarySubgroup G, LinearCharacter E.subgroup

/-- The actual monomial virtual character associated to a concrete Brauer-elementary index. -/
def brauerElementaryMonomialVirtualCharacter
    (G : Type u) [Group G] [Fintype G]
    (q : brauerElementaryMonomialIndex G) : VirtualCharacter G :=
  monomialVirtualCharacter G q.1.subgroup q.2

end GaloisForLFunctions
