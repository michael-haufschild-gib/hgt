import GaloisForLFunctions.HTGeometry.HolographicLocalityBound
import GaloisForLFunctions.HTGeometry.QuadraticWidthPrincipalSymbolCompletion

/-!
# Quadratic principal-symbol locality universality

The quadratic completion realizes every law-space two-plane independently.  Combining that
terminal construction with the membrane-locality counting theorem exposes the exact locality
cost of any support presentation of its compressed principal symbol.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {M : Type v} [AddCommGroup M] [Module K M]
  {d n : ℕ} [NeZero d] [Fact (1 < d)]
  {H : Type*} [Fintype H]

/-- **Quadratic principal-symbol locality universality law.**  Every membrane-local presentation
of the quadratic-width universal completion is pair-complete.  If each membrane sees at most
`Δ` law directions, then its number and valence obey the sharp covering inequality
`choose n 2 ≤ #H * choose Δ 2`. -/
theorem quadraticWidthPrincipalSymbolCompletion_membraneLocalityUniversality
    (q : K) (hq : IsPrimitiveRoot q d)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M)
    (m : M) (hm : m ≠ 0)
    (support : H → Finset (Fin n)) (Δ : ℕ)
    (hmembrane : MembraneLocalPrincipalBrackets
      (quadraticWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀) support)
    (hlocal : MembraneValenceAtMost support Δ) :
    MembranePairComplete support ∧
      Nat.choose n 2 ≤ Fintype.card H * Nat.choose Δ 2 := by
  have hLI : LinearIndependent K
      (principalBracketPair
        (quadraticWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀)) :=
    quadraticWidthPrincipalSymbolCompletion_principalBracketPair_linearIndependent
      q hq A₀ m hm
  have hcomplete : MembranePairComplete support :=
    membranePairComplete_of_principalBracketPair_linearIndependent
      (quadraticWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀)
      support hmembrane hLI
  exact ⟨hcomplete, by
    simpa using holographicLocality_choose_bound support Δ hcomplete hlocal⟩

/-- Binary locality forces one distinct membrane channel per law-space two-plane for the
quadratic universal completion. -/
theorem quadraticWidthPrincipalSymbolCompletion_binaryLocal_membraneLowerBound
    (q : K) (hq : IsPrimitiveRoot q d)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M)
    (m : M) (hm : m ≠ 0)
    (support : H → Finset (Fin n))
    (hmembrane : MembraneLocalPrincipalBrackets
      (quadraticWidthPrincipalSymbolCompletion q hq.pow_eq_one A₀) support)
    (hlocal : MembraneValenceAtMost support 2) :
    Nat.choose n 2 ≤ Fintype.card H := by
  have h := quadraticWidthPrincipalSymbolCompletion_membraneLocalityUniversality
    q hq A₀ m hm support 2 hmembrane hlocal
  simpa using h.2

end

end GaloisForLFunctions.HTGeometry
