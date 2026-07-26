import GaloisForLFunctions.HTGeometry.HolographicLocalityBound

/-!
# Realizations of the membrane-locality interface

Membrane locality is an implication whose premise is a covering failure, so it holds for every
symbol as soon as the membrane supports cover all law pairs, and it holds for every support family
as soon as all principal brackets vanish.  On the opposite extreme, singleton supports cover no pair
at all, so there membrane locality is exactly the vanishing of every principal bracket.

These are the two ends of the locality/compression trade-off measured by the holographic bound: the
covering end makes the interface free but the valence maximal, and the singleton end makes the
valence minimal but forces the bracket family to be trivial, which is incompatible with independence
as soon as one law pair exists.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I H : Type*} [Fintype I] [Fintype H]
variable {K M : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M] [LinearOrder I]

/-! ## Realizations -/

omit [Fintype H] in
/-- **Covering realization.**  If every law pair is met by some membrane, membrane locality holds
for every symbol. -/
theorem membraneLocalPrincipalBrackets_of_covering
    (symbol : (I → K) →ₗ[K] Module.End K M) (support : H → Finset I)
    (hcover : ∀ p : QuantumLawPair I,
      ∃ h : H, p.lower ∈ support h ∧ p.upper ∈ support h) :
    MembraneLocalPrincipalBrackets symbol support := by
  intro p hp
  exact absurd (hcover p) hp

omit [Fintype H] in
/-- Total membranes cover every pair. -/
theorem membraneLocalPrincipalBrackets_univ_support [Nonempty H]
    (symbol : (I → K) →ₗ[K] Module.End K M) :
    MembraneLocalPrincipalBrackets symbol (fun _ : H => (Finset.univ : Finset I)) :=
  membraneLocalPrincipalBrackets_of_covering symbol _ fun _ =>
    ⟨Classical.arbitrary H, Finset.mem_univ _, Finset.mem_univ _⟩

omit [Fintype H] in
/-- **Vanishing realization.**  A symbol with commuting coordinate images is membrane local for
every support family. -/
theorem membraneLocalPrincipalBrackets_of_bracket_eq_zero
    (symbol : (I → K) →ₗ[K] Module.End K M) (support : H → Finset I)
    (hzero : ∀ p : QuantumLawPair I, principalBracketPair symbol p = 0) :
    MembraneLocalPrincipalBrackets symbol support := fun p _ => hzero p

omit [CharZero K] in
theorem principalBracketPair_zero (p : QuantumLawPair I) :
    principalBracketPair (0 : (I → K) →ₗ[K] Module.End K M) p = 0 := by
  simp [principalBracketPair]

omit [Fintype H] in
theorem membraneLocalPrincipalBrackets_zero (support : H → Finset I) :
    MembraneLocalPrincipalBrackets (0 : (I → K) →ₗ[K] Module.End K M) support :=
  membraneLocalPrincipalBrackets_of_bracket_eq_zero _ support principalBracketPair_zero

/-! ## The singleton end -/

/-- Singleton membranes meet no law pair, so there membrane locality is exactly the vanishing of
every principal bracket. -/
theorem membraneLocalPrincipalBrackets_singleton_iff
    (symbol : (I → K) →ₗ[K] Module.End K M) :
    MembraneLocalPrincipalBrackets symbol (fun i : I => ({i} : Finset I)) ↔
      ∀ p : QuantumLawPair I, principalBracketPair symbol p = 0 := by
  constructor
  · intro h p
    refine h p ?_
    rintro ⟨i, hlow, hupp⟩
    rw [Finset.mem_singleton] at hlow hupp
    exact absurd (hlow.trans hupp.symm) (ne_of_lt p.isLt)
  · intro h
    exact membraneLocalPrincipalBrackets_of_bracket_eq_zero symbol _ h

/-- **No independent bracket family is singleton local.**  With singleton membranes, independence of
the principal brackets is impossible once a law pair exists. -/
theorem not_linearIndependent_principalBracketPair_of_singleton_local
    (symbol : (I → K) →ₗ[K] Module.End K M) (p : QuantumLawPair I)
    (hlocal : MembraneLocalPrincipalBrackets symbol (fun i : I => ({i} : Finset I))) :
    ¬ LinearIndependent K (principalBracketPair symbol) := by
  intro hLI
  exact hLI.ne_zero p ((membraneLocalPrincipalBrackets_singleton_iff symbol).mp hlocal p)

/-! ## The covering end of the holographic bound -/

/-- The locality bound at the covering end, with the interface premise discharged. -/
theorem localFaithfulPrincipalSymbol_choose_bound_of_covering [Nonempty H]
    (symbol : (I → K) →ₗ[K] Module.End K M) (Δ : ℕ)
    (hLI : LinearIndependent K (principalBracketPair symbol))
    (hlocal : MembraneValenceAtMost (fun _ : H => (Finset.univ : Finset I)) Δ) :
    Nat.choose (Fintype.card I) 2 ≤ Fintype.card H * Nat.choose Δ 2 :=
  localFaithfulPrincipalSymbol_choose_bound symbol _ Δ
    (membraneLocalPrincipalBrackets_univ_support symbol) hLI hlocal

end

end GaloisForLFunctions.HTGeometry
