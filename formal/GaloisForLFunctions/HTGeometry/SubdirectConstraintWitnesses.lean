import GaloisForLFunctions.HTGeometry.PrimeConstraintJoining

/-!
# Realizations of the subdirect constraint interface

A relation is subdirect when every local value occurs in some member.  This holds as soon as the
relation contains the constant profiles, so the full relation and the diagonal realize it, and it is
monotone.  The coupled-prime realization theorem therefore needs no separate subdirectness premise
whenever the carried relation contains the constants.
-/

namespace GaloisForLFunctions.HTGeometry

variable {I V : Type*}

/-! ## Realizations -/

/-- Containing the constant profiles is enough to be subdirect. -/
theorem isSubdirectConstraint_of_const_mem {C : Set (I → V)}
    (h : ∀ v : V, (fun _ => v) ∈ C) : IsSubdirectConstraint C :=
  fun _ v => ⟨fun _ => v, h v, rfl⟩

theorem isSubdirectConstraint_univ : IsSubdirectConstraint (Set.univ : Set (I → V)) :=
  isSubdirectConstraint_of_const_mem fun _ => Set.mem_univ _

/-- The diagonal relation is subdirect. -/
theorem isSubdirectConstraint_diagonal :
    IsSubdirectConstraint (Set.range fun v : V => (fun _ => v : I → V)) :=
  isSubdirectConstraint_of_const_mem fun v => ⟨v, rfl⟩

theorem IsSubdirectConstraint.mono {C C' : Set (I → V)} (hsub : C ⊆ C')
    (hC : IsSubdirectConstraint C) : IsSubdirectConstraint C' := by
  intro i v
  obtain ⟨c, hcC, hcv⟩ := hC i v
  exact ⟨c, hsub hcC, hcv⟩

/-! ## The premise disappears from the coupled-prime realization -/

/-- **Coupled-prime realization for constant-containing relations.**  A recurrent relation carrying
all constant profiles is realized by one prime source, with no subdirectness premise. -/
theorem joinedPrimeSource_realizes_recurringConstraint_of_const_mem
    [Fintype I] [Nonempty I]
    (E : (ℕ × I) ≃ Nat.Primes) (y : ℕ → I → V) (C : Set (I → V))
    (hy : recurringValueSet y = C) (hconst : ∀ v : V, (fun _ => v) ∈ C) :
    recurringValueSet (joinedPrimeSource E y) = Set.univ ∧
      CofinitelyRecurring (joinedPrimeSource E y) ∧
      recurringValueSet
          (fun n => distinctConfigurationProfile (joinedPrimeSource E y)
            (joinedPrimeConfiguration E n)) = C :=
  joinedPrimeSource_realizes_subdirect_recurringConstraint E y C hy
    (isSubdirectConstraint_of_const_mem hconst)

/-- **Coupled-prime realization for the full relation.** -/
theorem joinedPrimeSource_realizes_recurringConstraint_univ
    [Fintype I] [Nonempty I]
    (E : (ℕ × I) ≃ Nat.Primes) (y : ℕ → I → V)
    (hy : recurringValueSet y = (Set.univ : Set (I → V))) :
    recurringValueSet (joinedPrimeSource E y) = Set.univ ∧
      CofinitelyRecurring (joinedPrimeSource E y) ∧
      recurringValueSet
          (fun n => distinctConfigurationProfile (joinedPrimeSource E y)
            (joinedPrimeConfiguration E n)) = Set.univ :=
  joinedPrimeSource_realizes_subdirect_recurringConstraint E y Set.univ hy
    isSubdirectConstraint_univ

end GaloisForLFunctions.HTGeometry
