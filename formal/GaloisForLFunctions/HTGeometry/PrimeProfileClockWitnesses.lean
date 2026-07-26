import GaloisForLFunctions.HTGeometry.PrimeClockUniformAnnihilatorInverseLimit

/-!
# Realizations of the prime-profile clock interfaces

Clock invariance holds for the trivial and full submodules and is preserved by intersections, so
descending invariant chains exist.  Support on positive prime powers holds for the zero profile and
for the indicator of any prime power.

These are the structural premises of the clock-order escape theorem.  Its two analytic premises —
stagewise differential algebraicity together with failure in the inverse limit — are the escape
phenomenon itself and are not interface conditions: a constant chain makes them contradictory, so any
realization must use a strictly descending chain.
-/

namespace GaloisForLFunctions.HTGeometry

/-! ## Clock-invariant submodules -/

theorem primeProfileClockInvariant_top :
    PrimeProfileClockInvariant (⊤ : Submodule ℂ PrimeProfileClockQuotient) :=
  fun _ _ => Submodule.mem_top

theorem primeProfileClockInvariant_bot :
    PrimeProfileClockInvariant (⊥ : Submodule ℂ PrimeProfileClockQuotient) := by
  intro q hq
  rw [Submodule.mem_bot] at hq
  subst hq
  rw [map_zero]
  exact Submodule.zero_mem _

/-- The constant chain at the full submodule is a descending clock-invariant chain. -/
theorem primeProfileClockInvariant_const_chain :
    (∀ _n : ℕ, PrimeProfileClockInvariant (⊤ : Submodule ℂ PrimeProfileClockQuotient)) ∧
      ∀ _n : ℕ, (⊤ : Submodule ℂ PrimeProfileClockQuotient) ≤ ⊤ :=
  ⟨fun _ => primeProfileClockInvariant_top, fun _ => le_rfl⟩

/-! ## Profiles supported on positive prime powers -/

theorem primeProfileSupportedOnPositivePrimePowers_zero :
    PrimeProfileSupportedOnPositivePrimePowers 0 := by
  intro n hn
  exact absurd rfl hn

/-- The indicator of a positive prime power is supported on positive prime powers. -/
theorem primeProfileSupportedOnPositivePrimePowers_indicator (p : Nat.Primes) (e : ℕ) :
    PrimeProfileSupportedOnPositivePrimePowers
      ⟨fun n => if n = (p : ℕ) ^ (e + 1) then 1 else 0, by
        have hp : (p : ℕ) ^ (e + 1) ≠ 0 := pow_ne_zero _ p.2.ne_zero
        simp [Ne.symm hp]⟩ := by
  intro n hn
  refine ⟨p, e, ?_⟩
  by_contra hcase
  apply hn
  simp [hcase]

end GaloisForLFunctions.HTGeometry
