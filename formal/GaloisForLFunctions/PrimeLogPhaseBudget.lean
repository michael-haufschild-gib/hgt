import GaloisForLFunctions.RHTower.WeldRateLattice
import Mathlib.NumberTheory.PrimeCounting

/-!
# Prime phase-budget rank

The signed archimedean Gamma phase-budget law (§7) lower-bounds the recurrent Bohr-frequency rank by
`π(N)` via the rate lattice `Λ_N = ⟨log p : p < N⟩_ℤ`, whose `ℚ`-rank is the prime-counting value
because the prime logarithms are `ℤ`-linearly independent (unique factorization).  The full-family
independence is `RHTower.primeLog_linearIndependent`; this file records its finite restriction to the
primes below `N`, which — having `Nat.primeCounting' N = (N.primesBelow).card` elements — exhibits
`Λ_N` as free of rank exactly `π'(N)`.
-/

namespace GaloisForLFunctions

/-- The logarithms of the primes below `N` are `ℤ`-linearly independent: the restriction of the full
prime-log independence to the finite index set of primes `< N`.  With
`Fintype.card ↥(N.primesBelow) = (N.primesBelow).card = Nat.primeCounting' N`, this exhibits the rate
lattice `Λ_N = ⟨log p : p < N⟩_ℤ` as free of rank exactly `π'(N)` — the phase-budget lower bound. -/
theorem primeLog_primesBelow_linearIndependent (N : ℕ) :
    LinearIndependent ℤ (fun p : (N.primesBelow : Finset ℕ) => Real.log (p : ℕ)) :=
  RHTower.primeLog_linearIndependent.comp
    (fun x : (N.primesBelow : Finset ℕ) =>
      (⟨(x : ℕ), (Nat.mem_primesBelow.mp x.2).2⟩ : Nat.Primes))
    (fun _ _ hab => Subtype.ext (congrArg (fun q : Nat.Primes => (q : ℕ)) hab))

/-- The rank of `Λ_N` is the prime-counting value `π'(N)`: the independent prime-log family below `N`
is indexed by a set of cardinality `Nat.primeCounting' N`. -/
theorem primesBelow_card_eq_primeCounting' (N : ℕ) :
    (N.primesBelow).card = Nat.primeCounting' N :=
  Nat.primesBelow_card_eq_primeCounting' N

end GaloisForLFunctions
