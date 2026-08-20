import GaloisForLFunctions.RHTower.PrimeLogPhaseBudget
import GaloisForLFunctions.Core

/-!
# The prime-character carrier budget of the two-channel source

At prime cutoff `N` the truncated Euler source of the two-channel resolvent family spans the
rational vector space `V_N = ⟨log p : p < N⟩_ℚ`, whose dimension is the prime-counting value
`π'(N)`, because prime logarithms are `ℚ`-linearly independent.  A positive resource decomposition
of a recurrent differentially algebraic implementation therefore forces the complementary
arithmetic character module to carry at least `π'(N)` minus the finite boundary rank.
-/

noncomputable section

namespace GaloisForLFunctions

/-- The prime logarithms below `N` are `ℚ`-linearly independent. -/
theorem linearIndependent_log_primesBelow_rat (N : ℕ) :
    LinearIndependent ℚ (fun p : (N.primesBelow : Finset ℕ) => Real.log (p : ℕ)) :=
  linearIndependent_log_primes.comp
    (fun x : (N.primesBelow : Finset ℕ) =>
      (⟨(x : ℕ), (Nat.mem_primesBelow.mp x.2).2⟩ : Nat.Primes))
    (fun _ _ hab => Subtype.ext (congrArg (fun q : Nat.Primes => (q : ℕ)) hab))

/-- **Equation (20c).**  The rational span of the prime logarithms below `N` has dimension exactly
`π'(N)`. -/
theorem finrank_span_log_primesBelow (N : ℕ) :
    Module.finrank ℚ (Submodule.span ℚ
        (Set.range (fun p : (N.primesBelow : Finset ℕ) => Real.log (p : ℕ))))
      = Nat.primeCounting' N := by
  rw [finrank_span_eq_card (linearIndependent_log_primesBelow_rat N), Fintype.card_coe,
    primesBelow_card_eq_primeCounting']

/-- **Equations (20d)-(20e).**  A finite boundary carrier of rank `deltaBeta + 2 m (n+1)` leaves the
complementary arithmetic character module with rank at least the prime deficit. -/
theorem carrierBudget_rank_ge {N deltaBeta m n rankA : ℕ}
    (h : Nat.primeCounting' N ≤ deltaBeta + 2 * m * (n + 1) + rankA) :
    Nat.primeCounting' N - (deltaBeta + 2 * m * (n + 1)) ≤ rankA := by
  omega

end GaloisForLFunctions
