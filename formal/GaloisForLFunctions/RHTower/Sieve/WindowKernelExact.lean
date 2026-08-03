import GaloisForLFunctions.RHTower.Sieve.WindowTriangularWeight

/-!
# The overlap kernel *is* the triangular weight in the bulk

Away from the two boundaries — `n, m ≥ L` so the lower endpoint is not truncated, and `n, m ≤ X` so
the range of starts is not cut — the set of common starts is exactly `[max(n,m) - L, min(n,m))`, so

`K(n,m) = L - |n - m|`   whenever `|n - m| ≤ L`.

The triangular bound of the previous section is therefore attained, not merely valid: the kernel side
of the short-interval variance is exact, and nothing further can be extracted from it.  In particular
`K(n,n) = L` on the diagonal.

Any improvement on the trivial variance bound must come from arithmetic cancellation in the
coefficients, never from a better kernel estimate.
-/

namespace RHTower.Sieve

open Finset

/-- The exact kernel, in the ordered case. -/
theorem windowOverlap_eq_sub_of_le {X L n m : ℕ} (hnm : n ≤ m) (hm : L ≤ m) (hmX : m ≤ X)
    (hd : m - n ≤ L) : windowOverlap X L n m = L - (m - n) := by
  classical
  have hset : (Finset.range X).filter
      (fun x => n ∈ Finset.Ioc x (x + L) ∧ m ∈ Finset.Ioc x (x + L))
      = Finset.Ico (m - L) n := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc, Finset.mem_Ico]
    constructor
    · rintro ⟨_, ⟨h1, h2⟩, ⟨h3, h4⟩⟩
      omega
    · intro h
      omega
  rw [windowOverlap, hset, Nat.card_Ico]
  omega

/-- **The overlap kernel is exactly the triangular weight in the bulk.** -/
theorem windowOverlap_eq_sub_dist {X L n m : ℕ} (hn : L ≤ n) (hm : L ≤ m)
    (hnX : n ≤ X) (hmX : m ≤ X) (hd : Nat.dist n m ≤ L) :
    windowOverlap X L n m = L - Nat.dist n m := by
  rcases le_total n m with h | h
  · rw [Nat.dist_eq_sub_of_le h] at hd ⊢
    exact windowOverlap_eq_sub_of_le h hm hmX hd
  · rw [windowOverlap_comm, Nat.dist_comm] at *
    rw [Nat.dist_eq_sub_of_le h] at hd ⊢
    exact windowOverlap_eq_sub_of_le h hn hnX hd

/-- **On the diagonal every start counts.** -/
theorem windowOverlap_self {X L n : ℕ} (hn : L ≤ n) (hnX : n ≤ X) :
    windowOverlap X L n n = L := by
  have h := windowOverlap_eq_sub_dist hn hn hnX hnX (by simp)
  simpa using h

end RHTower.Sieve
