import GaloisForLFunctions.RHTower.SmoothNumbers

/-!
# Bounded smooth frequencies: witnesses and their exact count

The two interfaces `supportedBounded` and `isBoundedSmooth` are related to each other by transfer
lemmas and by an equivalence, but neither is exhibited on a concrete object.  This file supplies the
witnesses and then the exact size of the class.

Bounded exponent vectors on `S` are just the functions `S → {0, …, N}`: the coordinate map is a
bijection, its inverse extending a function by zero off `S`.  Composing with the unique-factorization
equivalence gives the count of bounded `S`-smooth integers,

`Nat.card {n // isBoundedSmooth S N n} = (N + 1) ^ |S|`,

which is the number of distinct Dirichlet frequencies produced by a finite auxiliary form supported
on `S` with exponents at most `N`.

* `supportedBounded_zero`, `isBoundedSmooth_one`, `supportedBounded_single`,
  **`isBoundedSmooth_prime_pow`** — the witnesses;
* `supportedBounded.mono`, `isBoundedSmooth.mono` — monotonicity in the prime set and the bound;
* `boundedVectorEquivFun`, **`card_isBoundedSmooth`** — the coordinate description and the count.
-/

namespace GaloisForLFunctions

/-! ### Witnesses -/

/-- The zero exponent vector is bounded and supported anywhere. -/
theorem supportedBounded_zero (S : Finset Nat.Primes) (N : ℕ) :
    supportedBounded S N (0 : Nat.Primes →₀ ℕ) := by
  refine ⟨?_, fun p => ?_⟩
  · simp
  · simp

/-- One is a bounded smooth frequency for every prime set and every bound. -/
theorem isBoundedSmooth_one (S : Finset Nat.Primes) (N : ℕ) : isBoundedSmooth S N 1 := by
  refine ⟨one_ne_zero, fun p hp => ?_⟩
  rw [Nat.factorization_one] at hp
  simp at hp

/-- A single exponent below the bound, at a prime of `S`, is a bounded supported vector. -/
theorem supportedBounded_single {S : Finset Nat.Primes} {N : ℕ} {p : Nat.Primes} {k : ℕ}
    (hp : p ∈ S) (hk : k ≤ N) : supportedBounded S N (Finsupp.single p k) := by
  refine ⟨?_, fun q => ?_⟩
  · intro q hq
    rcases Finset.mem_singleton.mp (Finsupp.support_single_subset hq) with rfl
    exact hp
  · by_cases hq : q = p
    · subst hq
      simpa using hk
    · simp [hq]

/-- **A prime power of `S` below the bound is a bounded smooth frequency.**  This is the generic
witness: the class contains every `p ^ k` with `p ∈ S` and `k ≤ N`. -/
theorem isBoundedSmooth_prime_pow {S : Finset Nat.Primes} {N : ℕ} {p : Nat.Primes} {k : ℕ}
    (hp : p ∈ S) (hk : k ≤ N) : isBoundedSmooth S N ((p : ℕ) ^ k) := by
  have h := isBoundedSmooth_primeProduct_of_supportedBounded (supportedBounded_single hp hk)
  have hprod : primeProduct (Finsupp.single p k) = (p : ℕ) ^ k := by
    unfold primeProduct
    rw [Finsupp.prod_single_index]
    simp
  rwa [hprod] at h

/-! ### Monotonicity -/

/-- Enlarging the prime set or the exponent bound preserves boundedness. -/
theorem supportedBounded.mono {S T : Finset Nat.Primes} {N M : ℕ} {m : Nat.Primes →₀ ℕ}
    (h : supportedBounded S N m) (hST : S ⊆ T) (hNM : N ≤ M) : supportedBounded T M m :=
  ⟨fun _ hp => hST (h.1 hp), fun p => le_trans (h.2 p) hNM⟩

/-- Enlarging the prime set or the exponent bound preserves bounded smoothness. -/
theorem isBoundedSmooth.mono {S T : Finset Nat.Primes} {N M n : ℕ}
    (h : isBoundedSmooth S N n) (hST : S ⊆ T) (hNM : N ≤ M) : isBoundedSmooth T M n :=
  ⟨h.1, fun p hp => ⟨hST (h.2 p hp).1, le_trans (h.2 p hp).2 hNM⟩⟩

/-! ### The coordinate description and the count -/

/-- **Bounded exponent vectors are exactly the functions `S → {0, …, N}`.**  Forward, read the
exponents at the primes of `S`; backward, extend a function by zero off `S`. -/
noncomputable def boundedVectorEquivFun (S : Finset Nat.Primes) (N : ℕ) :
    {m : Nat.Primes →₀ ℕ // supportedBounded S N m} ≃ (S → Fin (N + 1)) where
  toFun m p := ⟨m.1 p, Nat.lt_succ_of_le (m.2.2 p)⟩
  invFun f :=
    ⟨Finsupp.onFinset S (fun p => if h : p ∈ S then ((f ⟨p, h⟩ : Fin (N + 1)) : ℕ) else 0)
        (by
          intro p hp
          by_contra hpS
          simp only [dif_neg hpS] at hp
          exact hp rfl),
      by
        refine ⟨Finsupp.support_onFinset_subset, fun p => ?_⟩
        rw [Finsupp.onFinset_apply]
        by_cases h : p ∈ S
        · rw [dif_pos h]
          exact Nat.lt_succ_iff.mp (f ⟨p, h⟩).isLt
        · rw [dif_neg h]
          exact Nat.zero_le N⟩
  left_inv m := by
    apply Subtype.ext
    ext p
    rw [Finsupp.onFinset_apply]
    by_cases h : p ∈ S
    · rw [dif_pos h]
    · rw [dif_neg h]
      by_contra hne
      exact h (m.2.1 (Finsupp.mem_support_iff.mpr fun hz => hne hz.symm))
  right_inv f := by
    funext p
    apply Fin.ext
    dsimp only
    rw [Finsupp.onFinset_apply, dif_pos p.2]

/-- **The number of bounded smooth frequencies.**  A finite auxiliary form supported on `S` with
exponents at most `N` has exactly `(N + 1) ^ |S|` distinct Dirichlet frequencies. -/
theorem card_isBoundedSmooth (S : Finset Nat.Primes) (N : ℕ) :
    Nat.card {n : ℕ // isBoundedSmooth S N n} = (N + 1) ^ S.card := by
  classical
  have h1 : Nat.card {n : ℕ // isBoundedSmooth S N n}
      = Nat.card {m : Nat.Primes →₀ ℕ // supportedBounded S N m} :=
    Nat.card_congr (boundedExponentVectorEquivSmooth S N).symm
  have h2 : Nat.card {m : Nat.Primes →₀ ℕ // supportedBounded S N m}
      = Nat.card (S → Fin (N + 1)) :=
    Nat.card_congr (boundedVectorEquivFun S N)
  rw [h1, h2, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]

/-- The class of bounded smooth frequencies is never empty. -/
theorem nonempty_isBoundedSmooth (S : Finset Nat.Primes) (N : ℕ) :
    Nonempty {n : ℕ // isBoundedSmooth S N n} :=
  ⟨⟨1, isBoundedSmooth_one S N⟩⟩

end GaloisForLFunctions
