import Mathlib

/-!
# Canonical exponent vectors for jet monomials

A monomial in jets listed by an arbitrary index — `∏_i u_{n_i}^{e_i}` — is a monomial in the jets
listed *by order*: collecting the exponents of equal orders gives `∏_{j ≤ K} u_j^{E_j}` with
`E_j = ∑_{n_i = j} e_i`.

This is the normalisation that lets a presentation coming from an abstract differential adjoin, where
the variables arrive in arbitrary order, be read as the order-indexed jet polynomial that the
asymptotic residue theorems consume.
-/

namespace GaloisForLFunctions

open Finset

variable {R : Type*} [CommMonoid R]

/-- **Collecting exponents by order.**  Grouping the factors of a jet monomial into the fibres of the
order map turns it into a product over orders. -/
theorem prod_pow_fiber {N K : ℕ} (u : ℕ → R) (n : Fin N → ℕ) (hn : ∀ i, n i < K + 1)
    (e : Fin N → ℕ) :
    ∏ i : Fin N, u (n i) ^ e i
      = ∏ j : Fin (K + 1), u (j : ℕ) ^ (∑ i ∈ univ.filter (fun i => n i = (j : ℕ)), e i) := by
  classical
  have hmaps : ∀ i ∈ (univ : Finset (Fin N)), (⟨n i, hn i⟩ : Fin (K + 1)) ∈ univ :=
    fun i _ => mem_univ _
  rw [← Finset.prod_fiberwise_of_maps_to hmaps (fun i => u (n i) ^ e i)]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hfilter : (univ.filter (fun i => (⟨n i, hn i⟩ : Fin (K + 1)) = j))
      = univ.filter (fun i => n i = (j : ℕ)) := by
    refine Finset.filter_congr fun i _ => ?_
    constructor
    · intro h
      exact congrArg Fin.val h
    · intro h
      exact Fin.ext h
  rw [hfilter, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.mp hi).2]

/-- **The canonical exponent vector of a jet monomial.** -/
theorem exists_canonical_exponents {N : ℕ} (u : ℕ → R) (n : Fin N → ℕ) (e : Fin N → ℕ) :
    ∃ (K : ℕ) (E : Fin (K + 1) → ℕ),
      ∏ i : Fin N, u (n i) ^ e i = ∏ j : Fin (K + 1), u (j : ℕ) ^ E j := by
  classical
  refine ⟨univ.sup n, fun j => ∑ i ∈ univ.filter (fun i => n i = (j : ℕ)), e i,
    prod_pow_fiber u n (fun i => Nat.lt_succ_of_le (Finset.le_sup (mem_univ i))) e⟩

/-- **Canonical exponent vectors for a family sharing one variable list.**  One order bound serves
the whole family, so the family becomes a jet polynomial indexed by orders. -/
theorem exists_canonical_exponents_family {N M : ℕ} (u : ℕ → R) (n : Fin N → ℕ)
    (e : Fin M → Fin N → ℕ) :
    ∃ (K : ℕ) (E : Fin M → Fin (K + 1) → ℕ), ∀ α : Fin M,
      ∏ i : Fin N, u (n i) ^ e α i = ∏ j : Fin (K + 1), u (j : ℕ) ^ E α j := by
  classical
  refine ⟨univ.sup n, fun α j => ∑ i ∈ univ.filter (fun i => n i = (j : ℕ)), e α i, fun α => ?_⟩
  exact prod_pow_fiber u n (fun i => Nat.lt_succ_of_le (Finset.le_sup (mem_univ i))) (e α)

end GaloisForLFunctions
