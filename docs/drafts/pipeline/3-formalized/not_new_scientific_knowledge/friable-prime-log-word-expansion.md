# Friable prime-log word expansion

- **ID:** friable-prime-log-word-expansion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean certificate split from `../2-fully-proven/friable-dirichlet-auxiliary.md`)
- **Owner:** Leaner
- **Lean file:** `formal/GaloisForLFunctions/RHTower/FriableAuxiliary.lean`

## Statement

For a finite prime-exponent vector `m : Nat.Primes ->₀ ℕ`, the `T`-th power of the prime-log dot product
expands as a finite sum over degree-`T` words in the support of `m`:

```lean
theorem primeLogDot_pow_wordExpansion (m : Nat.Primes ->₀ ℕ) (T : ℕ) :
    (m.sum fun p k => (k : ℂ) * (Real.log (p : ℕ) : ℂ)) ^ T =
      ∑ w ∈ Fintype.piFinset (fun _ : Fin T => m.support),
        ∏ i : Fin T, ((m (w i) : ℂ) * (Real.log (w i : ℕ) : ℂ))
```

Substituting this into the derivative-at-one identity gives:

```lean
theorem iteratedDeriv_friableExponentDirichletExp_at_one_wordExpansion
    (T : ℕ) (P : (Nat.Primes ->₀ ℕ) ->₀ ℂ) :
    iteratedDeriv T (fun z : ℂ => friableExponentDirichletExp P z) 1 =
      (-1 : ℂ) ^ T * P.sum (fun m c =>
        c * (∑ w ∈ Fintype.piFinset (fun _ : Fin T => m.support),
          ∏ i : Fin T, ((m (w i) : ℂ) * (Real.log (w i : ℕ) : ℂ))) *
          ((primeProduct m : ℂ)⁻¹))
```

This is the word-level multinomial expansion. It does not collect equal words into exponent-count coefficient
vectors, define the full auxiliary structure `A_{S,d}`, prove the §5a surjectivity lemma, or prove any
Schanuel/algebraic-independence lower bound.

## Paper Proof

The finite dot product is `sum_{p in supp(m)} m_p log p`. Raise it to the `T`-th power and distribute:

`(sum_p a_p)^T = sum_{w : {1,...,T} -> supp(m)} prod_i a_{w_i}`,

where `a_p = m_p log p`. Grouping words with the same count vector recovers the usual multinomial
coefficients, but the word-sum form already gives the required degree-`T` log-monomial expansion.

The expanded derivative identity follows by substituting this expansion into the already-formalized theorem
`iteratedDeriv_friableExponentDirichletExp_at_one`.

## Gates

- [x] 0 -> 1 in-progress: word-level multinomial expansion isolated from the friable auxiliary card.
- [x] 1 -> 2 fully-proven: finite distributivity / multinomial theorem, then substitution into the derivative
  identity.
- [x] 2 -> 3 formalized: Lean theorems `primeLogDot_pow_wordExpansion` and
  `iteratedDeriv_friableExponentDirichletExp_at_one_wordExpansion`; scratch `#check` and `#print axioms`
  passed; both are audited in `scripts/check_axioms.sh`.
- [ ] 3 -> 4 publication-ready: include as the finite word-expansion step in the friable auxiliary note.

## Log

- 2026-06-19 — Leaner added the word-level log-monomial expansion and the expanded derivative-at-one theorem.
  The parent remains in `2-fully-proven` because coefficient collection, `A_{S,d}` packaging, PNT conversion,
  the surjectivity lemma, and the Schanuel-bound layer are not fully formalized.
