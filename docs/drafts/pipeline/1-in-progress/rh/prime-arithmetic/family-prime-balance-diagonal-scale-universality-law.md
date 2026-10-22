# Family prime-balance diagonal-scale universality law

- **ID:** family-prime-balance-diagonal-scale-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** Lean-corpus closure of family cross-resonance, diagonal character, and prime-product
  unique factorization
- **Statement:** Aggregate signed prime balance is neutral exactly when its positive and negative
  prime products agree; this same condition forces coordinatewise balance, equality of all complex
  diagonal Dirichlet monomials, and deletion of every shared scale from every commutative-group
  twisted family product.

## Goal

Determine whether the corpus's family resonance balance, prime-torus diagonal identity, and
arbitrary commutative-group scale split are independent descriptions of one universal neutral
phase.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [ ] 2 → 3 formalized: tree source and exact `lake env lean` passed; final axiom audit pending
- [ ] 3 → 4 publication-ready: post-proof literature audit pending

## Corpus inputs

- `familyTwistedProduct_split`
- `familyPrimeBalance_eq_zero_of_primeProduct_eq`
- `familyPrimeBalance_apply_eq_zero_of_primeProduct_eq`
- `diagonal_character_eq_dirichlet`
- `bohrCharacter_zero`

## Proof

`[PROVED HERE]` Let `b = ∑ᵢ mᵢ` be the aggregate signed prime-exponent vector.  Equality of
`primeProduct (positivePart b)` and `primeProduct (negativePart b)` forces `b = 0` by unique
factorization.  Evaluation at each prime then gives `∑ᵢ mᵢ(p) = 0`.

For each natural exponent vector `a`, the diagonal-character theorem identifies its prime-torus
monomial with `primeProduct(a)^z` for every complex `z`.  Therefore equality of the positive and
negative prime products gives equality of their complete complex diagonal monomial families.
Conversely, equality of those families at `z = 1` recovers equality of the encoded integers.

Finally, the family twisted-product split factors every shared-scale realization as
`(product of twist characters) * bohrCharacter b scale`.  Since `b = 0`, the last factor is one,
independently of the commutative group and shared scale.  Conversely, the simultaneous package
contains `b = 0`, whose positive and negative prime products are both one.

No numerical computation is used.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.FamilyPrimeBalanceDiagonalScaleUniversalityLaw`
- Main theorem:
  `GaloisForLFunctions.familyPrimeBalance_diagonalScaleUniversality`
- Exact source check:
  `lake env lean GaloisForLFunctions/RHTower/FamilyPrimeBalanceDiagonalScaleUniversalityLaw.lean`
  passed on 2026-07-23.
- Imported by `GaloisForLFunctions/RHTower.lean`.
- Final axiom audit and module build deferred to final audit.

## Novelty protocol

No literature search before exact Lean proof.

## Post-proof literature audit

Performed only after exact Lean source check passed.

- Defant, García, Maestre, and Sevilla-Peris, *Dirichlet Series and Holomorphic Functions in High
  Dimensions*, Chapter 3, “Bohr's Vision”
  ([Cambridge University Press](https://www.cambridge.org/core/books/dirichlet-series-and-holomorphic-functions-in-high-dimensions/207B14D75EA0CD5EEBC202A8B62D1ADF/listing?pageNum=2)),
  develops the Bohr transform from unique prime factorization and identifies monomials with
  Dirichlet coefficients.  This is the closest parent for the diagonal-monomial component.
- Carando, Defant, García, Maestre, and Sevilla-Peris, *The Dirichlet-Bohr radius*
  ([arXiv:1412.5947](https://arxiv.org/abs/1412.5947)), systematically transfers estimates between
  finite Dirichlet polynomials and multivariable Bohr radii.  It does not state the signed
  finite-family balance/scale-erasure equivalence.
- Defant et al., *Multipliers of Dirichlet series and monomial series expansions of holomorphic
  functions in infinitely many variables*
  ([arXiv:1405.7205](https://arxiv.org/abs/1405.7205)), supplies broader infinite-polydisk/Dirichlet
  correspondence context, not the arbitrary-commutative-group twisted-product conclusion.

No exact source was found equating signed aggregate prime-product neutrality with all complex
diagonal monomial equalities and universal deletion of a shared scale from an arbitrary
commutative-group family product.  Door 2 remains open rather than claimed closed.

## Log

- 2026-07-23 — terminal-symbol scan exposed shared `primeProduct`; actual theorem statements showed
  a live connector from aggregate balance to both diagonal Dirichlet and arbitrary-group scale
  realizations.
- 2026-07-23 — exact Lean source check passed; post-proof literature audit found Bohr-transform
  parent theory but not the full signed family/scale universality statement.
