# Cofinal typed obstructions in the identity bigraded model

- **ID:** cofinal-typed-obstruction-identity
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** proposition-interface discharge audit
- **Statement:** The constant bigraded rational module with identity twisted component in every weight has nonzero bundled typed obstructions cofinally.

## Goal

Realize `HasCofinalNonzeroBundledTypedObstructions` without importing any analytic conjecture, while
preserving the existing sharp law that finite vertical amplitude forbids such cofinality.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, explicit identity-model attack
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `hasCofinalNonzeroBundledTypedObstructions_identityRational`, final umbrella build and axiom audit pending
- [ ] 3 → 4  publication-ready

## Corpus and literature audit

`scripts/formal_tools.py research` found only the predicate, its finite-amplitude no-go, and the
general obstruction/Bianchi calculus in `TateFractureObstructionBianchiAmplitudeLaw.lean`. No prior
model realizes the cofinal predicate. This is an internal algebraic connector; external literature
is not needed because the proof reduces to composition of identities and a finite antidiagonal.

## Approach and proof

Let `A(p,q)=ℚ` as a bundled `ℚ`-module for every bidegree, and let every twisted component `D_r`
be the identity. For `r+s=n`, the transported composite `D_r D_s` is again the identity. Therefore,
for every `n`, every bidegree, and the vector `1`,

`O_n(1) = ∑_{r+s=n, 1≤r, 1≤s} 1`.

If `2≤n`, the filtered antidiagonal contains `(1,n-1)`. Every summand is the nonnegative rational
number `1`, so the sum cannot be zero. Hence `O_n ≠ 0`. Given any cutoff `c`, take `n=c+2`; then
`c<n` and `O_n≠0`. This proves cofinality. `[PROVED HERE]`

## Hypothesis stress and hostile review

- Characteristic zero is essential for this identity model: in positive characteristic, the number
  of positive decompositions can vanish modulo the characteristic.
- Constant bidegrees are essential to make every degree-shifting target definitionally the same
  module; this is an explicitly unbounded vertical-amplitude model, not a contradiction of the
  finite-amplitude no-go.
- The proof establishes an exact all-weight evaluation law first; cofinality is a corollary, not an
  isolated existential witness.
- No circular use of `HasCofinalNonzeroBundledTypedObstructions`, no `sorry`, and no external axiom.

## Log

- 2026-08-14 — corpus audit, explicit model, paper proof, and scratch Lean proof completed.
