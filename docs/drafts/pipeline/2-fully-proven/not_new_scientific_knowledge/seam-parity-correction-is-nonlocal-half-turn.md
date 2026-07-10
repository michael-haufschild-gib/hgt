# Seam Parity Correction Is A Nonlocal Half-Turn

- **ID:** seam-parity-correction-is-nonlocal-half-turn
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / source-transfer routing
- **Grade:** BRIDGE / guardrail. Door-2 reduces the proof to elementary
  polynomial algebra and the pullback `z -> -z`.
- **Source:** `finite-order-local-frequency-operators-not-markov.md`;
  `sigma-parity-fe-weld.md`;
  `seam-log-markov-pick-rh-equivalence.md`
- **Statement:** The coefficient parity needed to reverse the FE-even
  alternating seam signs is the half-turn pullback `Hf(z)=f(-z)`. It is not a
  finite-order local operator `q(D)` in the Euler operator `D=z d/dz`.

## Setup

Work on formal power series or polynomials in one variable `z`. Let

`D=z d/dz`.

Then each monomial is a degree eigenvector:

`D z^k = k z^k`.

A finite-order local degree-diagonal operator has the form `q(D)` for a real
polynomial `q`, and acts by

`q(D) z^k = q(k) z^k`.

Let `H` be the half-turn pullback

`Hf(z)=f(-z)`.

Then

`H z^k = (-1)^k z^k`.

## Theorem

There is no real polynomial `q` such that

`q(D)=H`

on all monomials.

Equivalently, exact coefficient parity is not finite-order local in `D`.

## Proof

If `q(D)=H` on all monomials, then

`q(k)=(-1)^k`

for every `k>=0`.

In particular, `q(2n)=1` for every `n>=0`. Thus the real polynomial `q(X)-1`
has infinitely many roots, so `q=1`.

But then `q(2n+1)=1` for every `n`, contradicting the required value
`q(2n+1)=-1`.

Therefore no such polynomial `q` exists.

The operator that does supply the parity is the half-turn `H`. Formally it is
`exp(i*pi D)` on the degree decomposition, but this is an infinite-order /
nonlocal pullback, not a finite polynomial in `D`.

## Consequence For The Seam-Log Markov Route

`finite-order-local-frequency-operators-not-markov.md` proves that polynomial
degree-symbol corrections cannot move a positive FE-even frequency source into
the Markov cone. This theorem identifies the missing operation in that
coefficient-diagonal model: the required parity comes from the global involution
`z -> -z`.

Thus a candidate source proof has two options:

1. explicitly construct a nonlocal half-turn / FE-involution mechanism from the
   completed Euler-Gamma source; or
2. leave the coefficient-diagonal frequency model entirely and prove positivity
   through a multiplicative, all-order, or boundary-index object.

A proof that stays inside finite-order `q(D)` local corrections cannot supply
the parity.

## Boundary

This theorem does not prove that the half-turn itself gives Markov positivity.
It only states the algebraic route condition: parity correction is nonlocal in
the seam-square coordinate. The source proof still has to show that the actual
completed object lands in the positive Markov/Pick cone after the full
interaction is applied.

## Theatre Test

For a proposed source correction:

1. Does it claim to repair the FE parity while remaining a finite polynomial in
   `D=z d/dz`?
2. If yes, it cannot equal the parity operator on all degrees.
3. If it invokes the half-turn `z -> -z`, where is that involution built from
   Euler/Gamma/FE data rather than imposed after reading the target cone?
4. If it leaves coefficient-diagonal operators, what replaces the Markov
   positivity proof?

## Novelty Status

The algebra is elementary. The significance is routing: it names the nonlocal
operation forced by the finite-order obstruction and prevents local `D`-operator
language from concealing the same failed transfer.

## Gates

- [x] 0 -> 1 in-progress: parity correction isolated from the finite-order
  local-operator no-go.
- [x] 1 -> 2 fully-proven: polynomial impossibility proof written.
- [ ] 2 -> 3 formalized: optional polynomial-root proof plus monomial action.

## Log

- 2026-06-24 -- Codex: created as the constructive routing companion to
  `finite-order-local-frequency-operators-not-markov.md`.

## 2026-06-24 half-turn is not sufficient for Markov positivity

`half-turn-repaired-frequency-not-markov.md` gives the next gate. The half-turn supplies the missing coefficient parity, but for a single positive FE-even frequency the repaired moments still have first shifted determinant `-7 B^2 lambda^8/360<0`.

Thus this card names a necessary nonlocal operation in the coefficient-diagonal model, not a sufficient proof of Markov/Pick positivity.
