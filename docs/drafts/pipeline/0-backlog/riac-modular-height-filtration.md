# Modular action with moving arithmetic cutoff

- **ID:** RIAC-modular-filtration
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** [RIAC](../1-in-progress/renormalized-intersection-arithmetic-counts.md), modular cells
- **Statement:** Construct a filtered modular action on primitive cusp coordinates and compare its cutoff boundary with actual prime faces.

## Discriminating obstruction

A nonempty finite subset of rational cusps cannot be preserved by translation
`x↦x+1`: iterating any rational cusp gives infinitely many distinct cusps.
On the projective rational line, translation can fix infinity, but inversion
sends infinity to zero. Thus a literal nonempty finite cusp set cannot carry
the full modular action by restriction. A finite quotient action is a different
construction and needs its own comparison with the prime complex.

## Positive target

Represent a cusp by a primitive pair `(a,b)` up to common sign, with height
`H(a,b)=max(|a|,|b|)`. For an integral matrix `g` of determinant one, put
`C(g)=max(|g₁₁|+|g₁₂|, |g₂₁|+|g₂₂|)`. The proposed exact filtration law is

`H(g(a,b))≤C(g)H(a,b)`.

Determinant one preserves primitivity; the inverse gives the reverse
comparison. Hence the action should map cutoff `B` into cutoff `C(g)B`,
with a controlled moving boundary. The cost is submultiplicative under
matrix composition. These elementary facts are a starting target for formal
cusp geometry, not a claimed new modular theorem.

## Missing arithmetic comparison

Prime-face height is a product of distinct primes. Cusp height belongs to
primitive integer pairs. No identification between these filtrations has
been constructed. The required comparison must preserve faces, boundary
maps and cutoff transitions, and distinguish Eisenstein from cuspidal data.
The existing `ThetaCuspHawkingBMCuspPeriodization` and `CuspOrbitIndex`
modules construct modular translations and orbit decompositions in the
upper half-plane; they do not provide that prime-face comparison.

No projective cusp action, filtration theorem or prime-cell equivalence is
formalized in this branch yet.
