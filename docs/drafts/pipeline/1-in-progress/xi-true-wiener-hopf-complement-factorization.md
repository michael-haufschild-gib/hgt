# True infinite Wiener–Hopf complement factorization

## Status

In progress. Source-pure, infinite, non-diagonal analytic repair.

## Frontier

Suzuki’s strongest unresolved step is global Pick/Loewner positivity of the
compound Xi Bezoutian. Recent Hardy transport code tries to expose its
anti-causal factor by splitting the full Xi canonical product into strict-right
and complementary factors.

Current complementary factor is defined by totalized pointwise division

`xiCanonicalProduct z / xiRightCanonicalProduct z`.

At every strict-right Xi zero both numerator and denominator vanish, so Lean
sets the quotient to zero. This gives a pointwise identity `0 = 0 * 0`, but not
the removable analytic quotient. Consequently current “Wiener–Hopf
factorization” cannot be differentiated across its own divisor and cannot
support a global Schur, Pick, or Julia argument.

## Conjecture C-WH-COMPLEMENT

For every genus-one indexed canonical product with reciprocal-square summable,
nonzero spectral points, and every predicate on its multiplicity index:

1. canonical products on predicate and complementary subtypes are entire;
2. full product equals predicate product times complementary product at every
   complex point;
3. each factor is nonzero away from its selected divisor.

For the Xi strict-right predicate this produces a genuine entire complement
factor. Multiplying it by the nowhere-zero Hadamard quotient gives an entire
source factor whose product with the strict-right factor is exactly `XiC`.
At a strict-right zero, genuine source factor is nonzero while current
totalized-division source factor is zero.

## Hostile falsifiers

- Infinite-product splitting may fail if subtype products are not independently
  multipliable.
- `Equiv.sumCompl` may reverse factor order or lose multiplicity copies.
- Complement may share a spectral value with strict-right subtype despite
  distinct multiplicity indices.
- Hadamard quotient may fail to be globally nonzero after removable filling.
- Old totalized quotient might accidentally agree with true complement at the
  divisor.

Each falsifier must be discharged in Lean without axioms, finite exhaustions, or
numerical evaluation.

## Scientific value if proved

This does not assert RH. It removes a genuine analytic defect exactly at the
infinite continuation wall and supplies the first valid global factor on which
the unresolved compound-Bezoutian positivity question can be posed. The
predicate-splitting theorem is universal and prevents the same totalized
division error for arbitrary canonical-product Wiener–Hopf decompositions.
