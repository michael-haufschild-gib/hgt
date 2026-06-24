# Positive Stieltjes Pole Plus First Atom Is Insufficient

- **ID:** positive-stieltjes-pole-plus-first-atom-insufficient
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / proof-route guardrail
- **Source:** `pole-budget-does-not-imply-uvarov-repair.md`;
  `stieltjes-bulk-exterior-christoffel-monotonicity.md`;
  `n1-signed-bulk-exterior-monotonicity-fails.md`;
  `source-selector-repair-obligation-ledger.md`
- **Statement:** Even a positive Stieltjes moment bulk supported to the right of
  the pole and first-trivial-zero boundary points does not, by itself, make the
  pole deficit repairable by the first-trivial-zero atom with the zeta masses.

## Setup

Let `V=R[y]_{<=2}`. Define a positive atomic Stieltjes bulk

`B[p] = (1/5)p(0)^2 + (12/23)p(1)^2 + (1/21)p(2)^2`.

The support `{0,1,2}` lies to the right of both exterior boundary points

`-4 < -4/25 < 0`.

Let

`A[p] = B[p] - 4 p(-4)^2`.

This is the positive bulk minus the pole-channel atom with the zeta pole mass
`4`.

Let the first-trivial-zero repaired form be

`R[p] = A[p] + (4/25) p(-4/25)^2`.

## Theorem

The form `A` has exactly one negative square, but `R` is not positive
semidefinite.

Thus a proof cannot infer first-trivial-zero Uvarov repair from the data:

1. positive Stieltjes bulk supported to the right of both boundary points;
2. one negative pole-channel subtraction at mass `4`;
3. first-trivial-zero repair atom at mass `4/25`.

## Proof

The bulk form `B` is positive definite on `V`: a nonzero polynomial of degree at
most `2` cannot vanish at all three points `0,1,2`, and all three weights are
positive.

The form `A=B-4e_{-4}^*e_{-4}` is a rank-one negative perturbation of a positive
definite form. Hence `A` has at most one negative square.

Evaluate `A` on the constant polynomial `p=1`:

`B[1] = 1/5 + 12/23 + 1/21 = 1858/2415`.

Therefore

`A[1] = 1858/2415 - 4 = -7802/2415 < 0`.

So `A` has at least one negative square. Hence `A` has exactly one negative
square.

Now evaluate the repaired form `R` on the same constant polynomial:

`R[1] = 1858/2415 - 4 + 4/25`.

Since

`1858/2415 - 4 + 4/25 = -37078/12075 < 0`,

the repaired form `R` is not positive semidefinite.

This proves the claim.

## Consequence For The RH Route

`stieltjes-bulk-exterior-christoffel-monotonicity.md` proves a true monotonicity
statement for positive moment bulks. The present theorem identifies a separate
mass and visibility issue: a positive bulk plus the formal pole and first
trivial-zero boundary atoms does not force repair.

The actual completed carrier needs the prime finite part, the functional
equation, and the semilocal channel system. The first-trivial-zero atom alone is
too small to repair an arbitrary pole deficit, even when the rest of the bulk is
a positive Stieltjes moment form on the correct side of the boundary points.

Thus a non-mirror proof must prove the actual source inequality:

`M_triv,rest + R^P + (4/25)e_{-4/25}^*e_{-4/25} >= 0`,

or the equivalent full semilocal Schur/index statement. It cannot stop at the
formal archimedean pattern:

`positive Stieltjes bulk - 4e_{-4}^*e_{-4} + (4/25)e_{-4/25}^*e_{-4/25}`.

## Theatre Test

For any proof using the pole atom and first-trivial-zero atom:

1. Does the argument use the actual prime residual `R^P`, or only the formal
   locations and masses of the two archimedean atoms?
2. Does it prove positivity on the constant polynomial and the first-trivial-zero
   kernel before invoking a scalar threshold?
3. Does it survive the explicit positive-bulk countermodel above?
4. If not, it has not used the completed source data needed for repair.

## Source Boundary

This theorem is a finite positive-moment counterexample. It proves no statement
about zeta's actual carrier and no zero localization. Its role is to block a
proof pattern that promotes the archimedean pole/first-trivial-zero bookkeeping
to the repair theorem without the prime-source inequality.

## Gates

- [x] 0 -> 1 in-progress: positive-bulk pole-plus-first-atom shortcut isolated.
- [x] 1 -> 2 fully-proven: exact finite Stieltjes-bulk counterexample written.
- [ ] 2 -> 3 formalized: optional rational arithmetic and rank-one inertia
  lemma.

## Log

- 2026-06-24 -- Codex: created under the private RH continuation after testing
  whether the positive-bulk variant of pole-to-Uvarov transfer survived. It
  does not; the constant polynomial already witnesses failure for the displayed
  positive atomic bulk.
