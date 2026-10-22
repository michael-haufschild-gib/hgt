# Frankenstein strict-frontier exact-source integrability gate

- **Status:** paper proof complete; Lean formalization in progress
- **Question:** can CCM/Wold/BV regularity make the exact Route-U Christoffel source wall locally
  integrable and thereby contradict the false-RH strict-frontier phase?
- **Axioms:** none

## Heavy conjecture

At every physical strict frontier (y_n), the exact source observable

\[
 W_n(v)=\frac{S_n(v)}{16N_{n+1}(v)}
\]

should be locally (L^1), perhaps because (S_n) is a literal finite rational--Gamma minus
von-Mangoldt source expression and the other routes prove smoothness or bounded variation for
completed source responses.

If true, this would contradict the already-proved cofinal nonintegrable-wall phase forced by
(\neg\mathrm{RH}).

## Hostile proof attempt

The numerator regularity argument succeeds but the quotient argument fails sharply.

1. On a strict frontier, the preceding Hankel head remains positive definite.  To the right, the
   next block is positive definite.  Thus canonical inverse-Hankel admission varies continuously
   on every compact interval starting at the frontier.
2. The literal adaptive source numerator (S_n(v)) is therefore continuous, hence interval
   integrable, on every finite interval ([y_n,b]).
3. At the endpoint, however, the source does not vanish:
   (S_n(y_n)>0).
4. The newborn norm vanishes, (N_{n+1}(y_n)=0), and the frozen-null-vector Lipschitz estimate
   gives (N_{n+1}(v)\le C(v-y_n)).
5. Hence (W_n(v)\ge c/(v-y_n)) on a right germ, with (c>0).  It is not locally (L^1), and
   therefore cannot have bounded variation there.

This is an exact obstruction, not lack of analytic infrastructure.  Ordinary source smoothness,
CCM bounded variation, or Wold trace regularity cannot apply to the quotient across its endogenous
admission zero.

## New exact producer interface

Define `XiShiftedAllStrictFrontierSourceWallsLocallyIntegrable` to mean: for every occupied strict
frontier, the exact wall is interval integrable on at least one nontrivial right interval.

Then

\[
 \mathrm{RH}
 \quad\Longleftrightarrow\quad
 \text{every occupied strict-frontier exact source wall is locally integrable}.
\]

The forward implication is vacuous for the correct mathematical reason: RH makes every shifted
Hankel failure set empty.  For the reverse implication, false RH supplies an occupied strict
frontier; its positive numerator and linearly collapsing admission norm force a nonintegrable
(1/(v-y_n)) lower bound.

## Consequence for Frankenstein search

The viable cross-route theorem is not generic local integrability of completed sources.  It must
act before division and prove one of two genuinely RH-bearing facts:

1. **source annihilation:** (S_n(y_n)=0) on every would-be strict frontier; or
2. **admission noncollapse:** (N_{n+1}(y_n)>0), excluding the frontier.

The corpus already proves the opposite sign (S_n(y_n)>0) conditional on an occupied strict
frontier.  Therefore any successful CCM/Wold/BV bridge must exclude frontier formation, not smooth
away its pole after formation.

## Lean target

`GaloisForLFunctions.RHTower.XiShiftedStrictFrontierSourceWallIntegrabilityGate` formalizes:

- continuity and interval integrability of the exact adaptive source numerator on every compact
  right interval at an occupied strict frontier;
- the named all-frontier local-integrability predicate;
- its unconditional equivalence with `RiemannHypothesis`.
