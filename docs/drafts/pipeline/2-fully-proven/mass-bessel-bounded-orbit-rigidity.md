# Mass-Bessel bounded-orbit rigidity

**Stage:** 2 — fully proven on paper  
**Date frozen:** 2026-08-04  
**Label:** `[LOCAL-RESEARCH] [PAPER-PROVED]`  
**Origin:** positive survivor of the source-selected bounded-orbit conjecture

## 1. Exact theorem

Let `a>\lambda>0` and let `G_{a,\lambda}(u)` be the `L^2(\mathbb R)` Fourier
multiplier

\[
 \widehat{G_{a,\lambda}(u)f}(\xi)
 =\exp\!\left(-iu\sqrt{(\xi-i\lambda)^2+a^2}\right)\widehat f(\xi).
\]

Then

\[
 \sup_{u\in\mathbb R}\|G_{a,\lambda}(u)f\|_2<\infty
 \quad\Longleftrightarrow\quad f=0.
\]

Consequently every linear subspace on which all two-sided orbits are uniformly
bounded is `{0}`.

## 2. Proof

Write the principal square root as `p(\xi)+iq(\xi)`.  Because `a>\lambda`, its
real part is positive.  From

\[
 2p(\xi)q(\xi)=-2\xi\lambda
\]

we obtain

\[
 q(\xi)>0\ (\xi<0),\qquad q(\xi)<0\ (\xi>0),\qquad q(0)=0.
\]

The reverse implication is immediate.  For the forward implication, assume
`f\ne0`.  Plancherel makes `\widehat f` nonzero on a set of positive measure.
Since `{0}` is null, either its intersection with `{q>0}` or its intersection
with `{q<0}` has positive measure.

In the first case, countable exhaustion by

\[
 \{q\ge1/N\}\cap\{|\widehat f|\ge1/N\},\qquad N\ge1,
\]

provides an `N` for which the set has positive measure.  On it,

\[
 |e^{-iu(p+iq)}\widehat f|^2
 =e^{2uq}|\widehat f|^2
 \ge e^{2u/N}/N^2.
\]

Integration forces the norm to infinity as `u\to+\infty`.  The second case is
identical with `u\to-\infty`.  Thus no nonzero orbit is bounded in both time
directions.

## 3. Dependency ledger

- sign law for the imaginary part of the principal square root;
- Plancherel injectivity;
- a nonzero `L^2` function is nonzero on a positive-measure set;
- countable exhaustion of `{q>0}` and `{|\widehat f|>0}`;
- monotonicity of the integral.

No arithmetic or RH hypothesis enters.

## 4. Significance

The exact open core cannot be realized as stability of the completed arithmetic
state in the natural critical-gauge Hilbert space.  If the scalar trace is
bounded, its boundedness coexists with an unbounded internal orbit and is
created only after observation.

This separates two notions previously conflated in the route:

- **state stability:** impossible except for zero;
- **output stability:** exactly the arithmetic cancellation still open.

The distinction rules out positive energies, equivalent renormings, and
source-selected bounded invariant subspaces in one theorem.

## 5. Novelty audit

The measure-theoretic argument is elementary.  Exact bounded-orbit rigidity for
this prime-critical mass gauge was not found in the internal route or external
collision search, but it remains a local synthesis of standard multiplier
theory.  Label is `[LOCAL-RESEARCH]`, not `[NOVEL]`.

## 6. Lean target

Formalize in two layers:

1. the sign law `sign(q(\xi))=-sign(\xi)` for the complex mass square root;
2. an abstract measure-space theorem saying a multiplier orbit with a
   nonzero-sign real growth exponent has no nonzero two-sided bounded vector.

Status: `[PAPER-PROVED]`; Lean module not yet written.
