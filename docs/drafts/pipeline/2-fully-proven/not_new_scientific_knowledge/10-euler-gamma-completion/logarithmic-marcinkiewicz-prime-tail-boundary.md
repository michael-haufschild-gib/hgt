# The first source-containing prime tail is logarithmic Marcinkiewicz

- **ID:** `logarithmic-marcinkiewicz-prime-tail-boundary`
- **Stage:** 2-fully-proven / not-new
- **Type:** theorem (paper), `[BRIDGE]`
- **Statement:** The logarithmic Marcinkiewicz quotient is the first natural weighted prime-tail
  model in this program that contains the unit Euler field while keeping finite prime changes
  non-dense.  Its normalized exponent characters have an exact right/line/left trichotomy.  The
  quotient supplies the missing tail class but does not supply a canonical dual zero-incidence
  functional.

## Critical tail space

For a complex prime field `b=(b_p)`, define

```text
||b||_M = sup_(X>=2) 1/log X *
            sum_(p<=X) (log p)/p * |b_p|.                 (1)
```

Let `M_log` be the Banach space of fields with finite norm, and let `M_0` be the closure of the
finite-support fields.  Explicitly,

```text
b in M_0  iff
  lim_(Y->infinity) sup_(X>Y) 1/log X *
    sum_(Y<p<=X) (log p)/p * |b_p| = 0.                   (2)
```

Indeed, the expression after the limit is exactly the norm of the tail obtained by deleting all
coordinates `p<=Y`.  Thus (2) is simply the closure criterion.

The finite-unit-invariant tail space is

```text
Q_log=M_log/M_0.                                          (3)
```

Every finite prime modification vanishes in `Q_log`.

## The zeta unit survives

For the unit field `one_p=1`, the prime number theorem and partial summation give

```text
sum_(p<=X) (log p)/p = log X + O(1).                      (4)
```

Hence `one` belongs to `M_log`.  On the other hand, after deleting any finite prime set, the tail
ratio in (2) tends to `1` as `X` tends to infinity.  Therefore

```text
[one] != 0 in Q_log,
||[one]||_(Q_log)=1.                                      (5)
```

This is precisely what every absolutely summable topology missed: the actual unit Euler tail is
present, while finite Euler changes do not approximate it.

## Point-character trichotomy

For a complex point `rho`, define the normalized prime character

```text
tau_rho(p)=p^(1/2-rho).                                   (6)
```

Write `beta=Re rho`.

### Right of the line

If `beta>1/2`, put `epsilon=beta-1/2>0`.  Then

```text
sum_p (log p)/p * |tau_rho(p)|
  = sum_p (log p)p^(-1-epsilon)<infinity.                 (7)
```

Thus truncations converge in `M_log`, so

```text
tau_rho in M_0,
[tau_rho]=0 in Q_log.                                     (8)
```

### On the line

If `beta=1/2`, then `|tau_rho(p)|=1`.  Equations (4)--(5) apply unchanged to every tail, giving

```text
tau_rho in M_log \ M_0,
||[tau_rho]||_(Q_log)=1.                                  (9)
```

Multiplication by the phase field `p^(-it)` is an isometry of `M_log` and `Q_log`, so every
critical-line ordinate has the same essential tail size.

### Left of the line

If `beta<1/2`, put `epsilon=1/2-beta>0`.  Partial summation with the prime number theorem gives

```text
sum_(p<=X) (log p)p^(-1+epsilon)
  asymptotic X^epsilon/epsilon.                           (10)
```

After division by `log X`, this tends to infinity.  Hence

```text
tau_rho notin M_log.                                      (11)
```

Combining (8)--(11):

```text
Re rho>1/2  -> [tau_rho]=0,
Re rho=1/2  -> [tau_rho] has norm 1,
Re rho<1/2  -> tau_rho is outside M_log.                  (12)
```

The FE-reflected character belongs to the same space simultaneously with `tau_rho` only on the
critical line.  This is a faithful static classifier of the base point, not yet a zero-incidence
theorem.

## Bounded dual readers are not the incidence object

The quotient (3) provides a nonzero source tail `[one]`, but it does not canonically pair that class
with a selected divisor point.  Hahn--Banach makes the distinction exact.  Since `[one]` is nonzero,
for every prescribed scalar `c` there exists a continuous linear functional

```text
Lambda_c in Q_log'  with  Lambda_c([one])=c.              (13)
```

There are therefore many topology-compatible readers of the unit tail, with arbitrarily assigned
values.  The tail space alone selects none of them.

At a zeta zero, analytic continuation does supply a canonical residue reader, but it is not a
bounded functional on all of `Q_log`.  Requiring an element of `Q_log'` was therefore too strong.
The card `prime-shift-residue-closability-criterion.md` constructs the resulting partial residue
functional explicitly.  Its correct ambient space is `M_0`, not `M_log`: all right-half shift
characters are vanishing tails, and their span together with `c00` is dense only in `M_0`.

Its graph is closable exactly when RH holds, but this follows from the general fact that a linear
functional vanishing on a dense subspace is closable exactly when it is zero.  Thus the source
incidence data splits into complementary layers:

```text
([one] in Q_log, global divisor Delta,
 graph of the canonical partial residue functional on M_0).                (14)
```

The missing RH statement is neither “the tail is nonzero” nor closure of the residue graph.  The
first is already (5), while the second is a tautological restatement of residue vanishing.  The
missing object is a nonlocal law coupling the nonzero quotient class `[one]` to the vanishing-tail
residue graph.

## Positive boundary and circularity test

Equation (12) shows why imposing simultaneous boundedness of a point character and its FE
reflection is circular: that membership condition is already equivalent to `Re rho=1/2`.

Equation (13) shows the complementary failure: merely asking for some continuous tail reader with
nonzero value is vacuous, because Hahn--Banach supplies one with any value.  Analytic continuation
does select a canonical reader on a dense domain in `M_0`, but its closability supplies no
independent force.  A valid constraint must relate that reader to the surviving quotient class
before any zero residue is assumed absent.

## Scientific status

This is `[BRIDGE]`, not new scientific knowledge.  The space is a standard Marcinkiewicz-type
sequence quotient, (4) and (10) are prime-number-theorem partial summation, and (13) is
Hahn--Banach.  The contribution is the exact interface it supplies after the joint-decoupling
theorem:

```text
summable coefficient tails: jointly dense and invisible;
Mertens-divergent tail: source class survives in Q_log;
right-half residue characters: confined to M_0;
canonical partial residue graph: constructed but graph closure is tautological;
nonlocal coupling of Q_log to the M_0 residue graph: missing.               (15)
```

The next scientifically admissible move is to construct or obstruct a canonical coupling between
the quotient source tail and the vanishing-tail residue graph, without a chosen Banach limit,
spectral operator, positivity criterion, or the desired critical-line membership condition.
