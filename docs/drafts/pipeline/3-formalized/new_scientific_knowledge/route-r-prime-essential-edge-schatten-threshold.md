# Route R prime essential-edge Schatten threshold

- **ID:** `route-r-prime-essential-edge-schatten-threshold`
- **Stage:** 3-formalized
- **Type:** STRICT PRECLOSURE SOURCE OBJECT / SHARP SUMMABILITY THRESHOLD
- **Status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `prime-first-trace-essential-normal-bockstein.md`

## Frontier decision

Two tempting producer objects fail before construction.

1. `[KILLED: CIRCULAR]` A positive invariant trace on every exact centered conormal line is
   precisely the already-isolated invariant-gauge premise: invariance and nonzero finite weight
   force the line character to be unitary.  Calling the gauge a coefficient trace supplies no
   arithmetic proof of invariance.
2. `[KILLED: CIRCULAR]` A crossed-product vacuum coefficient is positive and invariant only after
   the centered action is compatible with the chosen involution.  On a conormal eigenvector this
   compatibility again forces the centered character to be unitary.  It cannot define the missing
   source involution without already solving the horizontal problem.

The noncircular survivor is the actual strict-preclosure edge before any trace is taken.

## Frozen object

For an ordinary prime (p), let (r_p=operatorname{farPrime}(p)), so
(p^2<r_p\le 2p^2).  Put

\[
\begin{aligned}
 a_p&=(\log p)\,\operatorname{primeHardyKernelMap}(w_{p,r_p})-e_1,\\
 b_p&=p\,\Pi_1^\perp
   \bigl(\operatorname{primeFirstTraceClock}(w_{p,r_p})-e_1\bigr)-e_2.
\end{aligned}
\tag{1}
\]

`[LEAN-PROVED] [PRIME_ESSENTIAL_EDGE_EXACT_SCHATTEN_THRESHOLD]`

> The all-prime correction (p\mapsto(a_p,b_p)) is square summable but not absolutely
> summable.  Hence the normalized essential graph is a canonical affine Hilbert--Schmidt
> section over all ordinary-prime actions, but it has no trace-class correction.

Equivalently,

\[
 \sum_p\|a_p\|^2<\infty,qquad
 \sum_p\|b_p\|^2<\infty,qquad
 \sum_p\|a_p\|=\infty.
\tag{2}
\]

## Paper-proof attack

Existing exact estimates give

\[
 \|a_p\|\le {4\over p},qquad
 \|b_p\|\le {2\over p}+{6\over p^2}\le {5\over p}.
\tag{3}
\]

Since (sum_p p^{-2}<\infty), both square sums in `(2)` converge.  The load-bearing lower
bound is not a norm estimate copied from the parent theorem; it is an exact retained coordinate.
The second Hardy coordinate of (a_p) is

\[
 a_p(2)=p\left(p^{-2}-r_p^{-2}\right)
       ={1\over p}-{p\over r_p^2}.
\tag{4}
\]

Because (r_p\ge p^2) and (p\ge2),

\[
 0<{3\over4p}
 \le {1\over p}-{1\over p^3}
 \le a_p(2)
 \le \|a_p\|.
\tag{5}
\]

Euler divergence of (sum_p1/p) then gives the third assertion of `(2)`.

## Scientific content

This is not another Xi reporter and not a scalar reformulation.  It constructs the first global
all-prime object from the literal vector-valued source-normal edge and determines its exact
regularization class:

```text
ordinary trace / determinant       impossible (not ell1)
det2 / Hilbert--Schmidt extension  admissible (ell2)
higher or arbitrary completion     unnecessary at first anomaly grade
```

Thus the regular Gamma determinant cannot be attached to this edge by an ordinary coefficient
trace.  The first possible global determinant is second-regularized, and its multiplicative
defect is necessarily a quadratic trace cocycle.  This narrows the still-open Wold--Gamma/BV
landing: it must identify that quadratic strict-preclosure cocycle with the singular BV first
trace before divisor specialization.

## Reflected modular Fisher threshold

The literal occupancy-Fisher representative

```text
F_t(p)=p^t * p/(p+1)^2
```

has a second, topology-selecting wall which was previously absent from the frontier ledger:

```text
1/4 * p^(t-1) <= F_t(p) <= p^(t-1),
Summable (p |-> F_t(p)^2) <-> t < 1/2,
Summable(F_t^2) and Summable(F_(-t)^2) <-> |t| < 1/2.
```

This falsifies the claim that both reflected twists define classes of one fixed `ell2/ell1`
completion throughout the Xi strip `|t|<1`.  The positive survivor is exact: the `ell1` phase
transition at `t=0` remains coefficient-faithful, but the comparison object must be graded over
variable ideals rather than a fixed Hilbert carrier.  This is an internal frontier correction;
prime-power summability itself is parent mathematics.

## Hostile falsifiers

1. Retire `(2)` if coordinate `(4)` is not the literal source deviation coordinate.
2. Retire the Hilbert--Schmidt conclusion if either bound in `(3)` is not uniform on actual
   ordinary primes.
3. Retire non-trace-classness if the far-prime subtraction cancels the (1/p) coordinate.
4. Do not infer an operator determinant merely from an `ell2` vector; a diagonal/operator
   realization must be constructed separately.
5. Do not claim RH: the theorem fixes the source extension category but supplies no annihilation
   or Xi-conormal landing.

## Novelty boundary

The distinction between trace class, Hilbert--Schmidt class, and the second regularized Fredholm
determinant is parent operator theory.  External audit confirms that `det2` is the standard
replacement for a Hilbert--Schmidt perturbation and carries a quadratic trace correction in its
product law.  New internal content is the exact arithmetic threshold `(2)`--`(5)` for the actual
prime first-trace essential edge.  Exact corpus search found no prior theorem asserting this
threshold.

## Gates

- [x] invariant-trace and crossed-product-vacuum shortcuts killed as circular
- [x] exact all-prime strict-preclosure correction frozen
- [x] complete paper proof of `(2)`
- [x] formalize exact coordinate, lower bound, square summability, and failure of absolute
  summability
- [x] construct diagonal Hilbert--Schmidt realization
- [x] identify its `det2` cocycle with the Wold--Gamma regular anomaly
- [x] identify the same relative class with the BV singular first trace
- [ ] source-to-Xi annihilation
- [ ] RH

## Lean realization

Module:

```text
formal/GaloisForLFunctions/RHTower/
PrimeFirstTraceEssentialEdgeSchattenThreshold.lean
PrimeFirstTraceEssentialEdgeReflectedIdealGrade.lean
```

Exact unconditional declarations:

- `primeFirstTraceEssentialSourceDeviation_apply_two`;
- `three_div_four_prime_le_norm_primeFirstTraceEssentialSourceDeviation`;
- `summable_norm_sq_primeFirstTraceEssentialSourceDeviation`;
- `summable_norm_sq_primeFirstTraceEssentialResponseDeviation`;
- `not_summable_norm_primeFirstTraceEssentialSourceDeviation`;
- `primeFirstTraceEssentialSourceDeviation_not_memℓp_one`;
- `primeFirstTraceEssentialEdgeCorrection`;
- `primeActivationOccupancyFisherDensity_bounds`;
- `primeActivationOccupancyFisherTwist_bounds`;
- `summable_sq_primeActivationOccupancyFisherTwist_iff`;
- `summable_sq_reflected_primeActivationOccupancyFisherTwist_iff`.

Verification:

- direct `lake env lean` on module: passed;
- targeted `lake build GaloisForLFunctions.RHTower.PrimeFirstTraceEssentialEdgeSchattenThreshold`:
  passed, 9071 jobs;
- module has no forbidden declarations; repository-wide formal lint currently stops on unrelated
  concurrently added modules missing from the `RHTower` umbrella (none is this module);
- axiom audit: `propext`, `Classical.choice`, `Quot.sound` only.
