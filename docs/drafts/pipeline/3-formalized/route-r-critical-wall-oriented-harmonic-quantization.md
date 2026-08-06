# Route R critical-wall oriented harmonic quantization

- **Stage:** 2-fully-proven
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED]`
- **Active claim:** `[PAPER-PROVED — ROUTE_R_CRITICAL_WALL_ORIENTED_HARMONIC_QUANTIZATION]`

## Exact claim

For the explicit reflected Gamma Bockstein

\[
  \beta_t(p)=F_{-t}(p)-F_t(p),\qquad
  F_t(p)=p^t\frac{p}{(p+1)^2},
\]

put

\[
  W_t(p)=p^{-|t|}\beta_t(p),\qquad h(p)=p^{-1}.
\]

Then:

1. `t = 0` implies `W_t = 0`;
2. `0 < t` implies `W_t + h ∈ ell^1(Primes)`;
3. `t < 0` implies `W_t - h ∈ ell^1(Primes)`;
4. `h ∉ ell^1(Primes)`.

Consequently, in the fixed first-trace corona,

\[
 [W_t]=
 \begin{cases}
   +[h],&t<0,\\
   0,&t=0,\\
   -[h],&t>0,
 \end{cases}
 \qquad [h]\ne0.
 \tag{QW}
\]

Under the diagonal tail--Roos realization, the same trichotomy holds for
`routeRPrimeGammaDampedBocksteinSequence |t| t`.

## Internal frontier

- `[CORPUS]` `primeGammaCofinalBocksteinMagnitude_factor` gives the exact reflected Fisher
  factorization.
- `[CORPUS]` `summable_primeGammaCofinalBocksteinDampedMass_iff` gives the sharp open safe cone
  `t = 0 or |t| < epsilon`.
- `[CORPUS]` `primeActivationOccupancyFisherDensity_harmonic_difference_bounds` gives
  `0 <= 1/p-F_0(p) <= 3/p^2`.
- `[CORPUS]` `routeRDiagonalTailRoosClass_eq_zero_iff_summable` identifies fixed-tail
  null-homology with literal `ell^1` membership.
- `[LOCAL-RESEARCH]` existing Route R work identifies zero-aperture continuation as the only
  remaining source producer. It does not classify the class at the moving first trace wall
  `epsilon=|t|`.

No exact local statement of `(QW)` was found. The all-order Schatten wall gives only power-order
bounds and membership thresholds, not the orientation-preserving quotient class.

## External frontier

- `[LITERATURE]` Fröberg's prime-zeta continuation and the classical Mertens theory identify
  `sum_p p^{-s}` as having a logarithmic singularity at `s=1`.
- `[LITERATURE]` Kawalec, *On the series expansion of the prime zeta function about s=1 and its
  coefficients* (arXiv:2603.21535), writes
  `P(s)=log(1/(s-1))+regular` near `s=1`.
- `[LITERATURE]` Roos's derived-limit theory supplies the general inverse-limit complex, but not
  this arithmetic diagonal-class computation.
- `[LITERATURE]` Schur's theorem for `ell^1` shows weak continuation would already imply norm
  continuation; it does not create the missing source boundary.

The exact Route R quantization appears to be an application-specific decomposition. Scientific
priority is not established; treat it as a new local bridge, not new scientific knowledge.

## Conjecture loop

### Attempt 1 — weak `ell^1` continuation

`[FALSIFIED — CIRCULAR]` Ask only for weak convergence of the safe-cone tails in `ell^1`.
Schur's property turns weak convergence into norm convergence. More directly, boundedness plus
coordinate convergence and Fatou already yields the desired `ell^1` endpoint. This renames the
RH-strength producer and supplies no source mechanism.

**Failure-driven replacement.** Do not cross the trace wall. Normalize at the first wall
`epsilon=|t|` and classify the surviving corona class.

### Attempt 2 — unoriented unit wall residue

`[FALSIFIED — INFORMATION LOSS]` Absolute values give the universal class `[h]` for every
`t != 0`, but erase which Gamma orientation dominates.

**Failure-driven replacement.** Retain the signed Bockstein. The resulting class is
`-sgn(t)[h]`, producing a three-valued oriented rank.

### Attempt 3 — oriented harmonic quantization

**Hostile verdict:** `SURVIVES PRELIMINARY ATTACK`.

- It does not assume class nullity, critical-line placement, or RH.
- It is not a restatement of the safe-cone threshold: it identifies the exact nonzero quotient
  class and its orientation.
- It does not itself prove RH. It changes the producer burden from zero-aperture `ell^1`
  continuation to annihilation of one universal oriented wall residue.
- It is coefficient-faithful and uses no divisor specialization.

## Paper proof

Write

\[
  F_0(p)=\frac{p}{(p+1)^2}.
\]

The exact Fisher estimate gives

\[
  0\le h(p)-F_0(p)\le 3p^{-2}.
  \tag{1}
\]

Hence `h-F_0 ∈ ell^1(Primes)`.

Suppose first that `t>0`. Since `|t|=t`,

\[
\begin{aligned}
 W_t(p)
 &=p^{-t}\bigl(p^{-t}F_0(p)-p^tF_0(p)\bigr)\\
 &=F_0(p)\bigl(p^{-2t}-1\bigr).
\end{aligned}
\]

Therefore

\[
  W_t(p)+h(p)=\bigl(h(p)-F_0(p)\bigr)+F_0(p)p^{-2t}.
  \tag{2}
\]

By `(1)`, `F_0(p)<=h(p)`. Thus

\[
  0\le F_0(p)p^{-2t}\le p^{-1-2t}.
\]

Because `-1-2t<-1`, the prime real-power series on the right is summable. Both terms on the
right of `(2)` are therefore in `ell^1`, proving `W_t+h ∈ ell^1`.

Now suppose `t<0` and put `u=-t>0`. Then `|t|=u` and

\[
\begin{aligned}
 W_t(p)
 &=p^{-u}\bigl(p^uF_0(p)-p^{-u}F_0(p)\bigr)\\
 &=F_0(p)\bigl(1-p^{-2u}\bigr).
\end{aligned}
\]

Consequently

\[
  W_t(p)-h(p)=-\bigl(h(p)-F_0(p)\bigr)-F_0(p)p^{-2u},
\]

and the same two summability estimates prove `W_t-h ∈ ell^1`.

At `t=0`, the two reflected Fisher coefficients coincide, so `W_0=0`.

Euler's prime-harmonic theorem gives `h ∉ ell^1`. Hence the class `[h]` is nonzero. Adding an
`ell^1` sequence does not change the quotient class, proving `(QW)`. The diagonal tail--Roos
statement follows from `routeRDiagonalTailRoosClass_eq_zero_iff_summable` applied to differences.

## Hostile proof audit

- Real powers are applied only to positive primes.
- In the positive orientation the signed class is `-[h]`; in the negative orientation it is
  `+[h]`. The signs were checked before passing to absolute values.
- The correction exponent is `-1-2|t|<-1` exactly because `t != 0`.
- No prime number theorem or asymptotic expansion is required; only prime-power summability and
  Euler's divergence are used.
- The theorem remains valid for every real `t`, stronger than the Xi strip needed by Route R.

`[PAPER-PROVED]` The exact claim is dependency-closed.

## Frontier delta

The first trace wall is not a continuum of unrelated obstructions. It carries one universal
prime-harmonic rank port with an orientation sign. Thus any source producer need only prove:

> the fixed-source-orientation Stokes/Cartier residue of the Xi-specialized critical-wall class
> is zero.

It no longer needs to construct an `ell^1` continuation through the whole forbidden aperture
interval. If the residue law is coefficient-faithful, `(QW)` forces the oriented rank to be zero,
hence `t=0`, after which the existing Route R Lean chain proves RH.
