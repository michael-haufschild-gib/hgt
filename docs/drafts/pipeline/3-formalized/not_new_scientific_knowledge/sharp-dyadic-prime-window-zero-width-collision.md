# Sharp dyadic prime-window source endpoint is exactly Xi zero width

- **ID:** `sharp-dyadic-prime-window-zero-width-collision`
- **Stage:** `3-formalized`
- **Type:** `THEOREM (paper) / ROUTE-I TERMINAL COLLISION / NOT NEW SCIENTIFIC KNOWLEDGE`
- **Statement:** for every `alpha>=0`, the eventual all-epsilon upper-power spectrum of the literal
  sharp dyadic von-Mangoldt window is equivalent to `XiZeroHalfPlaneBound alpha`.

## Statement

For `alpha>=0` and a fixed cutoff `N`, define

```text
SharpUpper(alpha,N) :=
  for every epsilon>0, there exists C_epsilon>=0 such that
  for every n>=N,

  W(n)
    <= 2(1-1/sqrt(2))sqrt(n)
       + C_epsilon n^(alpha+epsilon),
```

where

```text
W(n)=sum_(n/2<k<=n) Lambda(k)/sqrt(k).
```

Then

```text
XiZeroHalfPlaneBound(alpha)
  <-> exists N, SharpUpper(alpha,N).                         (1)
```

At `alpha=0`, `SharpUpper(0,N)` is definitionally the original Route I endpoint
`DyadicWeightedPrimeWindowSubpowerUpper N`. Therefore

```text
RH
  <-> exists N, DyadicWeightedPrimeWindowSubpowerUpper N.    (2)
```

This is not merely an RH-equivalence obtained by composing two black boxes. Equation `(1)` is a
quantitative width identity for every `alpha`: both sides recover the same rightmost Xi transverse
exponent.

## Proof

### Xi width implies sharp-window power upper

Assume `XiZeroHalfPlaneBound(alpha)`. If `0<=alpha<1/2`, the classical generalized von Koch theorem
at `theta=1/2+alpha` gives

```text
|psi(x)-x| = O(x^(1/2+alpha) log(x)^2).
```

For `x>=1`, maximize `u^2 exp(-epsilon u)` at `u=2/epsilon` to obtain

```text
log(x)^2 <= 4/(e^2 epsilon^2) x^epsilon.
```

Thus, for every `epsilon>0`,

```text
|psi(x)-x| <= C_epsilon x^(1/2+alpha+epsilon),  x>=1.        (3)
```

If `alpha>=1/2`, Chebyshev's unconditional `psi(x)=O(x)` bound gives `(3)` directly because
`1/2+alpha+epsilon>1`. Hence the forward implication holds for every `alpha>=0`, including the
trivial wider-than-strip range.

The exact Abel identity from
`square-aperture-positive-excess-zero-width-collision.md` gives, for `n>=2`,

```text
W(n)-2(1-1/sqrt(2))sqrt(n)
 = E(n)/sqrt(n)-E(n/2)/sqrt(n/2)
   +(1/2)[I(n)-I(n/2)],

I(X)=integral_1^X E(t)t^(-3/2)dt,
E(x)=psi(x)-x.
```

Writing `beta=alpha+epsilon>0`, equation `(3)` implies

```text
|I(X)| <= (C_epsilon/beta)X^beta
```

and hence

```text
|W(n)-2(1-1/sqrt(2))sqrt(n)|
 <= (2C_epsilon+C_epsilon/beta)n^beta.                      (4)
```

Dropping the lower half of `(4)` proves `SharpUpper(alpha,2)`.

### Sharp-window power upper implies Xi width

Assume `SharpUpper(alpha,N)` and suppose, for contradiction, that `xi(rho)=0` with

```text
rho.re > 1/2+alpha.
```

Choose

```text
epsilon=(rho.re-(1/2+alpha))/2>0.
```

The corresponding instance of `SharpUpper` is an eventual fixed-power upper bound with exponent
`alpha+epsilon`. The already formalized fixed-power Landau theorem gives

```text
rho.re-1/2 <= alpha+epsilon.
```

By the definition of `epsilon`, the right side is the midpoint between `alpha` and
`rho.re-1/2`, a contradiction. Thus every Xi zero satisfies

```text
rho.re <= 1/2+alpha,
```

which is `XiZeroHalfPlaneBound(alpha)`.

This proves `(1)`. At `alpha=0`, the formal endpoint predicate reduces syntactically to Route I's
subpower predicate. The standard Xi functional-equation symmetry identifies zero half-plane width
zero with RH, proving `(2)`.

## Exact collision and route disposition

Retired Route C2 already proves, for its theta/Hankel current,

```text
C2TailCone(alpha) <-> XiZeroHalfPlaneBound(alpha).
```

Combining this with `(1)` yields

```text
C2TailCone(alpha)
  <-> exists N, SharpUpper(alpha,N)
```

for every `alpha>=0`. Route I's literal source endpoint therefore measures exactly C2's divisor
width. It does not contain a narrower source invariant, a new cancellation law, or an
unconditional mechanism that drives width to zero.

Route I is terminal as an independent route. Reopening it requires a genuinely new arithmetic
theorem that proves width zero without assuming any equivalent Xi-width, continuation, or
horizontal-monotonicity premise. Renaming the generalized von Koch transfer as a source estimate
does not reopen it.

## Anti-theatre and novelty audit

- `[DEPENDENCY-CLOSED PAPER PROOF]` Generalized von Koch is the only external analytic theorem;
  exact Abel transfer and reverse fixed-power Landau argument are explicit.
- `[NEW INTERNAL INFRASTRUCTURE]` Lean now formalizes the parameterized pointwise spectrum, its
  Chebyshev-error transfer, and its reverse Xi-width theorem.
- `[NOT NEW SCIENTIFIC KNOWLEDGE]` Generalized von Koch classically equates PNT error exponent and
  rightmost zeta-zero exponent. Route C2 already owns the formal project coordinate for that width.
- `[NO UNCONDITIONAL RH CLAIM]` At `alpha=0`, the forward input is RH-strength. This theorem closes
  route identity, not RH.

Sources:

- J. Pintz, *On the remainder term of the prime number formula and the zeros of Riemann's
  zeta-function*, <https://doi.org/10.1007/BFb0099452>.
- L. Schoenfeld, *Sharper Bounds for the Chebyshev Functions theta(x) and psi(x). II*,
  <https://doi.org/10.1090/S0025-5718-1976-0457374-X>.
- *Encyclopedia of Mathematics*, “Distribution of prime numbers,”
  <https://encyclopediaofmath.org/wiki/Distribution_of_prime_numbers>.

## Formal certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/
  CCMGeneralizedVonKoch.lean
```

Closed declarations:

- `chebyshevErrorPowerSpectrum_of_xiZeroHalfPlaneBound`
- `xiZeroHalfPlaneBound_iff_exists_dyadicWeightedPrimeWindowPowerUpper`
- `riemannHypothesis_iff_exists_dyadicWeightedPrimeWindowSubpowerUpper`

The leaf also supplies the full parameterized Perron-contour, logarithmic-derivative, half-integer,
natural-cutoff, and real-variable Chebyshev estimates. Exact source check and exact leaf build pass
for `GaloisForLFunctions.RHTower.CCMGeneralizedVonKoch`. Axiom audit of all 22 new declarations
reports only `propext`, `Classical.choice`, and `Quot.sound`; no project axiom, `sorryAx`, opaque
oracle, unsafe declaration, or computation is used.

## Gates

- [x] parameterized pointwise source spectrum defined
- [x] classical width-to-Chebyshev input identified exactly
- [x] Abel transfer paper-proved
- [x] reverse fixed-power zero-width theorem paper-proved
- [x] every new downstream step formalized unconditionally
- [x] endpoint identified definitionally with Route I source predicate
- [x] exact all-width collision with retired C2
- [x] generalized von Koch formalized in Lean
- [x] closed all-width Lean biconditional
- [x] closed zero-width RH biconditional

## Log

- 2026-08-01 — all-width equivalence proved; Route I classified terminal by exact C2 collision.
- 2026-08-23 — generalized von Koch and both closed biconditionals formalized; card promoted.
