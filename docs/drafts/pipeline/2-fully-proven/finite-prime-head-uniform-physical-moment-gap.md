# Uniform physical moment gap for every finite prime core

- **ID:** L-PSRC-FPHG
- **Stage:** 2-fully-proven (paper theorem; Lean formalization open)
- **Type:** THEOREM (paper)
- **Routes:** L, PSRC; source comparison with the finite-prime divisor head
- **Statement:** One fixed finite physical cutoff retains a positive signed inverse-cube moment, and a positive synchronized dilation-correlation gap, uniformly over every processed prime core and every dilation.

## Source and theorem [PROVED HERE]

Let `U(x)=divisorContinuousUnitHead x` and, for a finite set `P` of primes, let

```text
H_P(x) = sum_(d | prod(P)) mu(d) sqrt(d) U(x/d).
```

The Lean corpus proves `U(x)=0` for `x<=1`, `0<=U(x)<=(3/5)sqrt(x)` for all `x`, and the core-uniform positive signed moment

```text
m := exp(-2 sum_(n>=1) n^(-3/2)) * integral_1^infinity U(x)/x^3 dx > 0,
integral_1^infinity H_P(x)/x^3 dx >= m.                 (1)
```

For `X>0`, put `T_P(X)=integral_X^infinity |H_P(x)|/x^3 dx`. Then, for `X>=1`, **uniformly in `P`**,

```text
T_P(X) <= 2/sqrt(X).                                    (2)
```

Consequently, for every `X >= max(1,(4/m)^2)` and every finite prime core,

```text
integral_1^X H_P(x)/x^3 dx >= m/2.                     (3)
```

The corresponding two-scale statement is stronger. For `A>=1`, set

```text
g_(P,A)(x) = H_P(x) + A H_P(x/A),
E_P(X) = integral_1^X H_P(x)^2/x^3 dx,
C_P(A;Y) = integral_1^Y H_P(Ax) H_P(x)/x^3 dx,
```

where an integral over an empty interval is zero. For every
`X >= max(1,(8/m)^2)`, uniformly in `P` and `A>=1`,

```text
integral_1^X g_(P,A)(x)/x^3 dx >= m/2,                 (4)
E_P(X) + C_P(A;X/A)/A >= m^2/4.                        (5)
```

These are finite-cutoff, source-side laws. Their cutoff is independent of the number, identity, and order of processed primes and of `A`.

There is also a cofinal completion statement. Define the pointwise finite full divisor head

```text
H_inf(x) = sum_(1<=d<=x) mu(d) sqrt(d) U(x/d).
```

If `P` contains every prime at most `X`, then `H_P(x)=H_inf(x)` for every `x<=X`. The same bound (2) applies to `H_inf`. Thus along any cofinal exhaustion of finite prime sets,

```text
integral_1^infinity |H_P(x)-H_inf(x)|/x^3 dx -> 0,      (5a)
sup_(A>=1) integral_1^infinity
  |g_(P,A)(x)-g_(inf,A)(x)|/x^3 dx -> 0.                (5b)
```

In particular the positive signed moment in (1) passes to the full divisor head. The corpus's exact finite Euler moment product and the absolutely convergent Euler product at `3/2` identify it as

```text
integral_1^infinity H_inf(x)/x^3 dx
  = (integral_1^infinity U(x)/x^3 dx) / zeta(3/2) > 0. (5c)
```

This is a source-faithful completion in the inverse-cube `L^1` topology; it asserts no critical-weight or quadratic-energy completion.

## Proof

At a physical coordinate `x>=1`, every divisor `d>x` contributes zero because `U(x/d)=0`. Every remaining divisor contributes at most `(3/5)sqrt(x)` in absolute value, since `sqrt(d) U(x/d)<=(3/5)sqrt(x)`. There are at most `floor(x)<=x` possible positive integers `d<=x`, independently of `P`. Therefore

```text
|H_P(x)| <= (3/5)*x^(3/2).
```

Integrating against `x^(-3)` gives the sharper `T_P(X)<=(6/5)/sqrt(X)`, hence (2). Equation (3) follows by subtracting (2) from (1).

The full signed moment of `g_(P,A)` is `(1+1/A)` times the moment of `H_P`, hence at least `m`. Its absolute tail above `X` is bounded by

```text
T_P(X) + A^(-1)T_P(X/A) <= 4/sqrt(X).
```

For `X/A>=1`, apply (2) to `X/A`. For `X/A<1`, `H_P=0` on `(-infinity,1]`, so `T_P(X/A)=T_P(1)<=2` and `2/A<2/X<=2/sqrt(X)`. This proves (4).

Weighted Cauchy–Schwarz on `[1,X]`, whose `dx/x^3` mass is at most `1/2`, now gives

```text
integral_1^X g_(P,A)(x)^2/x^3 dx >= m^2/2.
```

Changing variables in the two shifted terms expands the left side exactly as

```text
E_P(X) + E_P(X/A) + 2 C_P(A;X/A)/A.
```

Since `E_P(X/A)<=E_P(X)`, inequality (5) follows.

For the completion, every divisor contributing at `x<=X` has all prime factors at most `X`, giving literal equality of the two heads there. The pointwise `x^(3/2)` envelope proves (2) for `H_inf` as well. Outside `[1,X]`, use the two tails in (2) to bound (5a) by `4/sqrt(X)`. The scaled-tail calculation used for (4) bounds (5b) by `8/sqrt(X)`, uniformly in `A`. Sending `X` to infinity proves both limits and permits passage of the signed moment by absolute `L^1` convergence.

## Consequence and remaining source obligation

The full-clock prescribed-prime theorem in `MobiusDivisorPrescribedPrimeSelfCorrelation.lean` had a core-uniform positive gap but used eventual cutoff passage. Equations (3)–(5) supply a **single physical cutoff** for the synchronized moment and square, so this part of the passage no longer needs a core-dependent threshold.

The finite prescribed-prime correlation drop is not yet uniform. Expanding the actual insertion `H_(P union {p})(x)=H_P(x)-sqrt(p)H_P(x/p)` at cutoff `X` leaves a mixed term at cutoff `X/p` and an annular boundary term. Their cutoffs differ from the synchronized pair in (5); replacing them by (5) without the boundary term would be invalid. The next hard step is an exact bound on that retained signed annular term, uniform along a cofinal prime/core schedule. No RH conclusion follows from (2)–(5) alone.

More precisely, for a fresh prime `p` put `rho_P=squarefreeDensity * prod_(q in P) q/(q+1)` and `D_(P,p)(X)=rho_P C_P(p;X)-rho_(P union {p}) C_(P union {p})(p;X)`. Finite expansion and the substitutions `x=p*y` give the exact source identity

```text
D_(P,p)(X)
 = rho_P * p*sqrt(p)/(p+1) * [E_P(X)+C_P(p^2;X/p)/p^2]
   + rho_P/(p+1) * [C_P(p;X)-C_P(p;X/p)].          (6)
```

The first bracket differs from (5) by the signed annulus `C_P(p^2;X/p)-C_P(p^2;X/p^2)`; the second bracket is another signed annulus. Explicitly, after rescaling the first one, their combined contribution inside `rho_P/(p+1)` is

```text
integral_(X/p)^X H_P(p*x) * [H_P(x)+p^(3/2)*H_P(x/p)] / x^3 dx. (7)
```

Thus (5) supplies a core-independent positive main term in (6), while (7) is the exact **finite-clock boundary obligation**. This is an algebraic identity, with no positivity claim for (7).

**Corpus anchors:** `DivisorContinuousUnitMoment.lean` (`divisorContinuousUnitHead_eq_zero`, `divisorContinuousUnitHead_nonneg`, `integral_mobiusDivisorContinuousHead_moment_uniform_lower`); `DivisorContinuousHeadRegularity.lean` (`divisorContinuousUnitHead_le_sqrt`); `MobiusDivisorPrescribedPrimeSelfCorrelation.lean` (full-clock uniform plus gap and prescribed-prime drop). The new uniform tail and synchronized finite-clock statements are paper-proved here, not yet Lean-certified; corpus discovery was partial and external novelty has not been audited.
