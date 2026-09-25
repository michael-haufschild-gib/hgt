# Cofinal three-prime Stokes holonomy at every nonzero grade

- **ID:** `stc-cofinal-triangle-holonomy-all-grades`
- **Stage:** 2-fully-proven (paper)
- **Type:** exact all-grade source obstruction and singular-correction threshold
- **Routes:** STC, Gamma-six/Sonin source lift
- **Status:** `[PROVED ON PAPER] [LEAN FORMALIZATION PENDING] [NOT AN RH PROOF]`

## Question

The canonical Sonin seam has pair coefficients of the form `a_p-a_q`, so its value around every prime triangle is zero. The existing [three-prime obstruction](stc-odd-curvature-three-prime-obstruction.md) proves that directly copying the analytic reflection-odd Stokes scalar into those coefficients fails near neutral grade. Does a different nonzero grade allow that direct gluing? The answer is no, and the failure grows along a cofinal third prime.

Let `c_pq(g)=routeRCrossPrimeStokesOddCurvature p q g` for primes `p<q`. Fix `p<q`, and for a third prime `r>q` set

```text
Ω_pqr(g) = c_pq(g) + c_qr(g) - c_pr(g).
```

## Theorem: cofinal holonomy

For every real `g≠0`, writing `a=|g|`,

```text
lim_(r→∞ through primes) Ω_pqr(g)/r^a
  = sign(g) [1/(1-p^(-a)) - 1/(1-q^(-a))].       (1)
```

The bracket is strictly positive. Thus `Ω_pqr(g)` has the sign of `g` and grows in magnitude like a positive multiple of `r^|g|` for every fixed nonzero grade. No one-prime potential can reproduce `c_pq(g)` on every ordered prime pair at any such grade.

The fixed `(3,5,7)` triangle from the earlier theorem has the opposite sign near `g=0`. Consequently, at each sufficiently small fixed positive grade the triangle defect changes sign as the third prime moves cofinally. The obstruction is a scale-dependent holonomy, not a removable global sign convention.

## Proof

It suffices to take `g>0`, because the corpus proves `c_pq(-g)=-c_pq(g)`. Put `x=g log(p)/2` and `z=g log(r)/2`. Both are positive. The definition of the regularized ratio uses `S(t)=sinh(t)/t`; cancellation gives the exact identity

```text
R_pr(g) = sinh(z)/sinh(x).
```

The polar identity in `RouteRCrossPrimeStokesCalkinPolarHandoff.lean` therefore reads

```text
c_pr(g) = -2 sinh(x+z)
             [sinh(z)/sinh(x) + sinh(x)/sinh(z)].         (2)
```

Equivalently, setting `P=p^g` and `R=r^g` and expanding the hyperbolic sines gives the exact rational normal form

```text
c_pr(g) = -(PR-1)(R-1)/[(P-1)R]
          -(PR-1)(P-1)/[(R-1)P].                         (2a)
```

All denominators are positive for `g>0` and `p,r>1`.

As `r→∞`, `z→∞` and `r^g=exp(2z)`. The elementary exponential formulas for `sinh` show

```text
sinh(x+z)/exp(z) → exp(x)/2,
sinh(z)/exp(z) → 1/2,
sinh(x+z)/(exp(2z) sinh(z)) → 0.
```

Dividing (2) by `r^g` gives

```text
lim c_pr(g)/r^g = -exp(x)/(2 sinh(x))
                   = -1/(1-p^(-g)).                     (3)
```

The fixed `c_pq(g)` disappears after division by `r^g`. Apply (3) once with `p` and once with `q` to obtain (1). Since `p<q` and `g>0`, `p^(-g)>q^(-g)`, so the displayed difference of reciprocals is positive. Oddness handles `g<0`.

## Necessary correction size

Suppose a proposed all-prime source calibration adds pair terms `B_pq(g)` so that `c_pq(g)+B_pq(g)=a_p(g)-a_q(g)`. Its triangle identity forces

```text
B_pq(g)+B_qr(g)-B_pr(g) = -Ω_pqr(g).           (4)
```

By (1), for every fixed `p<q` and `g≠0`, there are constants `C>0` and `R` such that every prime `r>R` obeys

```text
|B_pr(g)|+|B_qr(g)| ≥ C r^|g|.                 (5)
```

Indeed `B_pq` is fixed, and the triangle inequality applied to (4) absorbs it into half the asymptotic lower bound. In particular the two corrected prime rows cannot **both** belong to the reciprocal-Euler Hilbert space with norm `sum_r |B_ir|²/r`: by `(a²+b²)≥(a+b)²/2`, their combined squared tail dominates a constant times `sum_(r prime) r^(2|g|-1)`, which diverges by Euler's divergence of `sum_(r prime) 1/r`.

The correction required to make the literal analytic Stokes curvature a coboundary is therefore necessarily non-potential and non-Hilbert at the natural reciprocal-prime scale. This identifies a concrete singular price for the missing STC all-prime source lift. It does **not** exclude a different source calibration, a nonlocal singular operator, or a Sonin representation with cancellations. The canonical Xi seam still requires a source-derived complex phase and a cofinal Calkin estimate; neither follows from (1).

## Audit

- The exact source scalar, ratio and oddness are in `RouteRCrossPrimeStokesCalkinPolarHandoff.lean`; `RouteRCrossPrimeStokesFourChannelObstruction.lean` already proves the ratio simplification and near-neutral three-prime obstruction.
- The canonical pair-coboundary form is in `SoninPrimeSeamExteriorCalkin.lean`.
- The sharp source Hilbert chamber in [the Gamma-prime chamber theorem](stc-gamma-prime-hilbert-chamber.md) is consistent with (5); the present result concerns the **necessary correction** to an exact coboundary and holds at every nonzero grade.
- Deep corpus search was partial and returned the near-neutral theorem, but no all-grade cofinal triangle law. External priority is not claimed.
