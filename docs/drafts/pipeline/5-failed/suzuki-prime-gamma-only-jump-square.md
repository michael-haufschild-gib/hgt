# Failed Suzuki prime--Gamma-only jump square

- **ID:** `suzuki-prime-gamma-only-jump-square`
- **Stage:** 5-failed
- **Type:** FALSE PRODUCER / CENTRAL-TO-FULL-FREQUENCY EXTRAPOLATION
- **Status:** `[FALSIFIED] [POSITIVE SURVIVOR PAPER-PROVED] [NOT RH]`
- **Failed claim:** direct Neumann comparison channel cancels from the full affine-sewn source,
  so a prime--Gamma-only resolvent square can produce the jump Pick kernel
- **Positive survivor:**
  `../2-fully-proven/new_scientific_knowledge/suzuki-full-frequency-neumann-holonomy-survivor.md`
- **RH used:** no
- **Computation used:** no

## Killing theorem

For an odd compact source with characteristic `W`, the Xi-real normalized Neumann right-triangle
quotient is

```text
n_(a,W)(z)=-W'(0)sin(az)/(2zW(z)).                     (1)
```

If the full shifted response is `q_lambda=q_lambda^EG-lambda n_(a,W_lambda)`, affine sewing gives

```text
[beta q_alpha-alpha q_beta]/(beta-alpha)
 =[beta q_alpha^EG-alpha q_beta^EG]/(beta-alpha)
  +alpha beta sin(az)/(2z(beta-alpha))
    [W_alpha'(0)/W_alpha(z)-W_beta'(0)/W_beta(z)].      (2)
```

The last line is generally nonzero.  It vanishes identically only when the two projectively
normalized characteristics `W_lambda/W_lambda'(0)` coincide.  Actual finite resolvent shift is
projectively non-flat; the corpus already records its nonzero reflected tangent mechanism.

## Exact why the old argument failed

At the center, every simple odd characteristic satisfies

```text
n_(a,W)(z)=-a/(2z)+O(z).
```

The principal part is independent of `W`, so affine sewing cancels its residue.  The old argument
proved only this one Laurent coefficient and silently promoted it to equality of meromorphic
functions.  Formula `(2)` shows the first surviving coefficient is the difference of normalized
cubic characteristic curvatures.

## Representation lesson

Form shift is not merely an affine scalar gauge.  It changes the projective finite
characteristic.  Neumann comparison is invisible to central residue but visible to every higher
frequency through that holonomy.  A full-frequency factorization must use the coupled object

```text
prime--Gamma resolvent curvature + Neumann projective holonomy,
```

not either channel alone.

## Stronger replacement conjecture

For one curvature-recurrence-selected aperture and negative shift pair, define the explicit
holonomy correction `N_(alpha,beta)` by the last line of `(2)`.  The replacement producer is

```text
K_(m_EG)+K_(N_(alpha,beta))=B_(alpha,beta)^*B_(alpha,beta),
```

where `m_EG` retains the global Xi multiplier and the Euler--Gamma triangles but omits only the
explicit Neumann triangle.  The killing argument no longer applies because the discarded
projective term has been restored exactly.

## Positive survivor status

The full triangle, affine-holonomy, finite-resolvent tangent, and central-principal-part laws are
proved on paper in the positive-survivor card.  Exact algebraic and Pick-kernel connectors are
queued for Lean there.  No sign of the compensated sum and no RH conclusion is claimed.

## Log

- 2026-07-22 — prime--Gamma-only square killed by exact full-frequency Neumann triangle; stronger
  holonomy-compensated square selected.
