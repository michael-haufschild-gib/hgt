# APEX-B Proof Attempt: Faithful Positivity

Source: `docs/consolidated/08-conjectures-required.md` §3.

Claim status: `[OPEN CORE]`.

## Target Claim

Any one of the all-scale positivity forms proves RH:

```text
kappa_- = 0,
Q_W >= 0,
m_xi in N_0,
Hankel/Laguerre-Turan det H_d >= 0 for all d,t,
Omega >= Pi,
G5 unitary holonomy.
```

## Proof Attempt

The faithful-index route is the cleanest. Assume the completed carrier has an
integer negative-square index satisfying

```text
kappa_- = number of off-line conjugate zero pairs.
```

Then

```text
kappa_- = 0
<=> no off-line conjugate zero pairs
<=> RH.
```

This does not prove `kappa_- = 0`; it proves that the faithful index is the
right target. It also explains why measured positivity is too weak: an averaged
or density-level trace can miss a finite or density-zero set of off-line zeros,
while `kappa_-` cannot.

The local curvature route gives only a necessary detector. With

```text
Xi(t) = xi(1/2 + i t),
```

the logarithmic curvature identity is

```text
(log Xi)''(t) = sum_rho (1/2 + i t - rho)^(-2).
```

Under RH, every term is negative real away from zero ordinates. An off-line
same-height pair `1/2 +- a + i gamma` contributes

```text
2(a^2 - tau^2) / (a^2 + tau^2)^2,  tau = t - gamma,
```

which is positive for `|tau| < |a|`. Hence an off-line zero creates a local
convexity window. This supports detection, not confinement.

## Weakened Theorems Proved Here

**Theorem APEX-B-W1.** If the faithful index equality
`kappa_- = # off-line conjugate pairs` holds for the completed carrier, then
`kappa_- = 0` is equivalent to RH.

**Theorem APEX-B-W2.** An off-line same-height mirror pair creates a positive
local contribution to `(log Xi)''` near its ordinate.

Both proofs are the elementary arguments above.

## Attack As False

Low-degree positivity cannot prove the apex. The corpus already records that
the no-margin is sparse, migrating, and collective; local gap or curvature
controllers fail. Thus a proof of `d=2` concavity or finite-depth Hankel
positivity is not enough. The required object is all-degree and all-height.

## Where The Full Proof Fails

The missing line is:

```text
source-built completed object => kappa_- = 0
```

or equivalently an all-degree positivity theorem. Known RH-equivalent
criteria identify the target but do not supply a source-built reason it is
positive.

## Missing Input

1. Construction of the completed carrier without zero-feeding.
2. Proof its faithful negative-square index is the off-line zero count.
3. Proof the source construction forces the index to vanish.
4. A no-margin argument that does not rely on hidden spectral gap.
