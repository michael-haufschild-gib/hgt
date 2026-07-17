# Squared-Xi order-fourteen witnesses are confined to a compact window

- **ID:** squared-xi-order-fourteen-compact-witness-window
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / RH-disproof route discriminator
- **Scientific status:** `[PROVED HERE] [NOVELTY UNAUDITED] [NOT FORMALIZED]`
- **Sources:** `XiEndpointOffLineQuartetHeightGap.lean`; the genus-zero squared-Xi canonical product
- **Statement:** The first squared-seam order not protected by the reciprocal-square sector, derivative order fourteen, still has the RH-compatible strict sign for every `y>=8`.  Any order-fourteen RH-disproof witness must lie in `1/4<y<8`.

## Theorem

For

```text
g(y) = xi'(1/2+sqrt(y)) / (2*sqrt(y)*xi(1/2+sqrt(y))),
```

one has

```text
g^(14)(y) > 0                                             (1)
```

for every `y>=8`.  Consequently a violation of the RH-necessary sign at
order fourteen can occur on the absolute Euler ray only when

```text
1/4 < y < 8,
```

equivalently `1/2<w` and `w^2<8` for `y=w^2`.

## Proof `[PROVED HERE]`

Let an off-critical Xi quartet have centered coordinates
`delta+i*gamma`, and put

```text
u = delta^2,
v = gamma^2,
t = v-u,
b = 2*delta*gamma.
```

The open critical strip gives `0<u<1/4`.  The formal four-copy endpoint
height theorem gives

```text
85 < v.                                                   (2)
```

At squared coordinate `y`, its conjugate squared-root pair contributes a
positive multiple of

```text
H(y) = Re(1/(t+y-i*b)).                                   (3)
```

Write `A=t+y`.  If `y>=8`, then

```text
A = v-u+y > v+31/4,
b^2 = 4*u*v < v.                                         (4)
```

For `v=85+h`, `h>0`, exact expansion gives

```text
(v+31/4)^2-100*v
  = 1641/16 + (171/2)*h + h^2
  > 0.                                                    (5)
```

Equations (4)--(5) imply

```text
b^2/A^2 < v/(v+31/4)^2 < 1/100.                          (6)
```

Set `mu=1/(A-i*b)`.  Since `A>0`,

```text
|arg(mu)| = arctan(|b|/A) < |b|/A < 1/10.                (7)
```

Therefore

```text
15*|arg(mu)| < 3/2 < pi/2,                               (8)
```

where the last inequality uses only `pi>3`.  Hence
`Re(mu^15)>0`.

Critical-line pairs have `b=0` and the same conclusion immediately.
Differentiating (3) fourteen times gives

```text
H^(14)(y) = 14! * Re(mu^15) > 0.                          (9)
```

The squared-Xi logarithmic derivative and all its derivatives are locally
normally convergent sums of these orbit contributions away from the squared
divisor.  Summing (9) proves (1).  `QED`

## Consequence for the live source attack

The order-fourteen search no longer has a far-right regime.  It is the
compact symbolic sign problem

```text
g^(14)(y) < 0 for some 1/4<y<8.                           (10)
```

Through `s=1/2+sqrt(y)`, this is a compact interval in the absolute Euler
half-plane, where the rational, digamma, and von Mangoldt source expansions
all converge.  Any proof of (10) must preserve the exact pole/Euler
cancellation; separating their large derivatives before cancellation is not
valid.

## Gates

- [x] Off-line quartet height input already formalized.
- [x] Order-fifteen orbit angle bounded without zero computation.
- [x] Canonical-product assembly completed on paper.
- [x] First live derivative order confined to `1/4<y<8`.
- [ ] Independent audit of product normalization and strict summation.
- [ ] Lean formalization only if this compactness theorem is reused by the final proof.

