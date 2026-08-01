# Square-aperture positive-excess convex duality

- **ID:** `square-aperture-positive-excess-convex-duality`
- **Stage:** `2-fully-proven`
- **Type:** `THEOREM (paper) / EXACT FINITE DUALITY`
- **Scientific status:** `[PAPER-PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Route:** Route I

## Definitions

Put

```text
d_m = W(m^2)-2(1-1/sqrt(2))m,
P_M = sum_(1<=m<=M) (d_m)_+^2.
```

For a real aperture weight `u=(u_m)` define

```text
D_M(u) = sum_(1<=m<=M) (2u_m d_m-u_m^2).
```

The admissible cone is `u_m>=0` for `1<=m<=M`.

## Exact theorem

For every `M` and every admissible `u`,

```text
D_M(u) <= P_M.                                           (1)
```

Equality holds for the canonical weight `u_m=(d_m)_+`. Consequently, for every real `B`,

```text
P_M <= B  iff  for every admissible u, D_M(u) <= B.      (2)
```

If

```text
A_u(k)=sum_(1<=m<=M) u_m 1_{m^2/2<k<=m^2},
```

finite Fubini gives the exact source-facing expansion

```text
D_M(u)
 = 2 sum_(k<=M^2) Lambda(k)A_u(k)/sqrt(k)
   -4(1-1/sqrt(2)) sum_(m<=M) m u_m
   -sum_(m<=M)u_m^2.                                    (3)
```

There is also an exact defect decomposition. With `x_+=max(x,0)` and `x_-=max(-x,0)`,

```text
x_+^2-(2ux-u^2)=(u-x_+)^2+2u x_- .                     (4)
```

Therefore every admissible aperture weight satisfies

```text
P_M-D_M(u)
 = sum_(m<=M) ((u_m-(d_m)_+)^2+2u_m(d_m)_-).            (5)
```

This identifies both losses exactly: squared distance from the canonical positive optimizer and
weight spent on negative-deviation apertures.

The dual is also exactly normalized into Route I's pre-existing sharp source coefficient. At the
square logarithmic sample put

```text
S_m = dyadicSharpPrimeSourceCoefficient(m^2).
```

The sharp-source identity gives `S_m=-2d_m`, hence

```text
D_M(u)=sum_(m<=M)(-u_m S_m-u_m^2),
4P_M=sum_(m<=M)(S_m^-)^2.                                (6)
```

Thus this is not a new route or a rectangular/C2 normalization: it is the exact one-sided Hilbert
dual of Route I's existing sharp-source negative part, restricted to square apertures.

### Proof

For real `x` and `u>=0`, split on the sign of `x`. If `x>=0`, then

```text
x^2-(2ux-u^2)=(u-x)^2>=0.
```

If `x<0`, then `2ux-u^2<=0=(x_+)^2`. Thus

```text
2ux-u^2 <= (x_+)^2.
```

in both cases. For `u=x_+`, equality holds in the scalar inequality. Sum it over the finite
aperture set to obtain `(1)`, and use the canonical weight for the reverse implication in `(2)`.
Expanding `d_m`, exchanging the two finite sums, and collecting the deterministic terms proves
`(3)`. Identity `(4)` follows by substituting `x=x_+-x_-`, using `x_+x_-=0`, and expanding;
finite summation gives `(5)`.

## Route-I consequence

The surviving one-sided source conjecture is

```text
for every delta>0, P_M=O_delta(M^(1+delta)).             (7)
```

By `(2)`, `(7)` is exactly a uniform family of nonnegative-aperture inequalities, not a full
centered pair variance. Existing square-energy sampling proves `(7)` implies RH. Conversely,
Schoenfeld's RH bound gives `d_m=O(log(m)^2)` and therefore `(7)`, so `(7)` is still an exact
RH-strength endpoint. The gain is representational: negative prime-window deviations disappear,
and every attempted source proof must now control the explicit dual linear prime functional.

## Hostile audit

- Full square correlation was stronger than needed because it paid for both signs of `d_m`.
- Scalar analytic-response no-go does not apply: the dual varies an entire nonnegative aperture
  vector and is coefficient-nonlocal.
- Retired C2 does not own this functional: no completed Xi response or horizontal-modulus
  coordinate appears.
- Route E does not own it: no Möbius or squarefree coefficient occurs.
- A positive Selberg-sieve majorant with a density constant strictly above one leaves a main-term
  surplus of order `sum m u_m`; such a certificate cannot prove `(7)`. Any live proof must beat
  that parity-barrier loss through signed correlation or an equally sharp source mechanism.
- Any fixed finite preset test family has a nonzero dual defect on sufficiently large positive
  coordinate rays: its dual values grow at most linearly in the ray parameter, whereas `P_M`
  grows quadratically. Thus finite-mode testing cannot replace the full nonnegative aperture cone
  without an arithmetic theorem restricting the actual deviation vector.

The theorem `(1)`--`(6)` is elementary convex duality and source normalization, not scientific
novelty. Estimate `(7)`
remains the exact `[OPEN CORE]`.

## Gates

- [x] full-square failure converted into a one-sided representation constraint
- [x] scalar dual inequality dependency-closed
- [x] finite aperture duality dependency-closed
- [x] exact optimizer identified
- [x] exact optimizer-defect decomposition
- [x] route-collision audit
- [x] exact Lean formalization
