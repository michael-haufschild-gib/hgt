# Squared-Xi order-fourteen witnesses are confined to a compact window

- **ID:** squared-xi-order-fourteen-compact-witness-window
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4, fully unconditional) / RH-disproof route discriminator
- **Scientific status:** `[PROVED HERE] [NOVELTY UNAUDITED]`
  `[FORMALIZED IN LEAN, AXIOMS CLEAN, WINDOW SHOWN EMPTY]`
- **Sources:** `XiEndpointOffLineQuartetHeightGap.lean`; the genus-zero squared-Xi canonical product
- **Statement:** The first squared-seam order not protected by the reciprocal-square sector, derivative order fourteen, still has the RH-compatible strict sign for every `y>=8`.  Any order-fourteen RH-disproof witness must lie in `1/4<y<8`.
- **Formalized strengthening:** the sign holds for **every** `y>0`, so the compact window
  `1/4<y<8` is empty and no order-fourteen witness exists at all.

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

The paper argument confines the order-fourteen search to the compact symbolic
sign problem

```text
g^(14)(y) < 0 for some 1/4<y<8.                           (10)
```

The Lean formalization closes that window.  The shifted kernel
`mu_y = (A - b i)^{-1}` has `A = y + t` with `t = v - u > 0` at every Xi zero, so
`A > t` and every sector ratio `N b^2 < t^2` proved at `y = 0` holds a fortiori
at every `y > 0`.  The corner-exclusion sector for reciprocal-square power
fifteen is exactly such a ratio, hence `Re(mu_y^15) > 0` for every `y>0`, hence
`g^(14)(y) > 0` for every `y>0` and (10) has no solution.

## Gates

- [x] Off-line quartet height input already formalized.
- [x] Order-fifteen orbit angle bounded without zero computation.
- [x] Canonical-product assembly completed on paper.
- [x] First live derivative order confined to `1/4<y<8`.
- [x] Independent audit of product normalization and strict summation: both are machine-checked
  in `RHTower.SquaredXiCompleteMonotonicity`.
- [x] Lean formalization, unconditional and end to end.
- [x] 2 -> 3 formalized.
- [ ] 3 -> 4 publication-ready.

## Lean status

`formal/GaloisForLFunctions/RHTower/SquaredXiCompleteMonotonicity.lean`, axioms
`[propext, Classical.choice, Quot.sound]`.

- `RHTower.alternating_iteratedDeriv_squaredXiRadialField_pos_orderFourteen` —
  `0 < g^(14)(y)` for every `y > 0`, with no lower cutoff at all.
- `RHTower.re_xiShiftedReciprocalSquare_pow_fifteen_pos` — the atomwise input: the shifted
  order-fifteen reciprocal power is positive at every Xi multiplicity copy and every `y>0`.
- `RHTower.re_xiShiftedReciprocalSquare_pow_pos_of_sector`,
  `RHTower.xiCenteredSectorRatio_of_window_empty` — the shift-monotonicity of the sector ratio
  and its supply from an empty failure window; these are what remove the `y>=8` restriction.
- `RHTower.squaredXiRadialField_eq` — the identification of the formalized field with the card's
  `g(y) = xi'(1/2+sqrt y)/(2 sqrt y xi(1/2+sqrt y))`.

## Log

- 2026-07-31 — Formalized, and the compact window proved empty.  The card's `y>=8` came from
  re-deriving the angle bound at the shifted point with the crude estimate `b^2 = 4uv < v` and
  `A > v + 31/4`.  That is unnecessary: the shift is monotone in `A`, so the existing
  order-fifteen corner exclusion already gives the sign at every `y>0`.  The order-fourteen
  RH-disproof route is therefore closed rather than localized; the first unprotected squared-seam
  order is nineteen.  See `squared-xi-low-order-complete-monotonicity-protected.md`.

