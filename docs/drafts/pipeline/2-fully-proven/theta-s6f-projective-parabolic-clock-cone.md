# Theta S6F projective parabolic clock cone

- **ID:** S6F-PD-PARABOLIC-CONE
- **Stage:** 2-fully-proven
- **Type:** POSITIVE SURVIVOR / TRAJECTORY LOCALIZATION
- **Source:** `../1-in-progress/theta-rank-three-projective-drift.md`
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED]`

## Statement

On the physical theta trajectory, put

```text
R = modular scale,
X = R^2,
z = positive modular-lambda clock,
v = normalized quasimodular drift.
```

For `0 < x < 137/2000`, all three strict inequalities hold:

```text
(13/32 + z^2/32) z < v,
v < (33/80 + z^2/12) z,
191/10 + (147/20) z^2 < X.
```

In particular `v/z < 21/50`. This strengthens the prior rectangular clock cone
`13/32 < v/z < 7/16` by retaining the scale--clock coupling discarded by a box enclosure.

## Dependency-closed proof

Existing unconditional source theorems give, on the stated interval,

```text
R > 0,                    X > 191/10,
0 < z < 3/10,             (13/32)z < v < (7/16)z,
A = X(1-z^2) < 96/5,      S = R(v-z),
z' = R(1-z^2),
v' = (3 + A/4 + S^2/3)/R,
R' = -(2/3) R S.
```

### Curved upper wall

Let

```text
G_u = (33/80 + z^2/12)z - v.
```

It vanishes at the modular seam. Differentiation gives

```text
R G_u' = X(13/80 + z^2/4)(1-z^2) - 3 - S^2/3.
```

The old lower wall and `v<z` imply

```text
S^2 = X(z-v)^2 < X(19z/32)^2.
```

Therefore

```text
R G_u' > X H(z^2) - 3,
H(t) = 13/80 - (461/15360)t - t^2/4.
```

For `0 <= t < 9/100`, direct rational comparison gives

```text
H(t) > H(9/100) > 30/191.
```

Together with `X>191/10`, this yields `G_u'>0`. Since `G_u(0)=0`, strict
monotonicity gives `G_u(x)>0`, proving the upper wall. Also

```text
33/80 + z^2/12 < 33/80 + (9/100)/12 = 21/50.
```

### Curved lower wall

Let

```text
G_l = v - (13/32 + z^2/32)z.
```

Again `G_l(0)=0`, and

```text
R G_l' = 3 - (5/32)A + S^2/3
           - (3/32)X z^2(1-z^2).
```

The curved upper wall gives `v/z < 21/50`, hence

```text
S^2 = X(z-v)^2 > X(29z/50)^2.
```

Since `841/7500 > 3/32` and `1-z^2<1`, the last two terms have strictly
positive sum. The remaining part is strictly positive because

```text
3 - (5/32)A > 3 - (5/32)(96/5) = 0.
```

Thus `G_l'>0`, and seam anchoring proves `G_l(x)>0`.

### Parabolic scale floor

Set

```text
G_X = X - 191/10 - (147/20)z^2.
```

From `R'=-(2/3)RS`, `S=R(v-z)`, and `X=R^2`,

```text
X' = (4/3) R X z(1-v/z).
```

The curved upper wall gives `v/z<21/50`, so

```text
(4/3)X(1-v/z)
  > (4/3)(191/10)(29/50)
  > 147/10
  > (147/10)(1-z^2).
```

Consequently `G_X'>0`. At the seam `z=0` and the already proved self-dual
scale floor gives `G_X(0)>0`; hence `G_X(x)>0`.

## Hostile audit and significance

- `[FALSIFIED]` Positive-Laplace/Vandermonde shortcut: the pointwise reflected source is not a
  positive Laplace mixture; the corpus already proves stronger finite-measure and atomic no-go
  theorems. The obstruction is category error: the theta source is a positive density whose
  bilateral Laplace transform is Xi, not itself a positive exponential mixture in displacement.
- `[PAPER-PROVED]` Parabolic cone survives exact vector-field attack. Every inequality above uses
  only already formalized source identities and strict rational inequalities; no computed value,
  coefficient table, enclosure, or new premise occurs.
- Scientific delta: scale, lambda clock, and quasimodular clock are no longer enclosed independently.
  The trajectory lies in a curved three-variable region, excluding artificial corners of the prior
  rectangular box. This directly sharpens the domain on which projective drift must be proved.
- The theorem does **not** prove projective-drift positivity or RH. Next hostile test is whether the
  exact substitutions `X=191/10+(147/20)z^2+s` and
  `y=13/32+z^2/32+h` reveal a short computation-free drift decomposition.

## Literature audit

Search date: 2026-08-29. Planat--Solé, *Second-Level Concavity of the Riemann Xi Kernel*
([arXiv:2608.19160](https://arxiv.org/abs/2608.19160)), uses a Jacobi autonomous phase space and a
polynomially sheared cone for a rank-two kernel inequality, but not these rank-three source clocks
or the displayed parabolic bounds. Salazar, *Order-Moment Transport and Hankel Determinants in
Special-Function Inequalities* ([arXiv:2606.31647](https://arxiv.org/abs/2606.31647)), supplies
positive-representation Hankel mechanisms, but its hypotheses do not hold for this pointwise
reflected theta-source displacement. Bounded primary-source search found no exact match; priority
remains unverified.

## Lean status

`[LEAN-PROVED]` in
`GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthProjectiveParabolicClockCone`.
The exact module build and `#print axioms` audit pass; principal theorems depend only on
`propext`, `Classical.choice`, and `Quot.sound`. No computational result occurs in the module.
