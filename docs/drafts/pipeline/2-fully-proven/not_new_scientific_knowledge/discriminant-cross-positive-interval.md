# Discriminant Cross Positive Interval

- **ID:** discriminant-cross-positive-interval
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / route guardrail
- **Source:** `discriminant-bulk-cross-sign-needs-scale-separation.md`;
  `docs/consolidated/revision01/bridge-theorem.md`
- **Statement:** The degree-one discriminant cross term has an exact positive
  range. Scale separation is not a slogan: it is the exclusion of one explicit
  interval on the positive real axis.

## Setup

Let

`y=u+iv`, with `u>0` and `v!=0`,

and let `x>0` be a positive real bulk atom. Define

`C_y(x)=Re(y(y-x)^2)`.

Put `a=|v|` and `r=|y|=sqrt(u^2+a^2)`, and set

```text
x_-(y) = (u^2-a^2-ar)/u,
x_+(y) = (u^2-a^2+ar)/u.
```

## Theorem

The cross term factors as

```text
C_y(x)=u(x-x_-(y))(x-x_+(y)).
```

Moreover `x_+(y)>0`, and `x_-(y)>0` if and only if
`u>sqrt(3)a`. Therefore, on the positive real axis:

1. if `u>sqrt(3)a`, then `C_y(x)>0` exactly for
   `0<x<x_-(y)` or `x>x_+(y)`, while `C_y(x)<0` for
   `x_-(y)<x<x_+(y)`;
2. if `0<u<=sqrt(3)a`, then `C_y(x)<0` exactly for
   `0<x<x_+(y)`, while `C_y(x)>0` for `x>x_+(y)`.

The bad interval is therefore explicit. A termwise bulk-domination proof must
show that the relevant positive real atoms avoid it, or must replace termwise
positivity by a summed estimate.

## Universal Scale Bound

For every such `y`,

```text
x_+(y) <= C_* |y|,
C_* = sqrt(2) 3^(3/4) (sqrt(3)-1)/2 < 1.18.
```

Consequently, the simple sufficient condition

`x >= 1.18 |y|`

implies `C_y(x)>0`.

## Proof

Expanding the real part gives

```text
C_y(x)
 = u((u-x)^2-a^2)-2(u-x)a^2
 = ux^2+2(a^2-u^2)x+u(u^2-3a^2).
```

This quadratic has discriminant

```text
4a^2(u^2+a^2)=4a^2r^2,
```

so its two real roots are exactly `x_-(y)` and `x_+(y)`. Since the
leading coefficient is `u>0`, the sign is positive outside the root interval
and negative inside it.

It remains only to record which roots lie on the positive real axis. The
numerator of `x_+(y)` is `u^2-a^2+ar`. If `u>=a`, this is positive. If
`u<a`, then `ar>a^2-u^2` because

```text
a^2(u^2+a^2)-(a^2-u^2)^2 = u^2(3a^2-u^2)>0.
```

Thus `x_+(y)>0` always. For `x_-(y)`, positivity requires
`u^2-a^2>ar`; after squaring the positive sides this is equivalent to

```text
(u^2-a^2)^2>a^2(u^2+a^2)
iff u^2>3a^2.
```

This proves the interval statement.

For the universal bound, write `s=a/r`, so `0<s<1` and
`u=r sqrt(1-s^2)`. Then

```text
x_+(y)/r = (1+s-2s^2)/sqrt(1-s^2).
```

The derivative has numerator

```text
(s-1)(2s^2+2s-1),
```

so the maximum on `[0,1)` occurs at `s=(sqrt(3)-1)/2`, with value

```text
C_* = sqrt(2) 3^(3/4) (sqrt(3)-1)/2
    = 1.1799596795709859175...
```

Thus `x_+(y)<1.18|y|`, and `x>=1.18|y|` gives `x>x_+(y)`, hence
`C_y(x)>0`.

## Consequence For The RH Route

This theorem supplies the missing meaning of "scale separation" in the
discriminant attack. For an off-line reciprocal atom `y`, a low verified
on-line bulk atom `x` has a positive cross term once `x>=1.18|y|`.

It does not prove positivity of any shifted Hankel determinant for `zeta`.
The determinant route still needs a full summed domination estimate, or a proof
that every tuple used in a proposed finite-range theorem keeps its bulk atoms
outside the explicit bad intervals above.

## Gates

- [x] 0 -> 1 in-progress: exact root interval isolated.
- [x] 1 -> 2 fully-proven: quadratic factorization, root signs, and universal
  scale bound proved.
- [ ] 2 -> 3 formalized: optional real-closed-field polynomial lemma.

## Log

- 2026-06-24 -- Codex: created after the discriminant bulk-cross audit. The
  theorem converts the phrase "scale separation" into an explicit interval and
  a usable sufficient bound.
