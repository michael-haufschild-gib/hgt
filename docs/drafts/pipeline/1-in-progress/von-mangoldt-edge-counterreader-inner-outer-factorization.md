# Von Mangoldt edge-counterreader inner/outer factorization

- **ID:** `von-mangoldt-edge-counterreader-inner-outer-factorization`
- **Stage:** 1 — paper proof complete; Lean in progress
- **Parents:** `von-mangoldt-weighted-density-boundary-anomaly`, `SR-47`, `SR-48`
- **Type:** exact source-local cyclic-reader factorization / correction of conditional zero packet
- **Scientific status:** `[PAPER-PROVED] [LEAN-IN-PROGRESS] [ADVANCE]`
  `[EXTERNAL NOVELTY PROVISIONAL] [NOT RH]`
- **RH used:** no
- **Computation used:** no

## Correction that changes route

`SR-48` compactifies the locations that the full finite-aperture counterreader must vanish at
*if* its symbol continues past the relevant reciprocal clock. It does not prove that continuation.
Those nodes cannot be called unconditional zeros of the full reader.

The source current is nevertheless an additive sum of literal successor edges, while determinant
and cyclic readers turn direct sums into products. The correct object to factor first is therefore
one edge, not the nonlinear counterweight of the accumulated aperture.

## Universal source edge

Fix `0 < x < y` and the two-endpoint moment

```text
m(q)=y^q-x^q.
```

Let `c_0=1` and, for `n>=1`, let `c_n` be twice the canonical Hankel--Toeplitz counterweight. Its
opening law is

```text
sum_(r=0)^n c_r (y^(2n-r+2)-x^(2n-r+2))=0.             (1)
```

Put `u=x/y`, `e_n=c_n/y^n`, and

```text
D_n=sum_(r=0)^n e_r.
```

Equation `(1)` is exactly

```text
D_n=u^(2n+2) E_n,
E_n=sum_(r=0)^n e_r u^(-r).                            (2)
```

Using `(2)` at `n` and `n-1` gives, for `n>=2`,

```text
D_n/D_(n-1)=u^2(1-u^n)/(1-u^(n+2)).                    (3)
```

The first step is

```text
D_1=-u^3(1-u)/(1-u^3).                                 (4)
```

The product in `(3)` telescopes. For every `n>=1`,

```text
D_n=-u^(2n+1)(1-u)(1-u^2)
       /((1-u^(n+1))(1-u^(n+2))).                      (5)
```

This formula uses no sign assumption beyond `0<u<1`; all denominators are positive.

## Exact inner/outer split and exact radius

Let

```text
C(z)=sum_(n>=0)c_n z^n,
G(t)=sum_(n>=0)D_n t^n.
```

Since `e_n=D_n-D_(n-1)`, coefficient comparison gives

```text
C(z)=(1-yz)G(yz).                                      (6)
```

Moreover `(5)` yields

```text
D_n/u^(2n) -> -u(1-u)(1-u^2),
e_n/u^(2n) -> (1-u)(1-u^2)^2/u > 0.                    (7)
```

Therefore

```text
radius(C)=radius(G(y*·))=y/x^2,                         (8)
```

and `1/y<y/x^2`. Thus `(6)` proves an unconditional edge-reader zero at `z=1/y`; its first outer
singularity is the reflected clock

```text
lambda=x^2/y.                                          (9)
```

This saturates, rather than exceeds, the exact threshold needed by the prior descending-clock
argument to force the next zero. The missing outer factor is not an arbitrary analytic gauge.

## Von Mangoldt specialization

For every `n>=2` with `Lambda(n)>0`, the literal source edge has

```text
x=log n, y=log(n+1),
m_n(q)=(Lambda(n)/n)(y^q-x^q).
```

Nonzero scalar multiplication does not change canonical counterweights. Hence each active Euler
edge has exact factor

```text
C_n(z)=(1-log(n+1)z) G_n(log(n+1)z),                   (10)
```

with outer radius `log(n+1)/log(n)^2`. At prime edges, reciprocal-log Gamma transport sends the
unconditional inner zero to

```text
tanh(log(p+1))^2,
```

exactly the `SR-48` node. Thus `SR-48` becomes unconditional for the multiplicative edge-reader
packet, not for the accumulated nonlinear counterreader.

The reflected outer clock `log(p)^2/log(p+1)` lies strictly below `log p`; it is not literally the
`SR-47` projective node. This kills the proposed exact outer-factor equality. Positive survivor is
an exact two-scale collar: right-endpoint inner node plus reflected-left outer singularity. Its
cofinal displacement from the `SR-47` left node is the next source quantity to classify.

## Collision boundary

Corpus contains generic Hankel/Toeplitz counterweight recursion, finite signed atomic moments,
coefficientwise aperture convergence, and conditional endpoint-zero/capacity theorem. It contains
no two-clock formula `(3)`--`(9)` or edgewise von Mangoldt factorization `(10)`.

Targeted literature search found formal orthogonal-polynomial/Hankel--Toeplitz duality and generic
Padé/Schur theory, but no hit for recurrence `(1)`, telescoping law `(5)`, or von Mangoldt edge
factorization. Generic power-series factorization and radius theory are not novelty claims.

## Remaining falsifiers

1. Lean reindexing of existing opening law may not equal `(1)`.
2. Scaling by `Lambda(n)/n` may alter counterweights through a zero pivot.
3. Exact coefficient asymptotic `(7)` may fail at an endpoint.
4. Product of edge readers may not implement the already-proved accumulated cyclic trace.
5. The two-scale collar may retain no completed-Euler or reflection orientation.

Falsifiers 1--3 are paper-rejected and now require Lean. Failure of 4 must produce the precise
multiplicative anomaly; failure of 5 must classify the surviving collar invariant.

## Next theorem

Prove `(1)`--`(10)` unconditionally in Lean. Then derive the multiplicative anomaly between direct
sum of edge currents and accumulated Toeplitz countertrace. Exact vanishing of that anomaly, or an
exact completion term for it, is the required completed Euler cyclic-reader bridge.
