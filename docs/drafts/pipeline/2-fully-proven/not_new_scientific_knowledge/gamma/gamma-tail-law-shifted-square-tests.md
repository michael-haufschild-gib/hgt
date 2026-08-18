# Gamma Tail Law For Shifted Square Tests

- **ID:** gamma-tail-law-shifted-square-tests
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/consolidated/revision01/bridge-theorem.md`, RNG-selected variable `gamma = Im rho`
- **Statement:** Let `p(y)=y^j q(y)` with `q(0) != 0`. The high-height tail of the reciprocal square test
  `Q_r[p]=sum_rho m_rho y_rho^r p(y_rho)^2`, with `r=1` for `Q_0` and `r=2` for `Q_1`, satisfies

```text
sum_{|gamma_rho|>G} m_rho |y_rho|^r |p(y_rho)|^2
  = O_{p,r}(G^(1-2r-4j) log G).
```

The exponent is sharp at the level of absolute tails. In particular, `Q_0` with `p(0) != 0` is the slow
tail bottleneck: `O(G^-1 log G)`.

## Goal

Turn the bridge theorem's height variable `gamma=Im rho` into a concrete square-test certificate. The
existing `T_0` obstruction proves positive reciprocal moments converge. This card records the sharper
tail law needed for finite audits and hard-edge regularized explicit-formula limits.

## Gates

- [x] 0 -> 1 in-progress: bridge-theorem variable selected by corrected RNG sample space
- [x] 1 -> 2 fully-proven: dyadic zero-count proof complete
- [ ] 2 -> 3 formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: fold into reciprocal-certificate section

## Proof

[PROVED HERE]

Write

```text
w_rho = rho - 1/2,        y_rho = -w_rho^(-2),        gamma_rho = Im rho.
```

For nontrivial zeros, `0 <= Re rho <= 1`, so for `|gamma_rho| >= 1`,

```text
|w_rho|^2 = (Re rho - 1/2)^2 + gamma_rho^2
```

is comparable to `gamma_rho^2`. Hence

```text
|y_rho| = |w_rho|^(-2) = O(|gamma_rho|^(-2)).
```

Let `p(y)=y^j q(y)` with `q(0) != 0`. Since `y_rho -> 0` as `|gamma_rho| -> infinity`, there is a constant
`C_p` such that, on the high tail,

```text
|p(y_rho)| <= C_p |y_rho|^j.
```

Therefore

```text
|y_rho|^r |p(y_rho)|^2
  <= C_{p,r} |gamma_rho|^(-2r-4j).
```

The Riemann-von Mangoldt zero count gives

```text
N(T+1)-N(T) = O(log T)
```

on unit intervals, or equivalently `N(T)=O(T log T)` with dyadic summation. Thus, for
`alpha=2r+4j > 1`,

```text
sum_{|gamma_rho|>G} m_rho |gamma_rho|^(-alpha)
  = O(G^(1-alpha) log G).
```

Substituting `alpha=2r+4j` gives the stated upper bound.

The exponent is sharp for absolute tails. Indeed, for large `|gamma|`,

```text
|y_rho|^r |p(y_rho)|^2
  = |q(0)|^2 |gamma_rho|^(-2r-4j)(1+O(|gamma_rho|^-2)),
```

and the Riemann-von Mangoldt asymptotic supplies `asymp G log G` zeros in dyadic height windows. Hence the
absolute tail has the same power of `G` and the same logarithmic factor.

Specialising:

```text
Q_0, j=0:  O(G^-1 log G),
Q_1, j=0:  O(G^-3 log G),
Q_0, j=1:  O(G^-5 log G),
Q_1, j=1:  O(G^-7 log G).
```

Each zero of `p` at the reciprocal hard edge `y=0` improves the tail by four powers of `G`.

## Computation

The exponent audit is archived at:

- `computations/2026-06-21-conway-gamma-tail-square-tests.py`
- `computations/2026-06-21-conway-gamma-tail-square-tests.txt`

It evaluates the smooth model integral

```text
int_G^infinity t^(-alpha) log(t) dt
```

for the relevant values `alpha=2r+4j`.

## Route Consequence

Finite reciprocal square-test certificates must report height-tail control, not just a finite zero cutoff.
The bottleneck is precisely the first shifted tower with a nonzero hard-edge value:

```text
Q_0[p], p(0) != 0: tail = O(G^-1 log G).
```

The second shifted tower and hard-edge-vanishing tests have much faster tails. This sharpens the
regularization requirement from `xf1-square-tests-outside-weil-class`: the bridge limit has to control the
slow `Q_0` high-height tail at the same time as the low-height hard-edge pole.

## Log

- 2026-06-21 -- Conway: created from corrected bridge-theorem RNG draw `63/78`, `gamma = Im rho`.
