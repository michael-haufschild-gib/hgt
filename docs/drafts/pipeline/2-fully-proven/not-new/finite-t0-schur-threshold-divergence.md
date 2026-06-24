# Finite T0 Schur Threshold Divergence

- **ID:** finite-t0-schur-threshold-divergence
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/consolidated/gpt/proof-route.md`, sections 1, 2, 7, 8
- **Statement:** For a compact reciprocal Stieltjes model with infinite total mass but finite positive moments, no finite value of `T_0` can make the full unshifted Hankel tower PSD at all orders; the Schur thresholds for a finite `T_0` repair diverge.

## Goal

Close a possible false repair of the `T_0` obstruction. It is not enough to choose a large finite part for `T_0`: if the positive-order moments come from an infinite reciprocal divisor measure, every fixed finite `T_0` eventually violates some unshifted Hankel minor.

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, attack idea
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 -> 3 formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: standalone note if needed

## Proof

[PROVED HERE]

Let `mu` be a positive Borel measure supported in a compact interval `[0,R]`, with

```text
mu([0,R]) = infinity,
m_k = int y^k dmu(y) < infinity for every k >= 1.
```

Assume, for contradiction, that there is a finite `a` such that

```text
(a,m_1,m_2,...)
```

has all unshifted Hankel matrices PSD and is represented by a finite positive measure `nu` on `[0,R]`.

Then for every `k >= 0`,

```text
int y^k d(y nu)(y) = int y^(k+1) dnu(y)
                  = m_{k+1}
                  = int y^(k+1) dmu(y)
                  = int y^k d(y mu)(y).
```

Both `y nu` and `y mu` are finite positive measures on the compact interval `[0,R]`. The Hausdorff moment problem on a compact interval is determinate, so

```text
y nu = y mu.
```

On `(0,R]`, division by `y` gives `nu=mu`. But `nu` is finite while `mu` has infinite total mass on the reciprocal support. Contradiction.

Therefore no finite `a=T_0` can give an all-order PSD unshifted tower for these positive-order moments.

Equivalently, at finite order `d`, let `C_d=[m_{i+j}]_{i,j=1}^d` and `b_d=(m_1,...,m_d)^T`. When `C_d>0`, the leading unshifted block

```text
[[a, b_d^T],
 [b_d, C_d]]
```

is PSD only if

```text
a >= a_d := b_d^T C_d^(-1) b_d.
```

If the thresholds `a_d` were bounded, a finite `a` above their supremum would satisfy every finite PSD condition, producing the impossible finite extension above. Hence `a_d -> infinity`.

## Computation

For the toy reciprocal divisor `y_n=1/n^2` with unit weights,

```text
m_k = sum_{n>=1} y_n^k = zeta(2k),  k>=1.
```

The Schur thresholds are exactly

```text
a_d = d(2d+3)/2
```

for the tested symbolic range, and high-precision continuation follows the same values. Thus any chosen finite part fails at a predictable finite degree: `T_0^ren=50` fails by `d=7`, and `T_0^ren=500` fails by `d=22`.

Artifacts:

- `computations/2026-06-21-conway-t0-schur-threshold-divergence.py`
- `computations/2026-06-21-conway-t0-schur-threshold-divergence.txt`

## Route Consequence

The corrected proof route should not allow "choose a sufficiently large finite `T_0`" as a hidden alternative to the shifted theorem. A finite `T_0` may repair a bounded truncation, but all-order PSD forces the Schur threshold sequence to stay bounded, which is incompatible with infinite reciprocal mass.

The admissible all-order objects remain the shifted square tests:

```text
Q_0[p] = sum_{i,j} c_i c_j T_{i+j+1},
qquad
Q_1[p] = sum_{i,j} c_i c_j T_{i+j+2}.
```

## Log

- 2026-06-21 -- Conway: created as Step-12 follow-up to `reciprocal-seam-admissible-domain-q1`.
