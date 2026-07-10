# FID Shifted Hankel Strict Total Positivity

- **ID:** fid-shifted-hankel-strict-total-positivity
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), negative-control theorem for the proof route
- **Source:** random formula-graph node 53/100, `PS12` in `docs/consolidated/revision01/formulas-graph.md`
- **Statement:** The shifted FID Hankel matrix

```text
H_FID[i,j] = zeta(2(i+j)+3),  i,j >= 0,
```

is strictly Hankel totally positive: every minor with strictly increasing row and column indices is positive. Therefore even upgrading the FID certificate from principal Hankel PSD to all shifted Hankel minors still has no RH content; it remains positivity of the integer divisor, not positivity transfer to the zero divisor.

## Goal

Close a stronger false bridge than the already-retired "FID Hankel PSD implies RH" route. The formula `PS12` does not merely give a positive semidefinite Hankel tower. It gives a strictly totally positive shifted Hankel matrix. Thus an attempted repair that demands all shifted Hankel minors, rather than only principal minors, is still an integer-divisor certificate unless it proves a source-built integer-to-zero transfer.

## Gates

- [x] 0 -> 1 in-progress: random formula selected and checked against prior FID work
- [x] 1 -> 2 fully-proven: Cauchy-Binet/Vandermonde proof complete
- [ ] 2 -> 3 formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: fold into the FID negative-control section if needed

## Proof

[PROVED HERE]

From `PS12`,

```text
zeta(2k+1) = sum_{n>=1} (1/n) (1/n^2)^k.
```

Hence the shifted FID matrix is the Hankel moment matrix

```text
H_FID[i,j]
  = zeta(2(i+j)+3)
  = sum_{n>=1} (1/n^3) (1/n^2)^(i+j).
```

Let

```text
x_n = 1/n^2,       w_n = 1/n^3.
```

Then `x_n` are distinct positive points and `w_n > 0`. For strictly increasing row indices

```text
r_1 < ... < r_m
```

and column indices

```text
c_1 < ... < c_m,
```

Cauchy-Binet first applied to the truncation `1 <= n <= N` gives

```text
det[H_FID,N[r_a,c_b]]_{a,b=1}^m
 =
sum_{1 <= n_1 < ... < n_m}
  (prod_l w_{n_l})
  det[x_{n_l}^{r_a}]_{a,l=1}^m
  det[x_{n_l}^{c_b}]_{b,l=1}^m.
```

Letting `N -> infinity` is legitimate because each matrix entry converges to the corresponding zeta value and the determinant is a polynomial in the entries. The generalized Vandermonde determinants have the same orientation sign because the same ordered support points `x_{n_l}` occur in both determinants. Their product is positive. For every sufficiently large `N`, at least one `m`-tuple of support points exists, and every such summand is positive. Therefore every finite-truncation minor is positive and the limiting minor is a positive convergent sum.

Thus `H_FID` is strictly Hankel totally positive.

## Consequence For The Proof Route

This theorem strengthens the FID negative control. The obstruction is not that FID was checked with too weak a Hankel certificate. Even the all-minor shifted Hankel certificate is automatic from the integer divisor

```text
sum_{n>=1} (1/n^3) delta_{1/n^2}.
```

So the bridge cannot be:

```text
integer-side shifted Hankel total positivity -> RH.
```

It must be a source-built transfer theorem from the integer/prime divisor through the explicit formula to the zero reciprocal divisor, preserving the shifted square-test forms `Q_0` and `Q_1` there. In the proof-route language, abstract membership in a Stieltjes or Hankel-total-positive cone is not enough; the source measure has to be the completed zero divisor.

## Schur-Threshold Side Note

The original `PS12` measure

```text
mu = sum_{n>=1} (1/n) delta_{1/n^2}
```

has the same missing zeroth-moment disease as the reciprocal zero-divisor model:

```text
mu_0 = zeta(1) = infinity.
```

The general finite-`T_0` Schur-threshold theorem already proves that no finite `zeta(1)` replacement can make the full unshifted tower PSD at all orders. For this specific `PS12` measure, numerical thresholds satisfy

```text
a_d = b_d^T C_d^(-1)b_d = 2 log d + o(1)   [CONJECTURE; numerically stable to d=40].
```

This rate observation is not used in the theorem above. It explains why finite `zeta(1)` audits can look harmless for many low orders while still being invalid all-order objects.

## Computation

The script checks representative minors and records the `PS12` finite-part thresholds:

- `computations/2026-06-21-conway-ps12-strict-tp.py`
- `computations/2026-06-21-conway-ps12-strict-tp.txt`

## Log

- 2026-06-21 -- Conway: created from random formula-graph node 53/100 (`PS12`). Basic FID PSD and generic finite-`T_0` divergence were already prior work; the new node is the stronger all-minor negative control.
