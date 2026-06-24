# Finite-Degree Reciprocal Tests Are Height-Limited

- **ID:** finite-degree-reciprocal-tests-height-limited
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / finite-height guardrail
- **Source:** `fixed-rank-hankel-tests-do-not-imply-stieltjes.md`;
  `y-plane-quartet-minor-imaginary-defect.md`;
  `docs/consolidated/revision01/bridge-theorem.md`
- **Statement:** For any fixed finite degree, shifted reciprocal Hankel
  positivity is stable under sufficiently small non-real reciprocal conjugate
  pairs. Thus finite-degree positivity cannot exclude high off-line zeros.

## Setup

Let `B` be a positive real reciprocal bulk with moments

`L_k=sum_{x in B} M_x x^k`, for `k>=1`,

and assume the two shifted finite blocks

```text
B_d^(0) = [L_{i+j+1}]_{i,j=0}^d,
B_d^(1) = [L_{i+j+2}]_{i,j=0}^d
```

are positive definite. Let

`m_d=min(lambda_min(B_d^(0)), lambda_min(B_d^(1)))>0`.

Fix a multiplicity `mu>0`. For a non-real reciprocal atom `y`, add the
conjugate pair `y, conjugate(y)`, each with weight `mu`. Let the perturbed
moments be

`T_k=L_k+mu y^k+mu conjugate(y)^k`.

## Theorem

For every fixed `d`, there is `epsilon_d>0` such that, whenever

`0<|y|<epsilon_d` and `y` is non-real,

both perturbed shifted blocks

```text
H_d^(0) = [T_{i+j+1}]_{i,j=0}^d,
H_d^(1) = [T_{i+j+2}]_{i,j=0}^d
```

remain positive definite, while the perturbed reciprocal divisor contains a
non-real atom and therefore is not an RH divisor.

One explicit sufficient choice is any `epsilon_d<=1` satisfying

`2 mu (d+1) epsilon_d < m_d`.

## Proof

The perturbation in the `r`-shifted block, with `r=0` or `r=1`, has entries

```text
P_d^(r)(i,j)=mu y^(i+j+r+1)+mu conjugate(y)^(i+j+r+1).
```

For `|y|<=1`,

```text
|P_d^(r)(i,j)| <= 2 mu |y|^(r+1) <= 2 mu |y|.
```

Hence its Frobenius norm is bounded by

```text
||P_d^(r)||_op <= ||P_d^(r)||_F <= 2 mu (d+1)|y|.
```

If `2 mu (d+1)|y|<m_d`, then

```text
lambda_min(H_d^(r))
 >= lambda_min(B_d^(r)) - ||P_d^(r)||_op
 > 0
```

for both `r=0` and `r=1`. Thus both checked shifted blocks remain positive
definite.

Since `y` is non-real and has positive weight, the perturbed reciprocal divisor
is not supported on `R_+`. Therefore it is not an RH divisor. Equivalently, by
the all-order shifted moment determinacy/positivity criterion, some sufficiently
high square test must eventually detect the non-real pair, even though the
fixed degree `d` tests do not.

## Consequence For The RH Route

This theorem is the native reciprocal version of finite-prefix blindness. It
explains why high off-line defects can evade any prescribed finite Hankel audit:
in the reciprocal coordinate their moments are small in every fixed low degree.

Therefore a proof cannot be:

1. positivity of `H_d^(0),H_d^(1)` for a large but fixed `d`;
2. a finite determinant ladder without a uniform degree-to-height theorem;
3. a finite computation that does not include a source theorem forcing the
   all-order limit.

The live bridge remains all-order: a source-built relative Loewner or
boundary-Weyl sign theorem uniform in degree and height.

## Gates

- [x] 0 -> 1 in-progress: reciprocal finite-degree blindness isolated.
- [x] 1 -> 2 fully-proven: perturbation-norm proof written.
- [ ] 2 -> 3 formalized: finite Hermitian perturbation theorem.

## Log

- 2026-06-24 -- Codex: created after the monomial-tail no-go. This records the
  positive side of the same audit: finite reciprocal tests are stable under
  sufficiently high off-line pairs, so finite positivity is calibration only.
