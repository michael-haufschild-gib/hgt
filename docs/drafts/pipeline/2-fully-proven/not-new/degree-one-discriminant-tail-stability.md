# Degree-One Discriminant Tail Stability

- **ID:** degree-one-discriminant-tail-stability
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / route guardrail
- **Source:** `discriminant-cross-positive-interval.md`;
  `discriminant-bulk-cross-sign-needs-scale-separation.md`;
  `docs/consolidated/revision01/bridge-theorem.md`
- **Statement:** The degree-one shifted determinant has an exact finite-height
  stability criterion. A verified positive real bulk proves `det H_1>0` after
  a tail only when its determinant margin dominates an explicit tail error.

## Setup

Let a reciprocal divisor have absolutely convergent moments

`T_k = sum_z M_z z^k`, for `k=1,2,3`,

with positive multiplicities and conjugation symmetry. Split the divisor into a
positive real bulk `B` and a remaining tail `E`. Write

```text
L_k = sum_{x in B} M_x x^k,
E_k = sum_{z in E} M_z z^k,
eta_k = sum_{z in E} M_z |z|^k,
Delta_B = L_1 L_3 - L_2^2.
```

The full degree-one shifted determinant is

`Delta = T_1 T_3 - T_2^2`.

## Theorem A: Tail Stability

If

```text
Delta_B > L_1 eta_3 + L_3 eta_1 + 2 L_2 eta_2
          + eta_1 eta_3 + eta_2^2,
```

then `Delta>0`.

## Proof

Since `T_k=L_k+E_k`,

```text
Delta - Delta_B
 = L_1 E_3 + L_3 E_1 - 2 L_2 E_2 + E_1 E_3 - E_2^2.
```

Taking absolute values and using `|E_k|<=eta_k` gives

```text
|Delta - Delta_B|
 <= L_1 eta_3 + L_3 eta_1 + 2 L_2 eta_2
    + eta_1 eta_3 + eta_2^2.
```

The stated strict inequality therefore implies `Delta>=Delta_B-|Delta-Delta_B|>0`.

## Theorem B: One Conjugate Pair

Let the tail consist of one non-real conjugate pair

`y=u+iv`, `conjugate(y)=u-iv`, with `v!=0`,

each with multiplicity `mu`. Then

```text
Delta_{B plus pair} - Delta_B
 = 2 mu sum_{x in B} M_x x Re(y(y-x)^2)
   - 4 mu^2 |y|^2 (Im y)^2.
```

Thus the positive bulk contribution is exactly the sum of the cross terms
studied in `discriminant-cross-positive-interval.md`, while the pair carries
the local negative square from `y-plane-quartet-minor-imaginary-defect.md`.

## Proof

For one real bulk atom `(x,M_x)`, the pair-bulk contribution to
`T_1T_3-T_2^2` is

```text
2 mu M_x x Re(y(y-x)^2).
```

Summing over `B` gives the first term. The determinant of the pair alone is

```text
(mu y+mu conjugate(y))(mu y^3+mu conjugate(y)^3)
 -(mu y^2+mu conjugate(y)^2)^2
 = -4 mu^2 |y|^2 (Im y)^2.
```

Adding these two contributions proves the formula.

## Consequence For The RH Route

This theorem gives a legitimate replacement for the deleted termwise
`det H_1` proof. A finite-height proof can proceed by:

1. taking the verified on-line zeros as `B`;
2. bounding the absolute reciprocal tail by `eta_1,eta_2,eta_3`;
3. checking the displayed determinant-margin inequality.

That is a real proof obligation, not a phrase. It also does not prove RH. The
margin `Delta_B` is degree-specific; extending this method beyond `d=1` requires
degree-dependent determinant margins or a source theorem replacing the finite
tail estimate. The all-order bridge remains the source-built positivity problem.

## Gates

- [x] 0 -> 1 in-progress: degree-one summed repair isolated.
- [x] 1 -> 2 fully-proven: determinant perturbation and one-pair formulas proved.
- [ ] 2 -> 3 formalized: optional polynomial identity plus norm inequality.

## Log

- 2026-06-24 -- Codex: created after the cross-positive interval audit. The
  card converts the surviving finite-height `d=1` route into an explicit
  determinant-margin inequality and blocks the old termwise shortcut from
  re-entering as informal "bulk domination."
