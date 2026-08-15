# Finite-Degree Shifted Hankel Tail Stability

- **ID:** finite-degree-shifted-hankel-tail-stability
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / finite-height gate
- **Formalized companion:** `finite-degree-shifted-hankel-tail-stability-formalized.md`
- **Source:** `../../3-formalized/not_new_scientific_knowledge/degree-one-discriminant-tail-stability.md`;
  `docs/consolidated/revision01/bridge-theorem.md`
- **Statement:** A finite shifted Hankel block remains positive after an
  unverified tail only when the verified positive-bulk eigenvalue margin
  dominates an explicit tail matrix norm. This is the all-degree form of the
  summed domination obligation.

## Setup

Let

`T_k = L_k + E_k`, for `k=1,...,2d+1`,

where `L_k` comes from a positive real bulk and `E_k` is the remaining tail.
Define the shifted Hankel matrices

```text
B_d = [L_{i+j+1}]_{i,j=0}^d,
R_d = [E_{i+j+1}]_{i,j=0}^d,
H_d = B_d + R_d.
```

Assume `B_d` is positive definite, and suppose the tail has absolute moment
bounds

`|E_k| <= eta_k`, for `k=1,...,2d+1`.

Define

```text
F_d(eta) = (sum_{i=0}^d sum_{j=0}^d eta_{i+j+1}^2)^(1/2),
G_d(eta) = max_{0<=i<=d} sum_{j=0}^d eta_{i+j+1}.
```

## Theorem

If either

```text
lambda_min(B_d) > F_d(eta)
```

or

```text
lambda_min(B_d) > G_d(eta),
```

then `H_d` is positive definite. In particular, every principal determinant
of `H_d` is positive, including `det H_d`.

## Proof

For every vector `c`,

```text
c^* H_d c = c^* B_d c + c^* R_d c
          >= lambda_min(B_d) ||c||_2^2 - ||R_d||_op ||c||_2^2.
```

The Frobenius bound gives

```text
||R_d||_op <= ||R_d||_F
           <= (sum_{i,j} eta_{i+j+1}^2)^(1/2)
           = F_d(eta).
```

The row-sum bound gives

```text
||R_d||_op <= ||R_d||_infty
           <= max_i sum_j eta_{i+j+1}
           = G_d(eta),
```

when the matrix is real symmetric; in the conjugation-symmetric complex case,
apply the same estimate to the Hermitian operator norm after taking absolute
values entrywise, or use the Frobenius bound directly.

Thus either displayed hypothesis implies

`c^*H_dc > 0`

for every nonzero `c`, so `H_d` is positive definite.

## Consequence For The RH Route

This theorem is the precise finite-height meaning of "the verified bulk
dominates the unverified tail" for shifted Hankel square tests.

To prove a range such as `d <= d(H)` from an RH verification height `H`, one
must provide:

1. a certified positive real bulk matrix `B_d`;
2. a lower bound for `lambda_min(B_d)`;
3. absolute tail moment bounds `eta_k` for `k<=2d+1`;
4. one of the displayed inequalities.

Without these four items, a finite-range determinant claim is evidence or
heuristic, not a theorem. This theorem does not prove RH; it translates the
finite-range bridge obligation into a checkable matrix inequality.

## Relation To The Degree-One Card

For `d=1`, this matrix theorem gives a sufficient eigenvalue-margin test. The
separate card `../../3-formalized/not_new_scientific_knowledge/degree-one-discriminant-tail-stability.md` gives a sharper
scalar determinant identity:

`Delta-Delta_B=L_1E_3+L_3E_1-2L_2E_2+E_1E_3-E_2^2`.

Thus `d=1` has both a determinant-specific gate and the general matrix gate.
For `d>1`, the matrix gate is the reusable finite-height form.

## Gates

- [x] 0 -> 1 in-progress: all-degree tail-stability obligation isolated.
- [x] 1 -> 2 fully-proven: operator-norm proof written.
- [x] 2 -> 3 formalized: `GaloisForLFunctions.HTGeometry`
  `FiniteDegreeShiftedHankelTailStability.lean` proves the literal Rayleigh
  `lambda_min` lower bound, exact Frobenius and exact finite row-sum budgets,
  both strict-margin positivity gates, and positivity of every principal
  determinant under either stated alternative. Targeted leaf build and axiom
  audit pass with only `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-06-24 -- Codex: created to replace the informal `d~H` determinant-range
  language by an explicit finite-degree matrix inequality.

- 2026-08-15 -- Lean formalization completed in
  `formal/GaloisForLFunctions/HTGeometry/FiniteDegreeShiftedHankelTailStability.lean`.
  The certificate retains both literal alternatives: the Frobenius budget
  `F_d(eta)` and finite maximum row-sum budget `G_d(eta)`. Its
  `finiteDegreeShiftedHankelLambdaMin` is the infimum of the exact finite
  block Rayleigh quotient, not an externally assumed numerical surrogate.

## 2026-06-24 Monomial Gate Limitation

`monomial-tail-gate-height-linear-no-go.md` records the limitation of the
coefficient-norm version of this finite-degree gate. Since
`lambda_min(B_d) <= L_{2d+1} <= L_1 R^(2d)` while the first hard-edge tail
moment beyond height `H` is only of order `log H / H`, the monomial
absolute-tail gate cannot prove a height-linear range `d~H`.

The usable target is therefore the relative/source form of the same idea:
control `B_d^(-1/2) R_d B_d^(-1/2)`, move to an orthogonal-polynomial basis, or
prove the completed source sign directly.
