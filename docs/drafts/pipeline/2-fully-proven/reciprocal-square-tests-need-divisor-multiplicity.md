# Reciprocal Square Tests Need Divisor Multiplicity

- **ID:** reciprocal-square-tests-need-divisor-multiplicity
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** docs/consolidated/gpt/proof-route.md, Layer B square-test positivity
- **Statement:** Shifted square-test positivity is not determined by the distinct reciprocal support alone. Keeping the same support but changing divisor weights can change whether the first shifted Hankel tests are positive.

## Goal

Guard Layer B against replacing

```text
T_k = sum_rho m_rho y_rho^k
```

by a support-only sum. The divisor multiplicities `m_rho` are part of the positivity datum, not metadata.

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, attack idea
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 -> 3 formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: standalone note if needed

## Proof

[PROVED HERE]

Fix the same distinct support

```text
Y = {1, -1/2+i, -1/2-i}.
```

Give the real atom `1` weight `2`. Give each complex conjugate atom weight `c`, where `c` is either `1` or `2`. Define real moments

```text
m_n(c)=2 + c((-1/2+i)^n+(-1/2-i)^n).
```

The first four moments are:

```text
c=1: m=(4, 1, 1/2, 19/4),
c=2: m=(6, 0, -1, 15/2).
```

For `c=1`,

```text
H_0 = [[4,1],[1,1/2]],       det H_0 = 1,
H_1 = [[1,1/2],[1/2,19/4]],  det H_1 = 9/2.
```

Both matrices are positive definite.

For `c=2`,

```text
H_0 = [[6,0],[0,-1]],       det H_0 = -6,
H_1 = [[0,-1],[-1,15/2]],   det H_1 = -1.
```

Both shifted tests fail.

The distinct support `Y` was unchanged. Only the multiplicity of the conjugate pair changed. Therefore support-only reciprocal data do not determine shifted square-test positivity.

## Computation

Verified with exact rational moments in `computations/2026-06-21-penrose-proof-r06-multiplicity-support-invariant.py`.

Output archived at `computations/2026-06-21-penrose-proof-r06-multiplicity-support-invariant.txt`.

## Log

- 2026-06-21 -- created in 2-fully-proven from workflow NODE "multiplicities carry geometric or structural information" under method 12, invariant.
