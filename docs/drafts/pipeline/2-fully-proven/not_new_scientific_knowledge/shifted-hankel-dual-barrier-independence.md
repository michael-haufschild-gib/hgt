# Shifted Hankel Dual-Barrier Independence

- **ID:** shifted-hankel-dual-barrier-independence
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** docs/consolidated/gpt/proof-route.md, sections 7-8
- **Statement:** For every truncation order `d>=1`, positivity of `H_0=[m_{i+j}]_{i,j=0}^d` and positivity of `H_1=[m_{i+j+1}]_{i,j=0}^d` are logically independent. Therefore the shifted proof-route target cannot drop either `Q_0` or `Q_1`.

## Goal

Guard the corrected reciprocal-seam theorem against silently weakening

```text
H_d^(0)=[T_{i+j+1}] >= 0 and H_d^(1)=[T_{i+j+2}] >= 0
```

to only one shifted Hankel family. This is not claimed as a deep theorem of moment theory; it is a proof-route guardrail with explicit witnesses.

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, attack idea
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 -> 3 formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: standalone note if needed

## Proof

[PROVED HERE]

Let `m=(m_0,m_1,m_2,m_3)` be a real finite sequence and define

```text
H_0(m) = [[m_0,m_1],[m_1,m_2]],
H_1(m) = [[m_1,m_2],[m_2,m_3]].
```

First, at `d=1`, take `m=(1,0,1,0)`. Then

```text
H_0 = [[1,0],[0,1]] >= 0,
H_1 = [[0,1],[1,0]],
```

and `H_1` has eigenvalues `1` and `-1`. Hence `H_0 >= 0` does not imply `H_1 >= 0`.

Conversely, take `m=(0,1,0,1)`. Then

```text
H_0 = [[0,1],[1,0]],
H_1 = [[1,0],[0,1]] >= 0,
```

so `H_1 >= 0` does not imply `H_0 >= 0`.

The independence persists at the PSD boundary. For

```text
m^(0)_eps = (1,1,1+eps,2),
```

one has

```text
det H_0(m^(0)_eps) = eps,
det H_1(m^(0)_eps) = 1 - 2 eps - eps^2.
```

Thus for small negative `eps`, `H_0` fails while `H_1` remains positive definite; at `eps=0`, `H_0` is singular while `H_1` is positive definite; and for small positive `eps`, both are positive definite.

For

```text
m^(1)_eps = (2,1,1,1+eps),
```

one has

```text
det H_0(m^(1)_eps) = 1,
det H_1(m^(1)_eps) = eps.
```

Thus `H_1` can cross its PSD boundary while `H_0` remains positive definite.

Applying this with `m_n=T_{n+1}` proves that the two shifted square-test targets in `docs/consolidated/gpt/proof-route.md` are separately necessary at finite truncation level.

The same independence holds at every order. Let

```text
a_n = 1 if n is even, and a_n = 0 if n is odd.
```

Then `a_n` is the moment sequence of the positive measure

```text
(delta_1 + delta_{-1})/2
```

on the real line. Hence every Hankel block `[a_{i+j}]_{i,j=0}^d` is PSD. But for every `d>=1`, the shifted block `[a_{i+j+1}]_{i,j=0}^d` contains the leading principal submatrix

```text
[[a_1,a_2],[a_2,a_3]] = [[0,1],[1,0]],
```

so it is not PSD.

Conversely define `b_0=0` and `b_{n+1}=a_n`. Then every shifted block `[b_{i+j+1}]_{i,j=0}^d=[a_{i+j}]_{i,j=0}^d` is PSD, while every unshifted block `[b_{i+j}]_{i,j=0}^d` with `d>=1` contains

```text
[[b_0,b_1],[b_1,b_2]] = [[0,1],[1,0]],
```

so it is not PSD. This proves all-order logical independence.

## Computation

Verified in `computations/2026-06-21-penrose-proof-r04-liquidity-insolvency-boundary.py`.

Output archived at `computations/2026-06-21-penrose-proof-r04-liquidity-insolvency-boundary.txt`.

## Log

- 2026-06-21 -- created in 2-fully-proven after the workflow-selected shifted-Hankel transfer from the liquidity-vs-insolvency NODE.
