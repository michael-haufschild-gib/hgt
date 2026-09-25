# S6F hidden `sl₂` scale structure and matrix-Gram no-go

Date: 2026-08-29  
Status: computation complete; diagnostic only; forbidden as input to Lean proofs

## Route question

The prior exact principal-minor campaign found the signed reflected-jet scale velocity `H_X`
strictly positive definite on the Lean-proved refined parabolic cone. This run asked whether that
fact has either of two compact explanations:

1. a universal source-coordinate Lie-algebra identity; or
2. a coefficientwise PSD matrix-Bernstein decomposition in cone slack coordinates.

The first would open a conceptual proof route. The second would reduce the proof to a direct conic
matrix sum.

## Exact structural outcome

Let `V` be the autonomous source vector field in `(U,B,Q)` and put

```text
D = (U/2)∂U + (B/2)∂B + (Q+3/8)∂Q,
W = -3∂U + ∂B + (3B/4)∂Q,
e = V + W,
f = -W,
h = 4D.
```

Exact symbolic reduction gives

```text
[h,e] = 2e,    [h,f] = -2f,    [e,f] = h.
```

Thus source dynamics contain a literal `sl₂` triple. Moreover, physical scale differentiation is
exactly

```text
X ∂X = D,
```

after the normalized physical substitution. Hence `X H_X` is the Cartan derivative of the
universal signed reflected-jet Hankel matrix, not an unrelated polynomial matrix.

In coordinates

```text
r = U+3B,
b = B,
k = Q+3/8-3B²/8 = (16Q+6-6B²)/16,
```

the lowering direction becomes `W=∂b`, while

```text
V(r) = 2br+16k,
V(b) = b²+4k-1,
V(k) = 4bk-2kr.
```

The first Cartan-Hankel moment also factors compactly:

```text
m₀ = (3b²+8k)(3b²+8k-3)/32.
```

These identities are exact algebra. Their proofs can be reconstructed independently by chain rule
and polynomial expansion; no sampled value is needed.

## Killed explanation

The coefficientwise matrix-Bernstein Gram is false. After expanding `H_X` in nonnegative scale
slack `S` and using common Bernstein degrees on the compact clock rectangle:

- every one of the 286 coefficient matrices in the `S²` layer has negative leading rank-two and
  rank-three pivots;
- every one of the 273 coefficient matrices in the `S³` layer has negative determinant.

The assembled matrix remains positive definite, so cancellation between scale layers is essential.
Do not pursue a proof that writes `H_X` as a nonnegative scalar combination of its raw
matrix-Bernstein coefficient matrices.

## Consequence for S6F

The Loewner route survives, but its compact explanation must use the `sl₂` representation or a
nontrivial congruence mixing scale layers. Strongest next conjecture:

```text
[CONJECTURE]
On the degree-four reflected-jet module, the Cartan derivative induced by (e,f,h)
has a positive contravariant form throughout the refined physical cone.
```

Best hostile test is to construct that finite contravariant/Shapovalov form exactly and search for
an interior rational state where its rank-three restriction is indefinite. The known six-point
failure of all-order reflected-fibre positive definiteness makes failure beyond this finite module
plausible and prevents accidental promotion to an all-order claim.

## Reproduction

RunPod used six exact-symbolic workers. `verify_results.py` checks the chain-rule identity, all
three `sl₂` brackets, and the negative coefficient-matrix pivots. `SHA256SUMS` authenticates the
downloaded scripts and outputs.

```bash
python3 run_experiments.py --workers 6 --output results.json
python3 verify_results.py .
```
