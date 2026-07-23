# Xi Ward phase and source transport are non-diagonal Hardy contractions

- **ID:** `xi-ward-hardy-nondiagonal-nonexpansiveness`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`
- **Lean module:** `RHTower/GammaSewnMobiusXiWardHardyNonexpansive.lean`

## Result

For every finite packet `w : Fin n → ℂ` in the open right half-plane and every real aperture
`alpha ≥ 0`, let

```text
G_ij = 1 / (w_i + conj(w_j)),

Phi_i(alpha)
 = xiRightWardBoundarySourcePhaseCrossRatio(i*w_i, alpha),

V_i(alpha)
 = mobiusGammaXiAntiCausalWardTransportV(w_i, alpha)
 = 1 - Phi_i(alpha).
```

Lean proves unconditionally

```text
[(1 - Phi_i(alpha) conj(Phi_j(alpha)))
  / (w_i + conj(w_j))]_ij ⪰ 0.                         (1)
```

Thus the complete infinite Schwarz-paired Xi phase is a contractive multiplier of the
right-half-plane Hardy kernel, not merely a pointwise contraction.

Affine Schur closure gives the actual source transport:

```text
G - diag(V/2) G diag(V/2)^* ⪰ 0,                       (2)

4 G - diag(V) G diag(V)^* ⪰ 0.                         (3)
```

Equation `(3)` is finite-packet nonexpansiveness with the exact four-unit source radius.

## Proof mechanism

For one strict-right Cayley divisor factor

```text
b_lambda(w,alpha)
 = (w + lambda - alpha) / (w + lambda + alpha),
```

its Pick defect has the exact decomposition

```text
K_b
 = 2 alpha A A^*
   + 4 alpha Re(lambda) D G D^*,                       (4)
```

where

```text
A_i = (w_i + lambda + alpha)^(-1),
D = diag(A_i).
```

Both terms are positive semidefinite. Pick defects obey

```text
K_(fg) = K_f + diag(f) K_g diag(f)^*.                  (5)
```

This closes `(4)` under every finite Schwarz-paired product. The existing unconditional
`HasProd` identity for the actual Xi phase supplies entrywise convergence of those finite
products. Positive semidefiniteness is closed under finite-matrix limits, proving `(1)`.

Finally,

```text
K_((1-f)/2)
 = (1/2) K_f
   + (1/4) diag(1+f) G diag(1+f)^*,                    (6)
```

which proves `(2)` and `(3)`.

## Exact frontier after this theorem

This theorem does not prove the RH-bearing Ward-column inequality. Its right side is a multiplier
congruence,

```text
diag(V) G diag(V)^*,
```

whereas the required infinitesimal consumer contains the outer product of the aperture tangent,

```text
r_P r_P^*,
r_P(i) = d/d alpha V_i(alpha)|_(alpha=0).
```

Finite-aperture contractivity cannot be differentiated into that outer-product estimate without
an additional singular source theorem. The corpus already proves that a nonzero four-unit
boundary relative-trace density must have square-root, not norm-differentiable, scaling. Therefore
do not retry ordinary smooth Schur contraction, pointwise norm bounds, finite products, or
entrywise Pick positivity as the missing RH step.

The surviving problem is to construct the source-defined singular/cofinal boundary lift whose
Julia block has column `r_P` and boundary diagonal `4`, or to prove no such lift can arise from
the CCM source.

## Formal audit

- Direct `lake env lean` check: passed.
- Main theorem axiom dependencies: `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declaration.

