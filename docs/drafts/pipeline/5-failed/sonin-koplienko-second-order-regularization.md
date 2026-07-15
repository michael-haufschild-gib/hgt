# Sonin Koplienko second-order regularization

- **ID:** sonin-koplienko-second-order-regularization
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** physics-literature audit of the Hilbert--Schmidt relative-Gram trace obstruction
- **Statement:** Koplienko second-order trace regularization cannot scalarize the linear Sonin
  Euler channel: its defining first-variation subtraction deletes exactly the two unsquared
  principal/residual cross terms and retains only the squared residual energy.

## Route tested

`SoninRelativeGramDefect.lean` exposes a Hilbert--Schmidt relative Gram perturbation

```text
(P+cR)†(P+cR)-P†P
  = c P†R + conj(c) R†P + |c|² R†R.
```

Only the first two terms retain the logarithmic Euler coefficient without squaring it.  They are
Hilbert--Schmidt, but the present corpus does not make them trace class.  The route tested whether
Koplienko's trace formula for Hilbert--Schmidt perturbations supplies a canonical scalar trace
without an additional smoothing or trace-class hypothesis.

## Exact obstruction

Koplienko regularization is a second-order trace formula.  Before a trace is taken it subtracts
the unperturbed value and the first Fréchet variation.  For the Gram observable the entire
operator identity is elementary and exact:

```text
[(P+cR)†(P+cR)-P†P]
  - [c P†R + conj(c) R†P]
    = |c|² R†R.
```

At a Sonin prime-power scale, `c` is the exact logarithmic Euler coefficient.  The regularized
remainder therefore depends only on its squared modulus and on the already available residual
energy.  It contains no linear principal/residual channel from which the intended prime mode
could be recovered.

This does not say that Koplienko's formula is false or useless.  It says that its defining
subtraction is incompatible with this route's required value: the datum being sought is exactly
the datum the second-order regularization removes.

## Formal source

The source-only generic identity is in
`formal/GaloisForLFunctions/HTGeometry/KoplienkoSecondOrderGram.lean`, with the central-Sonin and
prime-power specializations in
`formal/GaloisForLFunctions/RHTower/SoninKoplienkoSecondOrderNoGo.lean`.

The formalized scope is deliberately smaller than the analytic Koplienko theorem.  It proves the
exact Gram subtraction that decides this route; it does not introduce a spectral-shift function
or assert existence of a Koplienko trace for the Sonin operators.

## Direct corpus consequence

- The tempting inference "Hilbert--Schmidt relative defect, therefore use a second-order trace"
  is retired for `SoninRelativeGramDefect.lean`.
- `HilbertSchmidtTraceObstruction.lean` remains the correct boundary for ordinary trace
  scalarization; second-order regularization crosses that boundary only by erasing the required
  linear information.
- A viable continuation must preserve the first variation.  It therefore needs a genuinely
  first-order relative trace, an additional source-side smoothing that makes the cross term trace
  class, or a non-trace pairing that is already continuous on the Hilbert--Schmidt ideal.
- The result is reusable in HTGeometry: any proposed physics regularization of a Gram
  perturbation whose signal lives only in the linear cross term can be rejected by the same
  identity before analytic trace machinery is built.

## Literature provenance

1. L. S. Koplienko, *The trace formula for perturbations of nonnuclear type*, Siberian
   Mathematical Journal 25 (1984), 735--743,
   DOI [10.1007/BF00968686](https://doi.org/10.1007/BF00968686).
2. F. Gesztesy, A. Pushnitski, and B. Simon, *On the Koplienko spectral shift function. I.
   Basics*, Journal of Mathematical Physics 48 (2007), 083501,
   [arXiv:0705.3629](https://arxiv.org/abs/0705.3629).  This modern treatment is supporting
   provenance only; no extra analytic theorem from it is imported into the Lean source.

## Verification status

Source inspection only.  In accordance with the active user constraint, no Lean invocation,
scratch compilation, lint, axiom inspection, numerical check, targeted build, or full build was
run.  The declarations are not stage-3 formalizations until targeted verification is authorized.

## Log

- 2026-07-15 — route falsified by the exact second-order Gram identity; generic HTGeometry and
  Sonin prime-power source written.  No computation or build run.
