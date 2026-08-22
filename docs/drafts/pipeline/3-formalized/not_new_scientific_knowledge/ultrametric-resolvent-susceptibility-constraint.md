# Ultrametric resolvent susceptibility constraint

- **ID:** `ultrametric-resolvent-susceptibility-constraint`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / QFT SPECTRAL INFRASTRUCTURE
- **Source:**
  `../../2-fully-proven/not_new_scientific_knowledge/04-rg-stochastic-quantum-fields/ultrametric-one-loop-resolvent-hypertranscendence.md`
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** For every integer branching parameter `p >= 2` and resolvent order `m >= 2`,
  the two-shell boundary coefficients determine a unique formal susceptibility through the exact
  contractive affine rescaling law.

## Formal statement

The module
`formal/GaloisForLFunctions/HTGeometry/UltrametricResolventSusceptibility.lean` defines

```text
ultrametricResolventScale
ultrametricResolventBoundaryCoefficient
ultrametricResolventCoefficientScale
ultrametricResolventCoefficient
ultrametricResolventBoundary
ultrametricResolventSusceptibility
```

and proves

```text
ultrametricResolventCoefficient_denominator_pos
ultrametricResolventScale_mul_rescale_power
ultrametricResolventCoefficient_recursion
ultrametricResolventSusceptibility_constraint
ultrametricResolventSusceptibility_unique
```

The coefficient denominator is positive unconditionally under `2 <= p` and `2 <= m`.  The
recursion is therefore nonresonant at every Taylor degree.  Coefficient extensionality gives the
complete power-series constraint

```text
Q = B + (p / p^m) * rescale(1/p, Q),
```

and the same nonresonance proves that any second formal solution equals `Q` coefficientwise.
No initial datum, normalization hypothesis, or unproved analytic premise enters the Lean theorem.

## Exact boundary

The module does not formalize normal convergence of the spectral sum, meromorphic continuation,
the pole proof of nonrationality, the external q-difference hypertranscendence theorem, the
one-loop log-determinant interpretation, or de Sitter harmonic analysis.  Those remain explicit
paper-level inputs in the source card.  The Lean result is the reusable static-constraint core.

## Gates

- [x] 0 -> 1 in-progress: source spectrum and coefficient recursion isolated
- [x] 1 -> 2 fully-proven: coefficient nonresonance and uniqueness proved on paper
- [x] 2 -> 3 formalized: exact module build and axiom audit pass
- [ ] 3 -> 4 publication-ready: analytic HT theorem remains external

## Verification

- touched-file `lake env lean` -- PASS
- exact cached module build -- PASS
- axiom audit of both capstones -- only `propext`, `Classical.choice`, and `Quot.sound`

## Novelty gate

Formal power series, coefficientwise affine rescaling, and nonresonant uniqueness are parent
mathematics.  Their application to the exact ultrametric susceptibility is useful corpus
infrastructure, not new scientific knowledge.
