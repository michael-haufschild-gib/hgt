# CCM four-unit boundary square-root ramification

- **ID:** CCM-C34
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (Lean)
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`
- **Source:** `ccm-hankel-boundary-relative-trace-four-unit-law.md`; C10--C11 and C33
- **Statement:** Every positive thermal first-order boundary density has exact square-root norm
  scale; a vanishing norm-differentiable curve has zero density, so no such curve can realize the
  four-unit CCM boundary normalization.

## Goal

Formalize the regularity consequence already implicit in the exact CCM relative-trace identity

```text
Delta_ell(u)=||Q_uH_ell||_HS^2,
Delta_ell(u)/u -> ||ell||_2^2.
```

This prevents future work from treating a smooth operator curve as a candidate carrier for the
nonzero four-unit boundary charge.

## Exact theorem

For a curve `F : R -> E` into any normed additive group, put

```text
delta_F(u)=||F(u)||^2/(1-exp(-u)),
a_F(u)=||F(u)||/sqrt(1-exp(-u)).
```

If `delta_F(u)->ell` as `u->0+`, then

```text
a_F(u)->sqrt(ell).                                      (C34.1)
```

If `E` is a real normed space, `F(0)=0`, and `F` has a norm derivative at zero, then

```text
delta_F(u)->0.                                          (C34.2)
```

Consequently a four-unit boundary curve satisfies `a_F(u)->2` and has no norm derivative at zero.
Dimension, rank, compactness, and operator realization are unrestricted.

## Proof

Equation `(C34.1)` is the exact identity

```text
sqrt(delta_F(u))=a_F(u)
```

followed by continuity of the square root. For `(C34.2)`, differentiability and `F(0)=0` give
`||F(u)||/u -> ||F'(0)||`, while continuity gives `||F(u)||->0`. Hence

```text
||F(u)||^2/u -> 0.
```

The derivative of `1-exp(-u)` at zero is one, so `u/(1-exp(-u))->1`; multiplication proves
`(C34.2)`. Uniqueness of limits excludes every positive density.

## Scientific classification

This is not new frontier progress. The paper-level relative-trace card already proves the
square-root Hilbert--Schmidt scale, and C10--C11 already identify a singular boundary graph as
mandatory. The new value is a dependency-closed Lean certificate and a no-repeat boundary:
norm-differentiable or norm-holomorphic boundary curves cannot be proposed as four-unit carriers.

The true open theorem remains source-defined nonexpansive transport from the squarefree/Euler
four-unit contact into `Q_u D_Xi`, equivalently the source-normalized Evans/model-space defect
vanishing. C34 neither proves that transport nor kills singular/cofinal CCM.

## Formal declarations

Generic module `formal/GaloisForLFunctions/HTGeometry/BoundaryTraceRamification.lean`:

- `thermalBoundaryTraceDensity`;
- `thermalBoundaryRamificationAmplitude`;
- `tendsto_thermalBoundaryRamificationAmplitude`;
- `tendsto_norm_sq_div_id_nhdsGT_zero_of_hasDerivAt`;
- `tendsto_one_sub_exp_neg_slope_nhdsGT_zero`;
- `tendsto_id_div_one_sub_exp_neg_nhdsGT_zero`;
- `tendsto_thermalBoundaryTraceDensity_zero_of_hasDerivAt`;
- `not_hasDerivAt_of_thermalBoundaryTraceDensity_tendsto_pos`.

CCM module `formal/GaloisForLFunctions/RHTower/CCMBoundaryTraceRamification.lean`:

- `ccmFourUnitBoundaryCurve_squareRootLaw`;
- `ccmFourUnitBoundaryCurve_not_hasDerivAt`.

## Gates

- [x] prior-corpus audit
- [x] paper proof
- [x] direct Lean checks
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [x] formal lint attribution audit: no finding in these modules; repository-wide lint fails only on
  pre-existing umbrella-reachability findings outside this card
- [x] targeted module build through
  `GaloisForLFunctions.RHTower.CCMBoundaryTraceRamification`

## Log

- 2026-07-23 — Formalized universal thermal square-root law and four-unit CCM specialization.
  Corpus audit found prior abstract square-root and relative-trace laws, so classified result as
  `NOT NEW SCIENTIFIC KNOWLEDGE` rather than promoting it as a frontier theorem.
