# Polynomial-blind, resolvent-complete boundary splitting — formalized

- **ID:** `moment-polynomial-blind-resolvent-complete-boundary-splitting-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `moment-polynomial-blind-resolvent-complete-boundary-splitting.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `HTGeometry/BoundaryConditionalExpectation.lean` | the leaf kernel and leaf average, the conditional-expectation identity `(4)`, `P_s = E_ν[·\|σ(π)]` `(5)`, the horizontal/vertical splitting `(6)`–`(8)`, and polynomial blindness `(10)`–`(13)` |
| `HTGeometry/CauchyTransformOpenUniqueness.lean` | Cauchy-transform uniqueness for finite measures from a nonempty open subset of the upper half-plane |
| `HTGeometry/CauchyKernelDensityVanishing.lean` | a density whose Cauchy transform vanishes on an open subset of **each** half-plane vanishes almost everywhere |
| `HTGeometry/NevanlinnaQuotientOpenImage.lean` | the Weyl pole map `q = −d/c` is nonconstant and has open images |
| `HTGeometry/NevanlinnaResolventCompleteness.lean` | the chart splitting of a projective integral, the leaf Cauchy transform `(14)`, the Möbius partial fraction `(18)`, resolvent completeness `(19)`–`(20)`, and the finite-centre separation of extremal leaves |
| `HTGeometry/NevanlinnaPickGramSplitting.lean` | complex Fubini over a probability kernel, the three kernels `(21a)`, `(21e)`, `(21f)`, the law of total covariance `(21h)`, the self-Gram variance identity `(21b)`, and the point-mass degeneracy `(21d)` |
| `HTGeometry/NevanlinnaBoundaryL2Completeness.lean` | resolvent completeness in `L²` `(21)`, the closed span of the centered features `(21c)`, and the rank-one mean layer `(21i)` |
| `HTGeometry/CompleteCauchyGermClosure.lean` | the complete-germ closure used for finite-centre determinacy |
| `HTGeometry/PositiveMeasureExtremeRays.lean` | a two-valued probability measure is a Dirac mass |

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

- `(4)` `NevanlinnaBoundaryFamily.integral_comp_projectiveLabel_mul_barycenter`;
- `(5)` `NevanlinnaBoundaryFamily.markovAverage_ae_eq_condExp` — the leaf average **is** the
  conditional expectation of the carrier over the label σ-algebra;
- `(6)`–`(8)` `NevanlinnaBoundaryFamily.integral_comp_projectiveLabel_mul_eq_parameter`,
  `NevanlinnaBoundaryFamily.forall_integral_comp_projectiveLabel_mul_eq_zero_iff` — the vertical
  space is exactly the kernel of leaf averaging;
- `(10)`–`(13)` `leafAverage_eval`, `leafAverage_eval_sub_const`,
  `integral_eval_mul_comp_projectiveLabel` — every polynomial is flattened to its moment, centered
  polynomials are vertical, and mean-zero label observables annihilate every polynomial;
- `(14)`, `(18)` `ClassicalAnalyticNevanlinnaCarrierFamily.leafCauchy`,
  `leafCauchy_sub_infty`;
- `(19)`–`(20)` `ClassicalAnalyticNevanlinnaCarrierFamily.eq_zero_ae_of_annihilates_leafCauchy`
  and `HTGeometry.analyticNevCarrier_eq_zero_ae_of_annihilates_leafCauchy` (the constructed family,
  no analytic hypothesis);
- `(21)` `ClassicalAnalyticNevanlinnaCarrierFamily.resolventSubmodule_topologicalClosure_eq_top` —
  in `L²` of the boundary law the constants together with the leaf Cauchy transforms span a dense
  subspace;
- `(21a)`, `(21e)`, `(21f)`, `(21h)` `boundaryGram`, `carrierPickGram`, `withinLeafGram`,
  `carrierPickGram_eq_add` — the law of total covariance on the support fibration;
- `(21b)` `boundaryGram_self` — the self-Gram is the boundary variance, hence real and nonnegative;
- `(21c)` `centeredSubmodule_topologicalClosure` — the closed span of the centered feature family
  is exactly the orthogonal complement of the constants, i.e. the mean-zero subspace: the exact
  rank statement for `Γ_η`;
- `(21d)` `boundaryGram_eq_zero_iff_exists_dirac` — the boundary covariance vanishes identically
  **iff** the boundary law is a point mass;
- `(21i)` `finrank_span_constL2` (the mean layer has rank one) together with `(21c)`;
  `polynomial_eq_zero_of_ae_eq_zero_of_support_infinite` supplies the card's argument that centered
  polynomials stay linearly independent on an infinite-support carrier, so the vertical layer is
  infinite;
- finite-centre determinacy: `measure_eq_of_completeCauchyJet_eq` (one complete regular germ
  determines the carrier, hence the boundary law by injectivity of barycentring) and
  `leafCauchy_injective_on_chart` (one scalar finite-centre value separates the extremal leaves).

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/BoundaryConditionalExpectation.lean
lake env lean GaloisForLFunctions/HTGeometry/NevanlinnaResolventCompleteness.lean
lake env lean GaloisForLFunctions/HTGeometry/NevanlinnaPickGramSplitting.lean
lake build GaloisForLFunctions.HTGeometry.NevanlinnaBoundaryL2Completeness
```

## What closed last

Two pieces of analysis that mathlib does not have.  **Cauchy-transform uniqueness from an open
set**: the resolvent transform of a finite measure is analytic off the line, so agreement on a
nonempty open subset propagates by the identity theorem, the total mass is recovered as
`lim_{y→∞} y·Im S(iy)`, and the normalised measures are then separated by the complete Cauchy germ.
**Two-sided density vanishing**: an integrable complex density whose Cauchy transform vanishes on an
open subset of *each* half-plane vanishes almost everywhere — one half-plane is provably
insufficient (the density `(τ − i)⁻²` against Lebesgue measure), which is exactly why the boundary
argument must use the Weyl map on both sides.  The Weyl pole map supplies those two open sets
because it is nonconstant: a constant nonreal value would force the real lower row to vanish
identically, contradicting the determinant-one law.

## Boundary

The remaining gates on the paper card — an independent specialist proof audit and a full
primary-source priority audit — are external literature obligations, not formalization obligations.
The RH content is stated as a carrier requirement: source determination must be transverse to the
Nevanlinna Bauer retract.  This is not a proof of RH.
