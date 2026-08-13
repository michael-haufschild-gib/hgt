# Spectral-type stratified moment fiber carries maximal translation HT — formalized

- **ID:** `spectral-type-stratified-moment-fiber-maximal-ht-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `spectral-type-stratified-moment-fiber-maximal-ht.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `HTGeometry/LabeledBoundarySimplex.lean`, `HTGeometry/HamburgerBoundaryKernel.lean` | barycentring, its additivity and homogeneity, exact label recovery, atomlessness transport, singularity transport, and complete Hamburger-moment preservation (4) |
| `HTGeometry/NevanlinnaBoundaryKernel.lean` | the boundary family, the exact label pushforward (6), and the closed embedding |
| `HTGeometry/ProjectiveSingularContinuousResidual.lean`, `HTGeometry/ProjectiveLabelNullPreimage.lean` | the projective singular-continuous parameter phase and the null-preimage theorem for a real-analytic lower row (9) |
| `HTGeometry/BoundaryBarycenterSpectralTransport.lean` | Luzin's property (N) on the line, pure-point transport, absolute-continuity transport (8), mutual-singularity transport, and the mixture mass-vector law (16)–(18) |
| `HTGeometry/NevFiberCountable.lean` | countability of every denominator fiber, which makes each `N`-extremal leaf purely atomic |
| `HTGeometry/AnalyticNevanlinnaBoundaryRealAnalytic.lean` | real analyticity of the lower row of the constructed family |
| `HTGeometry/NevExtremalFamily.lean`, `HTGeometry/AnalyticNevanlinnaCarrierConstruction.lean`, `HTGeometry/NevanlinnaTransferMinimalType.lean`, `HTGeometry/AnalyticNevanlinnaMaximalTranslationInputs.lean` | the constructed `N`-extremal family and the complete `MaximalTranslationInputs` term |
| `HTGeometry/NevanlinnaBoundaryFaceMaximalTranslation.lean`, `HTGeometry/CofinalCholeskyResidualPhase.lean`, `HTGeometry/AnalyticNevCofinalCholeskyUnconditional.lean` | the residual maximal full-translation phase on every infinite closed spectral face and on the whole carrier range (14)–(15) |

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

- `GaloisForLFunctions.HTGeometry.volume_image_eq_zero_of_differentiableOn` — Luzin's property (N):
  a function differentiable on a set maps Lebesgue-null subsets to Lebesgue-null sets;
- `HTGeometry.nevBarycenter_countableCarrier` — **pure-point transport**: a parameter law carried
  by a countable set produces a carrier concentrated on a countable set (the label level sets are
  the denominator fibers, and those are countable);
- `HTGeometry.nevBarycenter_absolutelyContinuous_volume` — **absolute-continuity transport (8)**:
  a parameter law absolutely continuous with respect to Lebesgue measure on the finite chart
  produces an absolutely continuous carrier;
- `HTGeometry.nevBarycenter_isSingularContinuous` — **singular-continuous transport (7),(9)**: an
  atomless parameter law singular with respect to projective Lebesgue measure produces an atomless
  Lebesgue-singular carrier;
- `GaloisForLFunctions.HTGeometry.NevanlinnaBoundaryFamily.measureBarycenter_mutuallySingular` —
  mutually singular parameter laws have mutually singular barycenters;
- `HTGeometry.nevBarycenter_mixture_spectralProfile` — **the spectral mass vector is retained
  (16)–(18)**: the barycenter of `a·η_pp + b·η_sc + c·η_ac` is the corresponding mixture of a
  countably carried, an atomless Lebesgue-singular, and an absolutely continuous carrier, and the
  three components stay pairwise mutually singular;
- `HTGeometry.nevBoundaryCarrierFace_hasHamburgerMoments` — every point of every boundary face has
  exactly the prescribed moment sequence;
- `HTGeometry.analyticNevCarrierFamily_maximalTranslationPhase_dense_residual` — the residual
  maximal full-complex-translation phase on every infinite closed boundary face, with no analytic
  hypothesis.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/BoundaryBarycenterSpectralTransport.lean
lake build GaloisForLFunctions.HTGeometry.BoundaryBarycenterSpectralTransport
```

## What closed last

The card's audit named three open items: the Hamburger/Nevanlinna extremal family, barycentric
moment preservation, and "the source-faithful measurable spectral disintegration used in
(6)–(9)".  The family and the moment preservation were closed by `nevExtremalFamily` and
`HamburgerBoundaryKernel`; the disintegration is replaced here by the four direct type-transport
theorems, of which absolute continuity is the analytically substantive one: it needs Luzin's
property (N) for the real-analytic projective label `-d/c`, so that a Lebesgue-null carrier set is
only visible to a Lebesgue-null set of parameters.  Mixtures follow from additivity, homogeneity,
and mutual-singularity transport of barycentring.

## Boundary

The remaining gates are an independent specialist proof audit and a full primary-source priority
audit across the parent fields: external literature obligations, not formalization obligations.
This is not a proof of RH.
