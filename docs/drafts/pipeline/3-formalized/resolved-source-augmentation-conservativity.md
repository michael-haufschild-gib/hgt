# Source-pointed observation network law

- **ID:** `resolved-source-augmentation-conservativity`
- **Stage:** 3-formalized
- **Status:** `[PROVED] [LEAN-FORMALIZED] [NOVELTY UNVERIFIED]`
- **Paper proof:**
  `../2-fully-proven/new_scientific_knowledge/deninger/resolved-source-augmentation-conservativity-law.md`
- **Publication manuscript:**
  `../4-publication-ready/riemann-hellinger-hodge-green-descent/main.tex`

## Formalized theorem

`formal/GaloisForLFunctions/HTGeometry/SourcePointedConservativityChainLaw.lean` proves:

1. kernel of a composite is pullback of the last-stage kernel;
2. a two-stage composite is conservative on a source sector iff each edge is conservative on its
   propagated source sector;
3. failure at either edge forces failure of every later composite;
4. stagewise uniform positive lower bounds multiply.

Iteration gives the arbitrary finite source-pointed chain law used as the paper's parent theorem.

`formal/GaloisForLFunctions/HTGeometry/SourcePointedObservationNetworkLaw.lean` proves:

1. kernel of a parallel observation pair is intersection of marginal kernels;
2. the pair is conservative exactly when its common source radical is zero;
3. every postprocessor remains blind to the kernel of its input observation.

Serial propagation and parallel kernel intersection form the paper's full network law.

`formal/GaloisForLFunctions/HTGeometry/ResolvedSourceAugmentationConservativityLaw.lean` proves:

1. addition of `n+1` resolved channels is a linear augmentation;
2. the anchored boundary `w |-> (-sum w,w)` is injective;
3. augmentation is surjective;
4. its kernel is exactly the anchored boundary range;
5. conservativity on a source sector is exactly disjointness from that range;
6. augmented vanishing is equivalent to resolved vanishing for every defect supported in a
   conservative sector;
7. covariance defect of an arbitrary ordered product is the sum of all transported factor
   defects;
8. a uniform positive lower bound implies source-sector conservativity.

`formal/GaloisForLFunctions/RHTower/DeningerGreenResolvedSourceConservativityCriterion.lean`
proves:

1. codiagonal of the arithmetic Green resolved defect vanishes unconditionally;
2. componentwise vanishing of that resolved defect is equivalent to RH;
3. support of every Green resolved defect in any codiagonal-conservative source sector implies RH.

## Exact open arithmetic arrow

No abstract hypothesis is hidden.  Local physical Xi jets now land coefficient-faithfully in
completed Hellinger--Gamma incidence, whose unsquared local Hodge trace vanishes exactly at zero
modular displacement.  Source-specific open statement is a global comparison to a canonical
completed arithmetic sector `S` satisfying

```text
range(Green resolved defect) <= S,
S intersect ker(codiagonal) = {0}.
```

The paper does not assert that statement or RH.

## Verification

- Direct foreground checks of all three new files pass.
- Targeted chain-law and Green-criterion builds pass.
- Axiom printouts use only `propext`, `Classical.choice`, and `Quot.sound`.
- Whole-tree formal lint passes.
- External novelty comparison intentionally deferred.
