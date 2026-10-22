# Theta first-Gibbs support-Haviland universality law

Status: Stage 3 — formalized in Lean 4; final umbrella audit pending  
Lean target: `GaloisForLFunctions.RHTower.ThetaFirstGibbsSupportHavilandUniversalityLaw`  
Novelty: `[NOVELTY UNVERIFIED]`

## Theorem-generated discovery

`ThetaSingleGibbsEssentialMomentClosure` identifies the first theta Gibbs moment functional with
integration against its positive half-line density, but extracts only nonnegativity of polynomial
squares.

`MomentFunctionalHaviland` shows that an exact positive representing measure controls the entire
cone of pointwise-nonnegative polynomials and makes the functional order-preserving.  The corpus
does not transport that stronger cone law to the theta Gibbs carrier.

## Statement

The first theta Gibbs moment functional has one simultaneous support-Haviland certificate:

1. every polynomial is represented exactly by integration against the first Gibbs density on
   `(0, ∞)`;
2. every polynomial nonnegative on `(0, ∞)` has nonnegative functional value;
3. pointwise polynomial order on `(0, ∞)` is preserved by the functional;
4. every polynomial square has nonnegative value.

The support-local condition is sharper than requiring nonnegativity on all of `ℝ`, and the final
square/Hankel statement is now a corollary of the full positive cone rather than the endpoint.

## Dependency-closed proof

1. Use the exact polynomial integral identity already proved for the first Gibbs moments.
2. Restricted-volume almost every point lies in `(0, ∞)`.
3. On that support, the polynomial is nonnegative by hypothesis and the Gibbs density is
   nonnegative, so their product has nonnegative integral.
4. Apply this result to `q - p` to obtain order preservation; moment-functional additivity and
   homogeneity identify its value with `L(q) - L(p)`.
5. Apply support positivity to `p²` to recover square positivity.

No computation or new measure-theoretic premise is introduced.

## Novelty audit

Corpus audit: the generic Haviland necessary law and the theta exact integral identity exist, but
the theta module states only square positivity.  Support-local full-cone positivity and polynomial
monotonicity are absent.

Literature audit: deferred until exact Lean proof succeeds, per research protocol.

## Lean verification

- Exact source check passed:
  `lake env lean GaloisForLFunctions/RHTower/ThetaFirstGibbsSupportHavilandUniversalityLaw.lean`.
- Wired into `GaloisForLFunctions.RHTower`.
