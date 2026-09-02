# Direct completed-SEM rectangle-winding anchor

- **ID:** ULF-DSA-001
- **Stage:** 1-in-progress
- **Status:** conjecture sharply isolated; two required theorems open; no RH claim
- **Target:** one source-defined integer, one fixed bound below one, no tensor/amplification step

## Big picture

Ferrero--Washington does not make a small real observable and hope it detects a zero.  Its
discrete invariant is already attached to the arithmetic completion.  Positivity of that invariant
would force exact congruences at every digit depth; equidistribution contradicts those congruences.
The complex analogue should likewise place discreteness on the **completed source**, not on a
zero-fed receiver.

For zeta, the natural discrete source observable is winding.  The first candidate is winding of
the literal completed symmetric Euler--Maclaurin member on a source-selected rectangle exhausting
the strict right half of the critical strip.  No anomaly is subtracted unless an exact identity
places that anomaly on this same rectangle boundary.  The corpus's winding `-1` belongs to a
different one-dimensional real-aperture crossing and cannot presently be combined with the
rectangle index.

## Corpus facts used

1. `completedSEMContourIndexZ` is an integer defined from the actual finite symmetric
   Euler--Maclaurin completion, without a zero list.  Under an isolating split it equals enclosed
   multiplicity (`CompletedSEMContourBoundary`).  Existing RH use is still zero-centred, so it is
   not the required global anchor.
2. One off-line pair has a fixed finite quantum: horizontal collision charge is even and at least
   two; strict-right order is at least one (`XiHorizontalCollisionChargeEndpoint`).  Thus no
   height amplification is logically required once the same integer is source-bounded.
3. Literal prime--Gamma formation has source winding `-1`; it equals the completed prime--Gamma
   crossing winding and the Hardy/Fredholm index on the real Euler ray
   (`GammaSewnMobiusApertureStokesSourceNoPositiveWinding`,
   `GammaSewnMobiusApertureStokesCompletedPrimeGammaSpectralFlowIdentification`).  This is a
   one-dimensional aperture index, not a right-half rectangle index.  It proves that winding
   geometries must be matched before indices are added or subtracted; it does not show that the raw
   rectangle winding has a universal anomaly.
4. The archimedean tail has the exact dimensionless budget
   `beta = 3 log 2 + pi/2 - 3 < 1` (`ArchimedeanBudgetConstant`).  This is a genuine subunit
   constant, but the existing Weil decomposition leaves an uncontrolled signed prime error; the
   constant alone does not bound an integer.
5. Two-prime Cesaro and Gauss--Hodge collision carriers still contain `analyticOrderAt xi` in their
   definitions.  They are source-labelled readers, not pre-divisor integers.
6. Rajchman decay is not a selector.  The corpus proves that clocks built from an off-line Cauchy
   pair are themselves Rajchman, including on the prime-log torus
   (`primeLogOffLineCauchyPairEnergyClockSample_isInfiniteTorusRayRajchman`).  Fourier decay can
   coexist with off-line charge.
7. `NoDiscreteInvariant` excludes continuous maps from connected divisor deformations into a
   totally disconnected target.  It does not exclude a discontinuous source winding/content that
   jumps when a completed boundary becomes singular.

## Ferrero--Washington lesson, stated correctly

For the cyclotomic Iwasawa module, positive `mu` is equivalent to exact digit congruences for every
depth and every input; uniform distribution of normalized digit truncations violates that
all-depth restriction.  The decisive ingredient is not merely Weyl decay.  It is:

```text
nonzero discrete content
  => exact restriction at every formation depth
  => one equidistributed depth violates the restriction.
```

The RH analogue must therefore derive an all-depth restriction from nonzero **source winding**.
Averaging a divisor count, an inertia, or a positive energy is invalid because the
average need not preserve the integer.

## The proposed integer

Choose a cofinal family of safe right-half windows `R_T` by a source predicate: their boundaries are
nonvanishing for Xi, but their definition does not enumerate or select divisor points.  Let `C_N`
be the actual completed symmetric Euler--Maclaurin member.  Define, after proving stability in `N`,

```text
I_T = stable_N wind(C_N on boundary R_T) in Z.
```

This definition reads a finite completed function on a contour.  Its later identification with a
divisor count is a theorem, not an input.  A relative index may replace it only after proving a
same-boundary factorization or transgression identity; the existing real-aperture `-1` cannot be
imported.

## Required theorem A: global finite-formation argument principle

Construct `R_T` and `C_N` before reading any zero and prove

```text
I_T = strictRightXiOrder(T).
```

Requirements:

- windows cofinal in the strict right half of the critical strip;
- boundaries source-selected and Xi-nonvanishing;
- stability under finite-to-entire SEM completion;
- the window lies strictly to the right of the critical line, so critical-line zeros are never
  enclosed;
- one strict-right zero forces `I_T >= 1`.

This theorem globalizes the existing zero-centred SEM winding certificate.  It is not yet in the
corpus.

## Required theorem B: direct subunit source law

Using literal integer formation and Poisson self-duality, prove directly that there is a
source-derived `s_T` with

```text
0 <= I_T <= s_T < 1
```

for every source-selected window.  Equivalent Ferrero--Washington form: `I_T > 0` forces an exact
restriction at every finite integer/Poisson formation depth, while source equidistribution violates
that restriction at one depth.

The existing constant `3 log 2 + pi/2 - 3 < 1` is only a clue.  It bounds a particular
archimedean Weil tail, not this rectangle winding.  It may be used here only after an exact
same-boundary decomposition proves that every other term cancels or has the required sign.

The proof must preserve unsquared Euler coefficients until the final boundary integral.  Squaring,
positive averaging, or replacing the source by a divisor ledger loses the cancellation and is
already closed by the corpus.

## Exact RH closure

Theorems A and B give

```text
0 <= strictRightXiOrder(T) = I_T < 1,
```

so `I_T = 0` for every cofinal window.  No Xi zero has real part greater than `1/2`; functional
equation gives the other half; hence RH.

## Hostile tests

1. **Boundary test:** if source-selected boundaries cannot be kept nonvanishing uniformly through
   finite-to-entire completion, theorem A fails.
2. **Crowd test:** any estimate containing `log T`, total zero count, or an on-line spacing term is
   not theorem B.
3. **Rajchman test:** Fourier decay alone cannot prove B because off-line Cauchy-pair clocks are
   Rajchman.
4. **Countermodel test:** the proof must fail for FE-symmetric shifted-Xi, Davenport--Heilbronn,
   Epstein, and Beurling countermodels at a named source step.  “Functional equation plus entire
   completion” is insufficient.
5. **Domain-matching test:** no index from a real aperture, circle, spectral ray, or other boundary
   may be subtracted from the rectangle index without an exact common-boundary identity.  Removing
   `[1/p]` coefficientwise remains forbidden.
6. **Circularity test:** neither `analyticOrderAt xi`, a selected Xi zero, nor an RH-equivalent
   global continuity/contraction premise may occur in the definitions or in theorem B.

## Current result

No direct subunit theorem is proved.  Audit establishes two nontrivial eliminations and one exact
target:

- amplification is not logically mandatory;
- Rajchman/equidistribution by itself is too weak;
- the live direct integer is global completed-SEM rectangle winding;
- no corpus theorem yet bounds that integer by a fixed subunit constant.

Next mathematical step is theorem A's fixed-window construction.  In parallel at the conceptual
level, theorem B must be sought as an exact finite-depth restriction, not inferred from unrelated
decay or an archimedean constant.

## Literature check

- Ferrero--Washington, *The Iwasawa invariant `mu_p` vanishes for abelian number fields*, Annals of
  Mathematics 109 (1979), 377--395.
- Lee--Palvannan, *An ergodic approach towards an equidistribution result of Ferrero--Washington*,
  arXiv:2207.09620: Weyl equidistribution is an ingredient in the vanishing proof, not a replacement
  for the all-depth congruence criterion.

## Log

- 2026-09-02 -- created after fresh Lean-corpus audit; naive phase-average and divisor-carrier
  variants rejected before conjecture was frozen.
- 2026-09-02 -- corrected after domain audit: removed unsupported subtraction of the real-aperture
  Stokes index from complex rectangle winding, and removed unsupported use of the archimedean-tail
  constant as a rectangle bound.
