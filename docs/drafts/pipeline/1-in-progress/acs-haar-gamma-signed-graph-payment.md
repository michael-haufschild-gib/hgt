# Pay the signed Haar Gamma graph from the actual divisor source

- **ID:** acs-haar-gamma-signed-graph-payment
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Route:** ACS: full-source effectivity → Hodge index → RH.
- **Parent:** [joint Haar payment](acs-haar-subcritical-divisor-operator.md)
- **Target:** Pay the actual signed Gamma/central-mass remainder and
  valuation completion cost from the retained divisor reserve, with
  every low index and both original poles present.

## Source mechanism

The exact Gamma off-diagonal is minus the signed rectangle pairing.
The corpus gives a positive exponential expansion of its Levy density.
For two equally oriented balanced Haar cells, the four-point mixed
kernel difference is nonpositive. Centering at the two internal cell
boundaries cancels the one-variable terms by the exact zero means.
This should prove that the original Gamma matrix has nonnegative
off-diagonal entries, including touching cells.

The resulting exact signed graph has a positive row potential minus
an additive difference-square form. The original arithmetic defect
has a positive divisor difference-square form with a charged absent
root. The target is their joint payment, preserving the row potential,
cell-weight correction and Euler-minus-outgoing completion cost.

## Required work

1. Prove the actual Gamma sign and signed graph decomposition, including
   all integrability and touching-boundary claims.
2. Compare the additive graph with the rooted divisor graph using an
   explicit allocation. A generic path certificate would only restate
   the missing inequalities; its supersolution and packing conditions
   must be proved for the original source.
3. Retain the exact diagonal and poles in the full signed Haar sign.
   A sign theorem for individual cross terms alone is not completion.

## Existing checked inputs

- `GammaFiniteMeanZeroOffDiagonal`: exact original rectangle expansion.
- `GammaMeanZeroCrossingBound`: integrability at touching boundaries.
- `RHTower.ArchimedeanAnomaly.archLevyDensity_eq_tsum` and
  `completelyMonotone_archLevyDensity`: original positive kernel series.
- [Actual divisor occupation](../3-formalized/acs-haar-subcritical-source-transport.md):
  original-domain, fully summable identity with its nonnegative boundary cost.
- [Original pole payment](../3-formalized/acs-haar-prime-defect-pays-poles.md).

## Validation

Exact-file `lake --old env lean` checks; required dependency oleans only.
No umbrella build, axiom check, web search, novelty check or numerical
experiment. Joint sign remains unproved.
