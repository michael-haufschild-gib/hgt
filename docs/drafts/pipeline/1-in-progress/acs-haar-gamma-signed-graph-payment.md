# Pay the signed Haar Gamma graph from the actual divisor source

- **ID:** acs-haar-gamma-signed-graph-payment
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Route:** ACS: full-source effectivity → Hodge index → RH.
- **Parent:** [joint Haar payment](acs-haar-subcritical-divisor-operator.md)
- **Target:** Pay the actual signed Gamma/central-mass remainder from
  the retained divisor reserve, with
  every low index and both original poles present.

## Source mechanism

The actual Gamma off-diagonal is minus the signed rectangle pairing.
`TheHaarGammaCrossTermsArePositive` proves its full summable expansion
`J_ab=sum_k U_a(2k+1/2)*V_b(2k+1/2)>=0` for a<b. The two Laplace
moments have proved signs, and original rectangle integrability pays
the complete series even when cells touch.

`TheHaarGammaDebtIsAnAdditiveGraph` proves the exact signed graph in
`u_a=sqrt(2a+1)*d_a` and the full original identity
`W(h)+G_X(u)=D_X+P(h)+sum_a V_X(a)*u_a^2`, with nonnegative graph
energy G_X and explicit signed potential V_X. Both original pole moments
and outgoing charges remain. The arithmetic defect has a positive
divisor difference-square form with a charged absent root. The target
is their joint payment, preserving the signed potential, cell-weight
correction and Euler-minus-outgoing completion cost.

The exact full-Weil identity uses D_X directly. The additional valuation
completion cost T_Q must be retained if the occupation representation
is used to estimate D_X.

## Required work

1. Completed in Lean: actual Gamma sign, complete Laplace series and
   signed graph/full-Weil decomposition, including touching boundaries.
2. Compare the additive graph with the rooted divisor graph using an
   explicit allocation. A generic path certificate would only restate
   the missing inequalities; its supersolution and packing conditions
   must be proved for the original source.
3. Retain the exact diagonal and poles in the full signed Haar sign.
   A sign theorem for individual cross terms alone is not completion.

## Existing checked inputs

- [Actual positive Laplace graph and full-Weil identity](../3-formalized/acs-haar-gamma-positive-laplace-graph.md):
  every paper claim formalized; all three exact-file Lean checks passed cleanly.
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
