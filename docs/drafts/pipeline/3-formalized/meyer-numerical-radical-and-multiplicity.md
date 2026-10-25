# Meyer numerical radical and multiplicity

- **ID:** qii-meyer-numerical-radical
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/q-ii-source-effectivity-and-linear-degree.md
- **Statement:** Ordinary trace radical consists exactly of sources vanishing at every Xi point; genuine Poisson boundaries require every lower jet to vanish. Equality is equivalent to simplicity. Ordinary trace positivity is equivalent to RH alone.

## Paper proof [PROVED HERE]

The actual finite causal section realizes one prescribed raw Mellin jet, with
every other divisor jet zero. Choose a source representative of this genuine
cohomology class. The zeroth-jet representative `e_rho` has Mellin value one
at `rho` and zero at every other divisor point.

The trace of the product of two convolution operators is
`sum_rho m(rho) M_g(rho) M_h(rho)`. Pairing `g` with an appropriate scalar
multiple of the arithmetic sharp of `e_rho` reads
`normSq(m(rho) M_g(rho))`. Thus vanishing of every real mixed trace is
equivalent to vanishing of all zeroth values. Full arithmetic jet separation
identifies the actual Poisson boundary with vanishing of every lower jet.

If every multiplicity is one, these kernels agree. If `m(rho)>1`, the source
with first jet one and all other jets zero lies in the trace radical but is
not a boundary. The source with only jet `m(rho)-1` nonzero is nonprincipal,
but its convolution square has every lower jet zero by the Hasse product
rule. Conversely, at simple points a square with zero value has zero value
before squaring. This proves the exact square-root closure criterion for the
actual boundary ideal.

On the critical line, each trace-square summand is a nonnegative norm square,
so RH implies positivity without a simplicity requirement. Conversely,
restricting actual source trace positivity to compact polar-multiplier
sources gives the already established Weil positivity criterion and hence RH.

For full scaling cycles, testing against the two fibres forces both pole
degrees to vanish. The remaining mixed trace readings are precisely the
zeroth Xi values. Balancing the fibre coordinates converts every source
boundary into a genuine principal cycle. Equality of the full numerical
radical with the principal cycles is therefore again exactly simplicity.

## Positive survivor and scope

The ordinary numerical quotient and the genuine Poisson quotient retain
different information at multiple zeros. The former retains values; the
latter retains the complete lower-jet algebra. This identifies the precise
extra simplicity obligation in a faithful degree construction. It does not
prove simplicity or RH, and no such premise is hidden in the equivalences.

## Lean certificate

Module: `ArithmeticCastelnuovoSeveri/MeyerNumericalRadicalAndMultiplicity.lean`.
Main declarations:

- `meyerSingleJetSource_jet`
- `meyerSourceTrace_radical_iff_values_zero`
- `meyerSourceTrace_radical_eq_boundary_iff_simple`
- `meyerSourceTrace_nonneg_iff_riemannHypothesis`
- `meyerCohomologyTraceDegree_sharp_squares_nonneg_iff`
- `exists_meyer_square_zero_nonprincipal_of_multiple`
- `meyerSource_square_root_boundary_iff_simple`
- `meyerScalingPair_radical_iff`
- `meyerScalingPair_radical_eq_principal_iff_simple`

Actual-file `lake --old env lean` check passed; all nine transitive axiom
audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
Umbrella import and README entry added. External novelty unverified.

## Current verification repair

A missing-olean attempt exposed a missing `zero_add` in the vertical fibre
calculation after cleanup. The rewrite was restored, and the horizontal unused
occurrence removed. The corrected source passed a fresh actual-file check;
all nine endpoint axiom audits again contain only `propext`, `Classical.choice`,
and `Quot.sound`. The mathematical statements are unchanged.
