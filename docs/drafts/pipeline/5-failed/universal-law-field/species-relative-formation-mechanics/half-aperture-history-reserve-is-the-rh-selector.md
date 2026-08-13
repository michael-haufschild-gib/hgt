# Failed overclaim: half-aperture history reserve is the RH selector

**Status:** `[FAILED AS SELECTOR] [POSITIVE SURVIVOR EXTRACTED] [NOT RH]`

## Claim tested

The Poisson-to-Boolean multiplicity reserve is summable exactly below half aperture.  Therefore its
properness should force the neutral point and unlock RH selection.

## Verdict

False.

## Exact counterreason

For every \(0<t<1/2\),

\[
 0<\sum_pR_p(t)<\infty.
\]

Hence finiteness defines an open chamber, not a unique neutral locus.  At \(t=0\), the reserve
vanishes, but no source law proved here forces vanishing rather than finite positive action.
Functional-equation symmetry only sends \(t\) to \(-t\); it does not identify complete
multiplicity histories labelwise.

## Positive survivor

The failed selector exposes two unconditional theorems:

1. exact Poisson--Boolean--history information conservation and the sharp all-prime threshold;
2. a predicted sharp prime--valuation asymptotic for the independently constructed Stokes
   coenergy.

They are recorded in ULF-SRFM-2 and ULF-SRFM-3.

## Replacement requirement

Selection needs a global formation/properness law stronger than finite action:

> bounded observer formation and bounded action must make the complete source-history lift compact,
> while every nonneutral functional-equation orbit must escape every such compact lift.

The reserve supplies a candidate vertical action but not this source-derived properness theorem.
