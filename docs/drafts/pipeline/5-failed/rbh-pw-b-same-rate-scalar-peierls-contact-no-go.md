# RBH / PW-B same-rate scalar Peierls-to-contact no-go

- **ID:** RBH-PW-B-SRSC
- **Status:** RETIRED SUBROUTE
- **Failure:** same-rate causal source pairing cannot realize a nonzero
  one-branch B2 scalar contact.

## Exact obstruction

Each literal source leg is quadratic in its primary amplitude.  The two-event
native and full-circle causal pairings are therefore biquadratic, and
antisymmetry gives, for every `q`, branch `b`, and independent amplitudes
`a,d`,

`causalSourcePair q b b a d = 0`,

`fullCausalSourcePair q branch b b a d = 0`.

The explicit full-minus-native lift defect also vanishes at the same rate.
Consequently it cannot supply a missing same-branch B2 contact.

## Positive survivor

Only a **complementary-rate, metric-valued** carrier can remain.  Its two
source rates sum to `-6`, whereas a one-branch contact has clock `2s`; these
cannot agree at an Xi copy.  Thus the survivor must retain bidegree rather
than collapse the two causal legs to one total-clock scalar contact.  The
literal cross-branch angular product and its forced cross-gradient source are
the exact next object.

## Status

- Paper proof: dependency-closed from source homogeneity and two-event
  antisymmetry.
- Lean source: `ThetaCuspHawkingBMLiteralCyclicPeierlsSameRateNoGo.lean` and
  `ThetaCuspHawkingBMLiteralCyclicPeierlsClockDichotomyNoGo.lean`.
- Local audit: not claimed; direct check stops before elaboration because the
  required transitive `.olean` for `LiteralCyclicPeierlsLiftDefect` is absent.
