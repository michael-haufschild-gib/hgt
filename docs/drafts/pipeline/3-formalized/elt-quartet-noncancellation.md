# A single top quartet cannot cancel its high current

- **ID:** ELT-QUARTET-CURRENT
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ELT-PHASE; the single-quartet question in §2.10
- **Statement:** In the finite-layer world, either the top contains two distinct positive ordinates, or the norm of the corrected prime current tends to infinity at every supercritical exponential speed.

## Paper mechanism

If the top has only one positive ordinate γ, reality and absence of real
zeros make its support `β±iγ`, with equal multiplicities m. The profile is

    m exp(πγ/4) exp(iγφ_a(t)) + m exp(−πγ/4) exp(−iγφ_a(t)).

Its norm is at least `m(exp(πγ/4)−exp(−πγ/4))>0`, uniformly in t,
by the reverse triangle inequality. Thus its oscillation cannot hide the
layer at any sufficiently large height. The complete normalized-current
error tends to zero and the reference mode grows, giving pointwise norm
divergence rather than only recurrent excursions.

The conclusion must be applied to the actual multiplicity-exact divisor.
Conjugation of `XiZeroCopy` supplies equality of multiplicities; it cannot
be assumed as an extra analytic input. A disjunctive theorem avoids assuming
that the top is a quartet.

## Consequence and limit

This removes phase cancellation as a loophole in comparisons aimed at
one quartet. It does not exclude the quartet: an independently proved
upper bound for this same corrected current and observation scale is still
missing. The full infinite remainder must remain in the proof.

## Status

`ExceptionalLayerTheory/ASingleTopQuartetCannotCancelItsCurrent.lean`:
`not_asymptoticAbscissaLaw_has_top_ordinate_dichotomy`.
Conjugation acts involutively on exact zero copies via
`DeningerDivisorSchwarzMonodromy`. The complete infinite remainder is
controlled by ELT-PHASE. Final `lake --old env lean` audit passed;
transitive axioms are exactly `propext`, `Classical.choice`, `Quot.sound`.
