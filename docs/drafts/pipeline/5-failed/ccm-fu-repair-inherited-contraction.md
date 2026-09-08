# CCM-FU: inherited contraction of the chosen repair pair

- **Stage:** 5-failed; inherited-contraction mechanism refuted in Lean.
- **Type:** [BRIDGE]; the general greedy repair rule remains open.
- **Goal:** Actual divisor source → renewable signed reserve → exhaustive
  prime selection → uniform signed Abel bound → RH.
- **Parent:** [greedy forced-prime repair](../1-in-progress/ccm-fu-greedy-forced-prime-repair.md).

## Frozen arithmetic question

Let B=Q_empty, let P be admitted under the full successor envelope, and
prescribe r for which S=P+r leaves admission. Choose q minimizing Q_(S+q),
with smaller prime breaking exact ties. Does this pair satisfy

`Q_(P+r+q+T) <= Q_(P+T)`

for T empty and for every singleton T={s} at an available prime distinct
from r,q? This would inherit every required endpoint bound from the actual
admitted parent. It is stronger than repair under B. The prior finite
repair pass does not determine whether its endpoints contract relative to
these particular parent energies.

The test distinguishes a direct inherited contraction proof from a repair
that must consume the parent's reserve. Failure rejects only this proposed
mechanism; it does not refute the greedy repair rule, general selection or RH.

## Frozen experiment

Reuse all boundary cases and supporting parents in the completed greedy
repair output, and the original full energy CSV at cutoffs 1 through 32.
Do not extend the cutoff range or change choices. Recheck stored energies,
admission, boundary status, and minimum choice against the CSV. Retain every
comparison and every positive increase exceeding 1e-12*max(1,B).

At every cutoff containing a failure, independently reconstruct the original
Mobius-divisor channels at 80 digits. Reconstruct every failed parent, its
forced state, every alternative repair and all first successors of these
states. Recheck admission, boundary status and the true minimizer. Report
unresolved distinct-prime orderings within 1e-60. For every failing comparison
retain both full signed fields, its increase, inherited reserve and final
margin below B. This permits analysis of the actual omitted reserve without
fitting a new budget. A floating-point witness still needs an analytic proof
before a Lean refutation is claimed.

Run only on the supplied RunPod host with up to eight cutoff workers,
one-thread numerical libraries, a 50-second internal deadline and 60-second
external deadline. Download results and hashes under the computation ledger;
remove owned files and workers. No repeated or larger scan is scheduled.

## Proof target

If contraction fails, the exact positive survivor to retain is the original
budget comparison: pair increase <= B-Q_(P+T), with all overlapping fibres
present. Determine from the complete source fields which signed terms create
the increase and which previously accumulated reserve pays it. Do not replace
that comparison by a generic receiver or assume an admitted endpoint.

## Source witness and positive comparison

The [completed experiment](../2-fully-proven/computations/ccm-fu-repair-inherited-contraction-2026-09-08/README.md)
finds 1,083 positive matching-energy increases among 8,805 comparisons.
Independent 80-digit reconstruction confirms every flagged increase. At the
first witness M=17, P={3,5,7}, r=11 and q=2, both matching energies increase,
but the full repaired envelope decreases. The inherited-contraction question
is refuted by the separate analytic Lean certificate below; the general
greedy repair rule remains open.

Write K_d for the literal unsigned channel at 17. The complete source at P
has only four coordinates:

`a=K_1-K_3-K_5-K_7+K_15`,
`b=-K_2+K_6+K_10+K_14`, `c=-K_11`, `d=-K_13`.

Analytic logarithm-series, harmonic Euler-constant and square-root enclosures
give a in [-.402,-.401], b in [.076,.078], c in [-.125,-.124], d in
[-.080,-.079], and B in [.360,.365]. The source profile, energy formulas and
final comparisons are checked in Lean in the
[complete source certificate](../3-formalized/ccm-fu-seventeen-repair-envelope.md).

Put S=P+11 and E=S+2. The exact relevant energies are
`Q_P=a²+b²+c²+d²`, `Q_S=(a+c)²+b²+d²`,
`Q_E=(a+c+b)²+d²`, `Q_(S+13)=(a+c+d)²+b²`, and
`Q_(E+13)=(a+c+b+d)²`. The same analytic boxes imply

- Psi(P)+1/20 <= B;
- B+1/200 <= Psi(S);
- 2 is the unique least-energy repair from S;
- Psi(E)+1/200 <= Q_S;
- Q_P+1/100 <= Q_E;
- Q_(P+13)+1/50 <= Q_(E+13).

The positive survivor is stronger than merely staying below B: both repaired
branches lie below the forced successor Q_S, already included in Psi(P).
A proof of general repair can therefore compare with a different original
successor, even where every comparison with its matching parent state costs
energy. No universal such comparison is established by this witness.

Both the negative mechanism statement and this strict positive survivor have
dependency-closed analytic proofs and targeted Lean checks. This retires only
the frozen matching-energy contraction claim, not the original repair rule.
