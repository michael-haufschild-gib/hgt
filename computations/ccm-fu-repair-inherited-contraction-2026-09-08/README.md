# Inherited contraction of a greedy repair pair

Finite diagnostic under the [frozen protocol](../../../5-failed/ccm-fu-repair-inherited-contraction.md).
No numerical value is used as a Lean premise.

## Result

Among 8,805 comparisons from the saved boundary cases at cutoffs 1 through
32, 1,083 increase energy relative to their matching parent state. Failures
occur at cutoffs 17, 19, 23, 25, 27, 28, 29, 30, 31 and 32. Every flagged
positive increase was independently reconstructed and confirmed at 80 digits
from the original divisor defect and Abel sums. The output retains all
affected signed fields, alternative repairs, admission margins and ordering
checks. This rejects the proposed inherited-contraction mechanism at the
numerical-evidence level; it does not reject repair under the original budget.

The first witness has M=17, P={3,5,7}, forced r=11 and unique least-energy
repair q=2. Put S=P+11 and E=S+2. Rounded direct values are:

| Quantity | Value |
| --- | ---: |
| Original budget B | 0.3621784446 |
| Psi(P) | 0.2889678568 |
| Psi(S) | 0.3730515882 |
| Psi(E) | 0.2799869904 |
| Q_E-Q_P | 0.0192116496 |
| Q_(E+13)-Q_(P+13) | 0.0268448614 |

Both matching energies increase, yet the repaired envelope is below the
parent envelope. In this witness both repaired energies are below Q_S.
Thus failure of a comparison with each matching parent state does not rule
out using a different parent successor to control the full envelope.

## Source information exposed

The actual retained coordinates at P, indexed by empty, {2}, {11}, {13},
are approximately (-0.401460, 0.076795, -0.124546, -0.079927). Inserting
eleven and then two adds the corresponding signed coordinates to the head.
The positive two-coordinate contracts after forcing eleven, but the combined
pair still costs energy relative to P and P+13. The strict envelope comparison
uses a different original successor and retains all four coordinates.

The separate [analytic Lean certificate](../../../3-formalized/ccm-fu-seventeen-repair-envelope.md)
proves this witness and its stronger envelope comparison from the literal
source. No all-cutoff repair or selection statement is established.

## Execution and provenance

- Supplied RunPod host `157.157.221.29:27094`; eight cutoff workers and
  one-thread numerical libraries.
- Completed run: 0.10968971997499466 seconds, including direct reconstruction.
- Internal 50-second and external 60-second deadlines; worker signal handlers
  allow pool cleanup on parent exceptions.
- The first attempt terminated in its audit branch because the host's
  Python 3.8 lacks `int.bit_count`. The compatibility correction uses
  `bin(support).count('1')`. Inputs, test, thresholds and arithmetic precision
  were unchanged; the corrected run completed all cases.
- Script and output hashes match remote copies. All four owned remote files
  and their directory were removed after download; no owned worker remained.
- No larger or repeated experiment is scheduled.

| File | SHA-256 |
| --- | --- |
| `screen.py` | `cc0a3b53bc678ac0eb7bdbaf1dee8fab2483923b8e73f85dc03238ca08ef1e1d` |
| `summary.json` | `3c4602d35db5729e29302df7005c80b9c7cb93d9eb4eeaa127eae2c05adeb57a` |
| Input `boundary.json` | `4cdaf037972be661b19dce1cd8ecf9f18e3f1f05142c8994334cd9bfe3d090eb` |
| Input `subset-states.csv` | `ba22442cb19cf20b5df1e9cc07d57c67d4105963a2a7cb75b5ab96c53e225fd9` |

The boundary input is the unchanged output of
`../ccm-fu-greedy-forced-prime-repair-2026-09-08/summary.json`; the CSV is
from `../ccm-fu-adaptive-prime-energy-2026-09-06/subset-states.csv`.
