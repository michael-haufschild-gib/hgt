# Least-energy repair immediately outside successor admission

This directory records a finite diagnostic, not a proof of the selection
candidate or RH. The [frozen protocol](../../../1-in-progress/ccm-fu-greedy-forced-prime-repair.md)
was written before execution. No numerical result is used in Lean.

## Question

At fixed cutoff M, put B=Q_empty and let Psi(P) include Q_P and every
one-prime successor energy. From an admitted P, prescribe an unprocessed
prime r. If S=P+r fails admission, does the prime q minimizing Q_(S+q)
restore admission, including every successor of S+q?

Previous screens tested greedy choice within admission and existence of
some repair after a forced prime. Neither tested this deterministic choice
at a boundary state.

## Result

The screen reads all 8,860 saved states at cutoffs 1 through 32. It finds
2,455 forced transitions from admission to nonadmission, representing 515
distinct boundary states. In every case the least-energy choice restores
admission. No alternative within the frozen tolerance of the minimum
fails admission. The prescribed independent 80-digit reconstruction was
therefore not triggered.

Every alternative, its energy, its full successor envelope and a maximizing
successor are retained in `summary.json`, together with all supporting
admitted parents and prescribed primes. CSV and JSON energies were
cross-checked at each cutoff using the frozen tolerance
`1e-12*max(1,B)`. This is a finite pass, not an all-cutoff comparison, an
exact certificate, or evidence of compatible exhaustive selection.

## Execution and provenance

- Supplied RunPod host: `157.157.221.29:27094`.
- Eight independent cutoff workers; numerical-library thread counts one.
- Reported elapsed time: 0.05829610675573349 seconds.
- Internal deadline 50 seconds; external deadline 60 seconds with a
  five-second kill grace. Pool workers retain terminating signal handlers
  so exception cleanup can reap them.
- Inputs reused from `../ccm-fu-adaptive-prime-energy-2026-09-06/`.
  The primary screen regenerates no arithmetic channels.
- Script and downloaded output hashes match their remote counterparts.
  All four owned remote files and their temporary directory were removed;
  the subsequent process scan found no owned worker.
- No larger or repeated scan is scheduled.

SHA-256:

| File | Hash |
| --- | --- |
| `screen.py` | `2fa7a22b9581f3ab717b5f1115fcc0c1797a8ec4cbeb8b7559ba534ba66ee845` |
| `summary.json` | `4cdaf037972be661b19dce1cd8ecf9f18e3f1f05142c8994334cd9bfe3d090eb` |
| Input `subset-states.csv` | `ba22442cb19cf20b5df1e9cc07d57c67d4105963a2a7cb75b5ab96c53e225fd9` |
| Input `defect-reserve-reanalysis.json` | `c6542367707c793fcf00675252e0b67e7bf7786a7a87769971dd4c2bcc944ff5` |

## Mathematical implication and remaining test

The result selects a concrete rule for an unresolved boundary case. A proof
must use minimum immediate energy to control the mixed interaction with
every other successor, retaining the forced prime's full third difference.
Immediate minimality alone has no such implication for arbitrary signed
fields. The arithmetic comparison remains unproved.
