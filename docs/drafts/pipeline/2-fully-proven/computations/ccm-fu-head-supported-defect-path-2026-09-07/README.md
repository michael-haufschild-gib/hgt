# Complete paths with defects confined to the head

Numerical diagnostic only. No result here is a Lean premise or formal
nonexistence theorem. The [questions](../../../1-in-progress/ccm-fu-head-supported-defect-path.md)
and original energy budget were frozen before execution.

All 8860 saved subset states through cutoff 32 were processed. Complete
certified paths with no negative nonempty oriented coordinates fail to
exist in this dataset at cutoffs 21–29 and 31–32. The minimum possible
maximum number of simultaneously negative nonempty coordinates along a
certified complete path is exactly one at these cutoffs and zero elsewhere.
This optimum comes from exhaustive dynamic programming.

There are 183 admissible states with no admissible successor, all reachable
through admissible predecessors. Every field at each affected cutoff was
independently reconstructed at 80 decimal digits from the defining divisor
defect and Abel sum. The complete path graphs and all failed states and
successors agree with the saved-data reconstruction.

The first stalled state is M=21, P={7,11,13,19}, reached in order 19,13,11,7.
Here B≈0.530585851982442 and Phi(P)≈0.498369727003215.

| Next prime | Successor Phi | Negative nonempty label | Original certificate |
|---|---:|---|---|
| 2 | 0.255925790301312 | {3} | passes |
| 3 | 0.457018584409562 | {2} | passes |
| 5 | 0.564479315223339 | {2} | fails |
| 17 | 0.595734486457666 | none | fails |

The successful exits create nonempty defects. The order
2,3,5,7,11,13,17,19 is a certified complete path at M=21. Its negative
nonempty coordinate moves from {3} after selecting 2 to {5} after selecting
3, then disappears after selecting 5. Every intermediate coordinate and
the complete signed endpoint remain in the output.

This rejects the restricted strategy at the numerical-evidence level.
Original reserve extension, PE4, SD1 and RH remain open. It supplies no
all-cutoff bound on defect count. The [formal positive comparison](../../../3-formalized/ccm-fu-mixed-transverse-compensation.md)
retains created defect energy without assuming any numerical value here.

## Execution and reproduction

- `screen.py` reads `defect-reserve-reanalysis.json` and `subset-states.csv`
  from the sibling `ccm-fu-adaptive-prime-energy-2026-09-06` record. Copies
  of those inputs were placed beside the script on RunPod.
- Main test recovers heads from the isolated late-prime energy identity,
  performs finite subset inversion, and retains every squarefree source
  label. Every good/defect energy and certificate is checked against its
  saved value. No source channel is regenerated in this main test.
- Tolerance is `1e-12*max(1,B)`, including sign classification. Independent
  80-digit source reconstruction audits every state at affected cutoffs.
- Supplied RunPod endpoint; eight worker processes, numerical library
  thread counts one, 60-second foreground deadline. Completed run took
  0.311930 seconds. Initial invocation failed before producing results
  because remote Python 3.8 lacks `int.bit_count`; the compatibility fix
  uses binary-string bit counts and changes no mathematical question.
- `summary.json` retains every failure and successor, successful complete
  paths, optimal paths, precision audits and input hashes. `SHA256SUMS`
  records script, output and both original inputs. All hashes were verified
  locally after download.
- Foreground run and worker pool terminated. All owned remote files were
  deleted after download; no computation remains running.

The computation-record directory does not promote numerical results to proofs.
