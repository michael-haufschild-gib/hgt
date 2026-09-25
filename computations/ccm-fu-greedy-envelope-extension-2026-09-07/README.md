# Least-energy exact-envelope extension: bounded RunPod evidence

Frozen question: at every proper actual state with current and all immediate
successor energies below the original diagonal B, does choosing the smallest
next energy (ties by smaller prime) preserve that entire successor envelope?
See the [frozen candidate](../../../1-in-progress/ccm-fu-greedy-envelope-extension.md).

The primary screen reads every saved subset state through cutoff32. It
cross-checks the original CSV energies against the saved defect-reserve JSON,
retaining tolerance `1e-12*max(1,B)`. It includes admitted states outside the
empty-state greedy path. Every choice within tolerance of the minimum is
checked, so a near tie with a failed envelope would trigger the prescribed
independent direct-source80-digit audit. No source channels are regenerated
unless that audit is triggered. There is no enlarged-cutoff screen.

## Result

- All8860 saved states were read and both complete energy tables agree within
  the fixed tolerance.
- All8176 eligible proper states admit the least-energy successor.
- No near-minimum candidate has a failed envelope: zero flagged states,
  zero failures, zero resolved near-tie cases.
- Consequently the prescribed80-digit failure audit was not triggered.
- Eight RunPod workers completed the screen in0.05915544182062149 seconds,
  under a60-second foreground deadline with numerical-library threads fixed
  to one. Every worker finished normally.

This strengthens the finite evidence from an existential successor to a
specific least-energy selection rule at every stored admitted state. It is
not an all-cutoff proof, a formal verification of these floating-point
values, or a premise in Lean. The required signed arithmetic inequality
remains open. No larger repeat is planned.

## Reproduction and integrity

Run `screen.py` from a directory containing the two existing input files
from `../ccm-fu-adaptive-prime-energy-2026-09-06/`. The output is `summary.json`.
The test ran only on the user-specified RunPod host, using eight processes.
The downloaded summary and local script match their remote hashes:

- `screen.py`: `6a6ecd86e73ffece4277db4799b6c8c4c2af19151722ec0a58a1b96f9e821139`.
- `summary.json`: `781d93f9ef9c389de16abc7f60e785584a43cfd8e09f9d67a757ce75b8682f72`.
- Input `defect-reserve-reanalysis.json`: `c6542367707c793fcf00675252e0b67e7bf7786a7a87769971dd4c2bcc944ff5`.
- Input `subset-states.csv`: `ba22442cb19cf20b5df1e9cc07d57c67d4105963a2a7cb75b5ab96c53e225fd9`.

The owned remote directory contained exactly the script, two inputs and
summary. After download and hash verification, a process check found no
worker with that directory as its working directory. All four files and
the owned directory were removed. No remote job remains.
