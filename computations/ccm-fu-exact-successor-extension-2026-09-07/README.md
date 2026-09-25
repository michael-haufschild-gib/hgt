# Exact successor-energy extension

Numerical evidence only. No output is a Lean premise. The
[question and protocol](../../../1-in-progress/ccm-fu-exact-successor-extension.md)
were frozen before execution.

For every saved state P, the envelope is the maximum of its energy and
all immediate successor energies. The original diagonal is the fixed
budget. All8176 admitted proper states through cutoff32 have an admitted
successor; no failures occurred. All8860 saved states were processed.
The envelope admits826 states rejected by the geometric certificate.
Every saved cutoff has a complete path in this larger admitted class.

The result supports a specific extension candidate that retains exact
signed overlaps. It proves no all-cutoff statement, complete source bound,
or RH result. The exact mixed comparison and terminal endpoint remain open.

## Reproduction and validation

- `screen.py` reads the existing `subset-states.csv` and
  `defect-reserve-reanalysis.json` from the sibling
  `ccm-fu-adaptive-prime-energy-2026-09-06` record. Place copies beside it on
  RunPod. Every state energy is cross-checked between both inputs, and each
  cutoff must contain the complete subset cube. No channels are regenerated.
- Original tolerance: `1e-12*max(1,B)`. The complete reachability calculation
  retains a path for every cutoff in `summary.json`.
- Independent80-digit source reconstruction was prescribed for every failed
  state and its first and second successors. No failure triggered that audit.
- Supplied RunPod endpoint; eight worker processes; numerical-library thread
  counts one;60-second foreground deadline. Runtime0.059853seconds.
- Downloaded output; remote and local hashes matched for the script, output
  and both inputs. The foreground pool exited normally. Four owned remote
  files and their temporary directory were removed.

SHA-256:

- Script: `1ba5f218b46c879fb19b51ce2a5dcae0b3e56468f407099cd3b059c02fb27e53`.
- Output: `7bbfb2fff054d1d24b18a0f1eff7a45be01cf841b047b1200a17394b0a742af1`.
- CSV input: `ba22442cb19cf20b5df1e9cc07d57c67d4105963a2a7cb75b5ab96c53e225fd9`.
- JSON input: `c6542367707c793fcf00675252e0b67e7bf7786a7a87769971dd4c2bcc944ff5`.
