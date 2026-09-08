# Prescribed-prime repair under the exact successor envelope

Numerical evidence only. No output is a Lean premise. The
[statement and protocol](../../../1-in-progress/ccm-fu-forced-prime-repair.md)
were frozen before execution.

All 39,220 prescribed-prime choices from admitted proper states at the
saved integer cutoffs through 32 restore admission in at most two mergers.
The first merger already restores admission in 36,765 cases; the other
2,455 cases have a second-prime repair. No failure, infinite repair
distance or longer repair occurs. All 8,860 states were processed.

This strengthens the earlier finite evidence that some next prime
preserves admission. Here every prescribed first prime has a repair.
It supports the derived coverage bridge but proves no universal
extension statement, every-cutoff energy bound or RH result.

## Reproduction and validation

Run screen.py only on RunPod, with copies of subset-states.csv and
defect-reserve-reanalysis.json from the sibling
ccm-fu-adaptive-prime-energy-2026-09-06 record. All complete subset cubes
and energies were cross-checked between both inputs. The budget remains
the original diagonal, with tolerance 1e-12*max(1,B). No channels were
regenerated. Independent 80-digit source reconstruction was prescribed
for every failed comparison; no failure triggered that audit.

Eight cutoff workers, one-thread numerical libraries, a 50-second internal
alarm and a 60-second foreground deadline were used on the prescribed
RunPod endpoint. Runtime: 0.060543984 seconds. The foreground pool exited
normally. The output was downloaded and local/remote hashes matched.
A process scan found no remaining screen.py worker. Four owned remote
files and their temporary directory were removed. No larger scan is
scheduled.

SHA-256:

- Script:514f7429482a8114b938d163ca26b751f05ddaca6c951028498a84c59b89048f.
- Output:8b522271fca778f47495389211deb65ac8da9d9a65dce4879e62095474cd6fdd.
- CSV input:ba22442cb19cf20b5df1e9cc07d57c67d4105963a2a7cb75b5ab96c53e225fd9.
- JSON input:c6542367707c793fcf00675252e0b67e7bf7786a7a87769971dd4c2bcc944ff5.
