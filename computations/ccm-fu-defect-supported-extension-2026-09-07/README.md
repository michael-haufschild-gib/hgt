# Extensions selected from negative support

Numerical evidence only; no output is a Lean premise. The
[question and protocol](../../../1-in-progress/ccm-fu-defect-supported-extension.md)
were frozen before execution.

All8860 saved states through cutoff32 were reconstructed. Among them,
all3949 certified proper states with a negative nonempty coordinate admit
a certified or terminal successor selected from the union of those negative
labels. Every saved cutoff also admits a complete certified path that obeys
this rule whenever the union is nonempty. There were no failures.

The exact all-cutoff extension statement remains open. Selecting a prime
inside a negative label can create other defects in the same operation;
these finite results do not bound that cost at arbitrary cutoffs.

## Reproduction and limits

- `screen.py` reads the original `defect-reserve-reanalysis.json` and
  `subset-states.csv` in the sibling `ccm-fu-adaptive-prime-energy-2026-09-06`
  record. Place copies beside the script when reproducing on RunPod.
- The main reconstruction uses the isolated late-prime head identity and
  subset inversion, retaining every squarefree source label. Every good
  energy, defect energy and certificate agrees with its saved value at the
  original tolerance `1e-12*max(1,B)`. The same tolerance classifies signs.
- The graph checks every eligible state and exhaustively constructs policy
  and unrestricted reachability. `summary.json` stores a complete path for
  each cutoff, counts and reconstruction errors. Failure fields would be
  retained; none occurred.
- Independent80-digit reconstruction was prescribed for failed cutoffs;
  no failure triggered it. The numerical passes therefore have the
  saved-data reconstruction checks, not a new arbitrary-precision audit.
- Supplied RunPod endpoint, eight worker processes, numerical-library
  thread counts one,60-second foreground deadline. Runtime0.085885seconds.
- Downloaded output and verified script, output and both input hashes
  against the remote files. Foreground worker pool ended normally; all
  four owned remote files and their temporary directory were removed.

The separate [negative-support transport theorem](../../../3-formalized/ccm-fu-negative-support-transport.md)
is analytic and holds at every cutoff. It says that any strict total defect
decrease must select a prime in negative support. It neither proves the
tested extension implication nor uses these numerical observations.
