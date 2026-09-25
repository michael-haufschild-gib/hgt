# Coprime deletion multiplication-fibre scan

- **Status:** RETIRED BEFORE RUN; no numerical results produced.
- **Purpose:** test whether square-mass defect of coprime `p × q` deletion grids keeps one sign beyond the formally proved `2 × 3` cell.
- **Method prepared:** `scan.py` uses exact Python integers and `ProcessPoolExecutor`; intended ranges are all coprime pairs through `80` and all prime pairs through `300`.
- **Remote record:** an initial probe used an incorrectly transcribed host and is invalid evidence. Authentication to the exact supplied endpoint `157.157.221.29:27094` with `/Users/michael/.ssh/id_ed25519` was subsequently verified.
- **Why no scan ran:** stronger corpus inspection retired multiplication-fibre stabilization before computation: its cancellation count is generic Jordan overlap machinery and the proposed cofinal scalar count factors through a Dirichlet polynomial times `ζ²`. Running a broad sign scan cannot repair either failure.
- **Consequence:** no sign pattern, asymptotic, or conjecture is inferred from computation. Do not cite this folder as mathematical evidence. `scan.py` is retained only as an exact multicore reproducibility artifact; outputs `cases.csv` and `results.json` were never created.
- **Lean independence:** finite theorems in `CoprimeBlockCarryTransgression.lean` and `CoprimeBlockMultiplicationFiber.lean` use no numerical output.
