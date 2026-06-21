# R67 — transient lubricated index

**Verdict:** DEAD END / known trace-regularization warning.

## Setup
- Seed RandomNode: `The role of substrate friction in screening hydrodynamic interactions between defects`.
- STEP 1 cold list + STEP 2 rng `3`: topic `Frictional screening in bacterial colony swarming`.
- STEP 3 cold list + STEP 4 rng `6`: NODE `Slime or EPS layers acting as transient lubricants`.
- Standing-order target pick: file rng `1` -> `docs/consolidated/08-conjectures-required.md`; topic rng `24` -> `G-C10. Source-built faithful-index object`.
- STEP 5 constraint: transient regularization can change measured friction/positivity without changing the underlying object.
- STEP 8 selected transfer by Levenshtein: `lubricated source positivity is not source-built rigidity` (`44`).
- STEP 9 method rng `17` = change representation.
- STEP 11 method rng `1` = split into subclaims.

## Computation
Archive script: `computations/2026-06-21-penrose-r67-transient-lubricated-index.py`.

Transient positive regularizer `Q -> Q + eps I`:

| eps | neg_index | min_eig | trace |
|---:|---:|---:|---:|
| 0.20 | 0 | 0.1200 | 3.0100 |
| 0.10 | 0 | 0.0200 | 2.5100 |
| 0.08 | 0 | 0.0000 | 2.4100 |
| 0.05 | 1 | -0.0300 | 2.2600 |
| 0.02 | 1 | -0.0600 | 2.1100 |
| 0.00 | 1 | -0.0800 | 2.0100 |

## Split-subclaim Check
- Transient smoothing can hide a negative direction: true.
- Trace remains positive throughout: true.
- Source-built faithful positivity follows: false.

## Reading
This is the known G-C10/G-C18 warning: trace or transient regularization is not a faithful integer-index proof.
