# R61 — B2 synchronous artifact counterexample

**Verdict:** DEAD END / grid-stability warning.

## Setup
- Seed RandomNode: `Coarse-graining can erase microscopic determinism, but it can also introduce artifacts mistaken for physical laws`.
- STEP 1 cold list + STEP 2 rng `8`: topic `Pseudorandomness from deterministic cellular automata`.
- STEP 3 cold list + STEP 4 rng `6`: NODE `Spectral artifacts can appear from synchronous updating`.
- Standing-order target pick: file rng `1` -> `docs/consolidated/08-conjectures-required.md`; topic rng `8` -> B2 two-lemma bridge.
- STEP 5 constraint: synchronized observation can manufacture a spectral/defect-looking signal.
- STEP 8 selected transfer by Levenshtein: `synchronous grid artifacts can fake off-seam transport defects` (`41`).
- STEP 9 method rng `16` = minimal counterexample.
- STEP 11 method rng `2` = attack as false.

## Computation
Archive script: `computations/2026-06-21-penrose-r61-b2-synchronous-artifact.py`.

NODE validation:
- deterministic Rule-90 center-cell time-series FFT peak `1.000`;
- random full-state projection FFT peak `0.801`.

Minimal B2 counterexample:
- constructed source-free oscillatory artifact with true residue/source charge `0`;
- synchronized offset `0` triggered `80` defect counts;
- half-period offset `0.5` triggered `0`;
- random offsets ranged `0..80`, mean `4.800`.

## Attack-as-false
The statement "grid-visible defect implies source-carrying transport defect" is false. It needs offset/desynchronization robustness or an actual logarithmic residue.

## Reading
This is a valid B2 guardrail: the detect lemma cannot use synchronous grid visibility alone. But it repeats prior grid-stability and sampling-alias warnings, and proves neither B2 lemma.
