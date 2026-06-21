# R57 — faithful-index modulation quotient

**Verdict:** DEAD END / generic Morse-index discipline.

## Setup
- Seed RandomNode: `The sensitivity of pattern onset to nondimensionalization choices and hidden parameter scalings`.
- STEP 1 cold list + STEP 2 rng `20`: topic `Singularity formation in nonlinear dispersive equations`.
- STEP 3 cold list + STEP 4 rng `7`: NODE `Modulation equations for blowup parameters such as scale, phase, center, and frequency`.
- Standing-order target pick: file rng `1` -> `docs/consolidated/08-conjectures-required.md`; topic rng `29` -> `G-C18. Faithful-index rigidity`.
- STEP 5 constraint: blowup/inertia readouts must separate true unstable directions from neutral modulation parameters.
- STEP 8 selected transfer by Levenshtein: `modulation-neutral modes must be quotiented before reading faithful index` (`61`).
- STEP 9 method rng `14` = weaken.
- STEP 11 method rng `16` = minimal counterexample.

## Computation
Archive script: `computations/2026-06-21-penrose-r57-faithful-index-modulation.py`.

The NODE toy tracked four blowup modulation coordinates as `t -> T`:
- scale shrank from `1.00000` to `0.10000`;
- phase rate grew from `1.000` to `100.000`;
- center oscillated;
- frequency grew from `1.000` to `10.000`.

The weakened G-C18 test used a quadratic carrier with one true negative physical direction and four small neutral modulation directions.
- Raw negative inertia varied from `1` to `4` as the neutral dust signs changed.
- The modulation-quotiented negative index stayed `1`.
- Trace changed only mildly (`1.617232..1.682768`), so trace control did not protect the faithful integer readout.

Minimal counterexample:
- With no physical negative direction, neutral dust alone produced raw negative counts `0..4`.
- The quotient negative count stayed `0..0`.

## Reading
The surviving rule is: a G-C18 faithful-index readout must specify the neutral modulation/gauge quotient before asserting integer rigidity. This is useful for instrumentation and matches the target kill condition against trace-only control, but it is generic Morse-index bookkeeping. It supplies no source-built proof that the completed carrier forces the index to zero.
