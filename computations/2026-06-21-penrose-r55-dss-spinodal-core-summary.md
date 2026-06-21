# R55 — DSS-cross spinodal core warning

**Verdict:** DEAD END / existing gatekeeper.

## Setup
- Seed RandomNode: `Warm dark matter simulations often form artificial filament fragments from discreteness noise`.
- STEP 1 cold list + STEP 2 rng `9`: topic `Spinodal decomposition`.
- STEP 3 cold list + STEP 4 rng `3`: NODE `The unstable composition range lies inside the spinodal, not merely inside the miscibility gap`.
- Standing-order target pick: file rng `1` -> `docs/consolidated/08-conjectures-required.md`; topic rng `15` -> `DSS-cross (3b)`.
- STEP 5 constraint: the true linear-instability core is strictly smaller than the broad coexistence/plausibility region.
- STEP 8 selected transfer by Levenshtein: `period/nonperiod plausibility is only the miscibility gap` (`57`).
- STEP 9 method rng `18` = right theorem.
- STEP 11 method rng `1` = split into subclaims.

## Computation
Archive script: `computations/2026-06-21-penrose-r55-dss-spinodal-core.py`.

1. Source validation used the symmetric double-well `f(c)=c^4/4-c^2/2`: miscibility gap `[-1,1]`, spinodal core `[-0.577350,0.577350]`, ratio `0.577350`.
2. Height-12 integer-relation probes showed broad residual floors are not the core:
   - actual cross set `[1, gamma0, gamma1, pi^2]`: min residual `5.962e-04`;
   - random control `[1,u1,u2,u3]`: min residual `8.563e-05`;
   - planted relation `[1,a,b,2a-3b+5]`: residual `0`.
3. The finite Euler diagnostic for `S={2,3,5}` gave stable local rank for the first six regular coefficients (`1.790008e+00, 8.816104e-02, 1.630999e-03`), while the one-Frobenius `S={2}` coefficients collapsed to Bernoulli multiples of powers of `log 2`.

## Split-subclaim check
- Broad period/non-period or low-height PSLQ evidence is only an outer plausibility zone. The random control can have a smaller residual than the Stieltjes/period cross set at the same height.
- A planted exact relation is the actual "spinodal core" analogue, but this is generic integer-relation discipline, not new DSS-cross structure.
- The right theorem for the target is already known in the corpus: finite Euler Stieltjes trdeg equals prime-log corank, with the open monotonicity/Schanuel rung externalized.
- Therefore the transfer adds no new theorem or non-reducing invariant.

## Reading
The analogy is a gatekeeper only: do not promote "no low-height relation" or period/non-period plausibility to the DSS-cross core. The core remains the existing finite Euler `corank = Stieltjes-trdeg` equality plus the still-open corank-to-trdeg monotonicity rung.
