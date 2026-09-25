# CLG/TTF even energy certificate: discovery artifacts

These archived calculations were performed before the Runpod-only instruction in this task. They were not executed on Runpod. No mathematical calculation was rerun after that instruction: their results were already known. All future exploratory computations must run on the specified Runpod host, use multicore Python where parallel work is available, and return results to this directory family.

The artifacts guided selection of a finite algebraic certificate. They supply no premise to a Lean theorem. The Lean source independently proves every polynomial identity and sign inequality using exact symbolic proofs.

## Artifacts

- `clg_even_inner_explore.py`, `clg_even_inner_polys.json`: exact source polynomials through twelve and seven reflected moments; exploratory state comparisons.
- `clg_even_inner_det.py`, `clg_even_inner_det.json`: an intermediate determinant and head expression. This uses an earlier correction comparison and is not the final determinant.
- `clg_even_inner_transform.py`, `clg_even_inner_unit.json`: stronger correction `Q(3Q−6/19)`, relative shear, coupled gap substitution and the final 5368-term unit determinant candidate.
- `clg_even_inner_minorant.py`, `clg_even_inner_minorant.json`: the 95-term lower polynomial, degree at most four in each coordinate, and its 125 Bernstein coefficients.

The archived scripts retain their original `/tmp/clg_even_inner_*` paths and are provenance records, not a request to rerun a known calculation. Exploratory failures in a larger independent parameter box are not counterexamples for the actual theta orbit and do not retire a route.

## Formal status

The exact source derivatives through twelve, all seven unit moment identities, the literal source normalization, the positive quartic and all twelve nonnegative remainder blocks are checked. Final determinant incidence and actual positive-definiteness capstones are being checked. The current research card records the authoritative proof boundary.
