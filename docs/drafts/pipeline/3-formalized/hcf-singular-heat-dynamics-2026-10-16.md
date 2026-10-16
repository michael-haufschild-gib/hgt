# HCF: singular heat dynamics

Status: formalized. Paper proof, all three final direct Lean audits, and dependency-axiom audit complete.

## Corpus starting point

The current frontier map and actual Lean modules establish normal blocks, exact kernels and nullities, and the complete all-time block Jacobi census. They do not determine the heat-time multiplicity or local evolution of singular determinants. Complete source-sign control remains open.

## Conjecture loop

1. Reconsider source-facing ground simplicity through the existing derivative-chain and pole-forcing structure. Neither finite-dimensional ground structure nor a nonzero source functional alone excludes derivative chains; no simplicity claim follows.
2. Test exact heat unfolding: if the regular heads surrounding a rank are `n` and `n+d`, then the determinant of size `n+k` has heat-time zero order exactly `k(d-k)`.

3. The Wronskian mechanism predicts the same exponent, but would require a new all-rank Wronskian valuation engine. The current corpus instead supplies two-border condensation and exact meromorphic derivative orders. Use them to prove the heat Toda identity, then solve its multiplicity recurrence. This proof succeeds.
4. Test the resulting crossing law: the sign of the product at opposite small heat displacements is `(-1)^(k(d-k))`. The analytic nonvanishing factor makes this a direct consequence of the exact order. No source orientation is inferred.

## Exact contribution

At every positive actual heat time `a`, let `n` and `n+d` be consecutive regular Hankel heads. Then

`ord_a Δ_(n+k) = k(d-k)` for every `0 ≤ k ≤ d`.

There is an analytic nonvanishing germ `g` with

`Δ_(n+k)(t) = (t-a)^(k(d-k)) g(t)` near `a`.

Thus simultaneous singular sections have a completely determined heat-time order profile. This excludes excess vanishing beyond the block-determined order and fixes crossing versus tangency by block parity. It is an exact local desingularization, not a bound, RH equivalence, or conditional receiver. It does not show that singular contacts cannot occur or control the sign of the full prime–Gamma source.

## Dependency-closed proof

1. Existing actual moment derivatives are `μ'_r = -μ_(r+1)`. In the derivative of a determinant with consecutive rows, every row replacement except the last repeats another row and vanishes. Thus `Δ' = -K`, where `K` has its terminal row advanced once.
2. Differentiate `K` along its consecutive columns. Again only the terminal column survives, so `Δ'' = L`, where both terminal row and column are advanced once.
3. Existing two-border Schur condensation gives `Δ_(r+1) Δ''_(r+1) - (Δ'_(r+1))² = Δ_r Δ_(r+2)` wherever the preceding head is invertible. Existing isolated zeros and real analyticity extend this identity to every positive time, including simultaneous singularities.
4. At a nonflat analytic zero of order `m>0`, `f'/f` has order `-1`; its derivative has order `-2`. Since `f f''-(f')² = f² (f'/f)'` off the zero, the curvature numerator has exact order `2m-2`. All actual determinant orders are finite by the existing isolated-zero theorem.
5. Hence the integer orders in a normal block satisfy `m_k+m_(k+2)=2m_(k+1)-2`, with `m_0=m_d=0`. First differences are affine; the unique solution is `m_k=k(d-k)`.
6. Analytic order factorization supplies the nonvanishing factor. At opposite displacements its two values have positive product, so the determinant product has sign `(-1)^(k(d-k))`.

## Lean surface

- `HTGeometry/HankelHeatToda.lean`: consecutive-row differentiation, terminal-border differentiation, condensation.
- `HTGeometry/AnalyticTodaMultiplicity.lean`: exact curvature order, discrete multiplicity solution, reflection sign law.
- `RHTower/XiGaussianHeatTodaMultiplicity.lean`: unconditional `hcf_heat_toda`, `hcf_heat_block_multiplicity`, `hcf_all_time_heat_multiplicity`, `hcf_heat_singular_normal_form`, `hcf_heat_crossing_parity`.

Actual capstones take only positive heat time and rank/block indices. Generic helper assumptions are discharged by existing actual-source theorems.

## Validation

- Focused `lake --old build +<module>:olean` succeeded for all three modules. No full or umbrella builds.
- Final `lake env lean <actual-file.lean>` succeeded separately for all three source files, with no output or warnings.
- A separate `/tmp` audit printed axioms for all five capstones and five mathematical engine theorems. Every result uses exactly `propext`, `Classical.choice`, and `Quot.sound`.
- Both theorem-area umbrellas import the new modules; the current HCF frontier map records the exact dynamics and remaining source-sign obstacle.
- `scripts/formal_tools.py lint` ran. Its only errors concern three unrelated concurrent CHMD files missing from the RHTower umbrella: `CHMDComplexKernelReadout`, `CHMDMixedZeroOperator`, `CHMDStripFourierReadout`. The HCF modules have no lint errors. Concurrent files were preserved.
- Whitespace checks passed. No heartbeat changes, numerical experiments, added axioms, placeholder proofs, web searches, commits, or pushes.

## Constraints

No web, novelty searches, old research markdown, or numerical experiments. Use current Lean corpus and documented corpus search. Actual capstone must require no RH, source-sign, positivity, genericity, or nonzero-pivot assumption. Focused foreground builds only; final direct actual-file audits, standard-axiom audit, umbrella wiring, lint, cleanup.
