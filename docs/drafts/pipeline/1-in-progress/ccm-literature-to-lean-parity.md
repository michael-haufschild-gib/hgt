# CCM literature-to-Lean parity before frontier research

- **ID:** `ccm-literature-to-lean-parity`
- **Stage:** 1-in-progress
- **Type:** PRIMARY-LITERATURE COVERAGE / LEAN FRONTIER LEDGER
- **Started:** 2026-08-11
- **Scope:** whole Connes/CCM RH program: Route C1, CCM-FU, and Route O
- **Scientific status:** `[MECHANICAL INGESTION] [NOT NEW SCIENCE] [NOT AN RH PROOF]`

## Expanded operational goal

Treat Route C1 and Route O as one CCM program.  Close it only by a literal source theorem through
RH or a source-complete no-go/classification.  Before originating another CCM conjecture, make the
umbrella-reachable Lean corpus theorem-level complete for every unconditional primary-literature
result that lies ahead of it.  Only the residual after this parity audit is a scientific frontier.

## Acceptance rule

An item is `EXACT` only when umbrella-reachable Lean constructs the source-defined objects, states
the paper's hypotheses without strengthening or suppressing them, and proves the paper's endpoint
without `sorry`, `admit`, project axioms, opaque declarations, unsafe code, or computation.  Generic
operator infrastructure, an abstract surrogate, a conditional RH receiver, or an unwired file is
not exact coverage.  Numerical observations and convergence conjectures are recorded but never
formalized as theorems.

## Fixed primary-source ledger

| Source | Unconditional theorem relevant to CCM | Current Lean status | Required action |
|---|---|---|---|
| Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta function* | semilocal trace formula and quotient spectral realization | `PARTIAL`: rational adelic/Bruhat and trace-norm infrastructure exists; no theorem-level source audit yet | inventory exact numbered results against declarations |
| Connes--Consani, arXiv:1910.14368 | semilocal Fourier unitary; cutoff trace formula; projection/logarithmic-derivative sign criterion | `PARTIAL`: exact class-space pieces exist; source trace formula not identified end-to-end | formalize missing exact operator identities |
| Connes--Consani, arXiv:2006.13771 | Sonin compressed trace identity; archimedean Weil lower bound for support `[2^(-1/2),2^(1/2)]` with the paper's Fourier vanishing hypotheses | `MISSING`: continuous Sonin projections and trace ideals exist, but no theorem on the paper's concrete functional/operator | formalize source scaling representation, trace identity, and exact non-computational inequality; separately audit paper's numerical spectral bound |
| Connes--Consani, arXiv:2106.01715 | lower-semicontinuous restricted Weil form; spectral triples; exact zeta-cycle spectral theorem | `MISSING/PARTIAL`: many restricted-Weil and prolate pieces exist; no literal zeta-cycle theorem located | formalize exact circle periodization, orthogonal complement, and spectral characterization |
| Connes--Consani--Moscovici, arXiv:2310.18423 | semilocal Sonin Hilbert isomorphism; common de Branges image; Gamma-quarter Jacobi/metaplectic model; semilocal prolate operator | `PARTIAL`: Gamma density, moments, Jacobi recurrence, relative traces, and continuous Sonin pieces exist; exact Hilbert isomorphism not located | prove missing source-space isometries and identify every local surrogate |
| Connes--Consani--Moscovici, arXiv:2511.22755 | finite simple-even ground rank-one perturbation is self-adjoint in the Weil quotient; regularized determinant equals the ground Fourier transform; every transform zero is real | `PARTIAL`: literal finite matrix, ground shift, source/response completion, determinant lemma, and real-rooted completion exist; paper's eta-channel theorem is not packaged end-to-end | first implementation target |
| Connes--van Suijlekom, arXiv:2511.23257 | lower-bounded convolution ground-state Fourier real-zero theorem; continuous-kernel and finite-matrix variants | `PARTIAL`: finite paraorthogonal connector and zero-limit transfer exist; continuous theorem absent | formalize exact continuous theorem after finite CCM capstone |
| Connes, arXiv:2602.04022 | survey synthesis and finite CCM source statements | `AUDIT`: do not count restatements as new theorems | check only for genuinely stronger unconditional statements |

## First exact claim

For the literal finite restricted-Weil matrix of arXiv:2511.22755, assume exactly the source
paper's simple even lowest-eigenvector hypotheses and nonzero Dirichlet normalization.  Construct
the eta-channel rank-one perturbation of the physical logarithmic clock and prove:

1. the shifted Weil form descends to a positive-definite quotient by the ground line;
2. the perturbation is self-adjoint for that quotient metric;
3. its finite determinant is the exact resolvent/Fourier numerator;
4. the compactly supported ground Fourier transform is entire and every zero is real after the
   unchanged exterior logarithmic-clock spectrum is restored.

Existing branch-free source/response completion is stronger in one direction but does not replace
this claim: it may select the response channel, whereas the paper's theorem uses the constant
Dirichlet boundary and the assumed even simple ground.

## Dependency order

1. Package exact simple-ground/radical-line data for the literal published matrix.
2. Prove eta-channel activation from reflection-evenness and Dirichlet normalization.
3. Instantiate existing metric-adjoint and rank-one determinant lemmas at physical clock scale.
4. Add removable-singularity-filled finite Fourier transform and prove determinant equality.
5. Add exterior clock factor and the real-zero theorem.
6. Wire module into `RHTower.lean`; run file Lean, targeted module build, lint, and axiom audit.
7. Continue ledger in order of scientific leverage: arXiv:2006.13771, arXiv:2310.18423,
   arXiv:2106.01715, then arXiv:2511.23257.

## Gates

- [x] Existing corpus and failed-route audit checked before formalization.
- [x] Exact paper hypotheses and theorem text recovered from primary TeX.
- [x] Numerical convergence and experimental claims excluded.
- [ ] Finite arXiv:2511.22755 theorem exact and umbrella-reachable.
- [ ] Archimedean compressed positivity exact and umbrella-reachable.
- [ ] Semilocal Sonin/de Branges source isomorphisms exact and umbrella-reachable.
- [ ] Zeta-cycle spectral theorem exact and umbrella-reachable.
- [ ] Continuous Connes--van Suijlekom theorem exact and umbrella-reachable.
- [ ] Joint C1/O frontier recomputed only after parity closure.
