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

An item is `EXACT` only when umbrella-reachable Lean constructs the source-defined objects,
internalizes admissibility in the objects' types, proves every scientific hypothesis from those
definitions, and proves the paper's endpoint without proposition-valued premises, `sorry`, `admit`,
project axioms, opaque declarations, unsafe code, or computation.  Generic
operator infrastructure, an abstract surrogate, a conditional RH receiver, or an unwired file is
not exact coverage.  Numerical observations and convergence conjectures are recorded but never
formalized as theorems.

## Fixed primary-source ledger

| Source | Unconditional theorem relevant to CCM | Current Lean status | Required action |
|---|---|---|---|
| Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta function* | semilocal trace formula and quotient spectral realization | `PARTIAL`: rational adelic/Bruhat and trace-norm infrastructure exists; no theorem-level source audit yet | inventory exact numbered results against declarations |
| Connes--Consani, arXiv:1910.14368 | semilocal Fourier unitary; cutoff trace formula; projection/logarithmic-derivative sign criterion | `PARTIAL`: exact class-space pieces exist; source trace formula not identified end-to-end | formalize missing exact operator identities |
| Connes--Consani, arXiv:2006.13771 | Sonin compressed trace identity; archimedean Weil lower bound for support `[2^(-1/2),2^(1/2)]` with the paper's Fourier vanishing hypotheses | `PARTIAL-EXACT`: source-normalized integrated scaling, Haar involution/adjoint, cutoff-one Sonin projection, and positive compressed Gram operator are unconditional and umbrella-wired; trace-classness, trace identity, and inequality remain open | formalize source trace-class bridge, trace identity, and exact non-computational inequality; separately audit paper's numerical spectral bound |
| Connes--Consani, arXiv:2106.01715 | lower-semicontinuous restricted Weil form; spectral triples; exact zeta-cycle spectral theorem | `MISSING/PARTIAL`: many restricted-Weil and prolate pieces exist; no literal zeta-cycle theorem located | formalize exact circle periodization, orthogonal complement, and spectral characterization |
| Connes--Consani--Moscovici, arXiv:2310.18423 | semilocal Sonin Hilbert isomorphism; common de Branges image; Gamma-quarter Jacobi/metaplectic model; semilocal prolate operator | `PARTIAL`: Gamma density, moments, Jacobi recurrence, relative traces, and continuous Sonin pieces exist; exact Hilbert isomorphism not located | prove missing source-space isometries and identify every local surrogate |
| Connes--Consani--Moscovici, arXiv:2511.22755 | finite simple-even ground rank-one perturbation is self-adjoint in the Weil quotient; regularized determinant equals the ground Fourier transform; every transform zero is real | `CONDITIONAL SOURCE THEOREM`: literal finite matrix, unconditional ground shift, source/response completion, determinant lemma, and real-rooted completion already exist; paper does not discharge simplicity/evenness or convergence | do not add a hypothesis-packaging theorem; only an unconditional proof of the literal eta-channel assumptions would move parity |
| Connes--van Suijlekom, arXiv:2511.23257 | lower-bounded convolution ground-state Fourier real-zero theorem; continuous-kernel and finite-matrix variants | `PARTIAL`: finite paraorthogonal connector and zero-limit transfer exist; continuous theorem absent | formalize exact continuous theorem after finite CCM capstone |
| Connes, arXiv:2602.04022 | survey synthesis and finite CCM source statements | `AUDIT`: do not count restatements as new theorems | check only for genuinely stronger unconditional statements |

## First exact claim

Formalize the unconditional Connes--Consani archimedean compressed-trace theorem of
arXiv:2006.13771 on the paper's concrete test algebra, scaling representation, and Sonin
projection.  The final closed statement universally quantifies over the test function and proves
the source inequality from its intrinsic support and Fourier-vanishing conditions; it must not
take the inequality, a spectral bound, a positivity interface, or a numerical certificate as a
premise.  Required endpoints are:

1. multiplicative convolution, involution, and Fourier character identities on exact smooth
   compactly supported tests;
2. the unitary scaling representation on even `L2(Real)` and its integrated operator `rho(g)`;
3. the concrete physical and Fourier cut projections and their Sonin intersection projection;
4. trace-classness and positivity of `rho(g) S rho(g)^*`;
5. the exact trace-remainder identity with the archimedean Weil distribution;
6. the source inequality, without importing the paper's floating-point spectral estimates.

The published proof's bound `gamma approximately 2.94355` is numerically sourced.  Under the
no-computation rule it is not an admissible premise.  The formal proof must replace that step by an
exact analytic estimate, or record a genuine rigor gap in the source theorem and formalize the
strongest unconditional trace identity preceding it.

## Dependency order

1. Audit the source proof's non-computational lemmas and isolate the exact missing spectral bound.
2. Reuse the corpus's continuous `L2`, Fourier, projection, and trace-ideal infrastructure.
3. Formalize source test algebra and integrated scaling representation.  Integrated L1 scaling,
   contractivity, Haar involution, and adjoint law are complete in
   `CCMArchimedeanIntegratedScaling.lean` and `CCMArchimedeanScalingStar.lean`.
   The literal half-line projection `P`, Hardy projection `F P F⁻¹`, involution
   `H = 2 F P F⁻¹ - 1`, intrinsic Schwartz multiplier, and exact cross-Hardy-block decomposition
   are complete in `CCMArchimedeanQuantizedCalculus.lean`.  This is only the algebraic reduction
   preceding Lemma `quantsmooth`; it does not count as trace-class coverage.
4. Formalize exact Sonin projection and compressed positive trace.  Cutoff-one projection and
   bounded-operator positivity are complete in
   `CCMArchimedeanSoninCompressionPositive.lean`; trace-classness and trace nonnegativity remain.
5. Formalize trace-remainder identity.
6. Prove an exact analytic replacement for the numerical spectral step, or classify the source
   endpoint as not presently unconditional at published proof level.
7. Wire every completed exact module into `RHTower.lean`; run file Lean, targeted module build,
   lint, and axiom audit.
8. Continue with arXiv:2310.18423 and arXiv:2106.01715.  Revisit arXiv:2511.22755 only if its
   simple-even eta-channel hypotheses are discharged unconditionally.

## Gates

- [x] Existing corpus and failed-route audit checked before formalization.
- [x] Exact paper hypotheses and theorem text recovered from primary TeX.
- [x] Numerical convergence and experimental claims excluded.
- [x] Conditional arXiv:2511.22755 hypothesis packaging rejected as non-progress.
- [x] Source-normalized integrated scaling representation exact and umbrella-reachable.
- [x] Archimedean compressed bounded-operator positivity exact and umbrella-reachable.
- [ ] Archimedean compressed operator trace-class and trace positivity exact.
- [ ] Semilocal Sonin/de Branges source isomorphisms exact and umbrella-reachable.
- [ ] Zeta-cycle spectral theorem exact and umbrella-reachable.
- [ ] Continuous Connes--van Suijlekom theorem exact and umbrella-reachable.
- [ ] Joint C1/O frontier recomputed only after parity closure.
