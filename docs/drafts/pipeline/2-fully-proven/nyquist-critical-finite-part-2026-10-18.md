# Critical Nyquist finite part and signed broad-source classification

- **ID:** nyquist-critical-finite-part-2026-10-18
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scope:** Independent BiScaleUncertainty; infinite-grid tail rigidity beyond Trap 5.
- **Parent:** `../1-in-progress/infinite-grid-tail-rigidity-2026-10-17.md`
- **Predecessor:** `../3-formalized/nyquist-weight-order-threshold-2026-10-17.md`
- **Count:** Uncounted candidate for connected package 16; 15 packages certified.
- **Field guide:** `formal/GaloisForLFunctions/BiScaleUncertainty/README.md`, read-only.
- **Paper:** `docs/reports/BiScaleUncertainty/NyquistCriticalFinitePart.md`
- **Closeout:** Paper proof complete. No Lean implementation started; no partial code or
  pending imports. Goal cleared by user; retain as a paper-only successor, uncounted.

## Proven paper statement

For the actual degree-m Nyquist Taylor residual at critical weight beta=m+1,
subtract its continuous mean density c=(m+1)^(m+1)/(2(m+2)!). The cell discrepancies
are absolutely summable with an explicit inverse-square bound, defining a finite
part B. For every fixed signed compact Lipschitz test H, the broad-test residual
has expansion c L integral_0^infinity H + B H(0) + O_H(1/L). For normalized
autocorrelations of actual fixed smooth compact sources, the leading coefficient
is c (integral f)^2/(2 integral f^2). Thus ordinary zero mean cancels critical
escape; nonzero mean gives linear escape despite vanishing rescaled source energy.

## Goal and novelty boundary

Package 15 gives logarithmic prefix growth and one nonnegative broad-source
divergence witness. It does not identify the finite part or classify signed-source
cancellation. The paper proves both from the actual cell producer.
The counterterm is continuous density c, integrated as c times cell width; it is
never a discrete counterterm inserted before floor summation. No Chebyshev or
positivity receiver premise occurs. No global uniform convergence or grid blindness
is asserted for the broad-source family. Source-dependent regularity constants
must be derived from the fixed smooth source, not inferred from energy alone.

## Plan and gates

1. Finish corpus applicability audit, including additive autocorrelation mass.
2. Prove explicit cell discrepancy, convergent primitive finite part, quantitative
   signed broad-test expansion, source classification and actual zero-mean witness.
3. Audit the dependency-closed paper proof and novelty boundary before new Lean.
4. Formalize the exact connected result with one foreground Lean process at a time.
5. Check every public declaration's axioms, direct leaves, imports, API index,
   formal lint and source hashes; promote and count only after the complete audit.

- [x] Well-posed source-pure candidate and attack mechanism.
- [x] Complete paper proof and internal novelty audit; no global priority claim.
- [ ] Exact Lean statements checked and axiom-audited.
- [ ] Counted significant contribution.

## Corpus evidence

Two completed deep searches: `/tmp/nyquist-critical-finite-part-deep.json` and
`/tmp/nyquist-critical-cell-discrepancy-deep.json`. Both returned partial=false,
no unfinished stages/errors, 20 candidates and 20 source arguments; all candidate
statements and source arguments inspected. First search mostly retrieved unrelated
multiplicative autocorrelation. Second supplied existing Taylor remainder bounds;
other candidates concern collars, arithmetic quadrature or unrelated kernels.
Prose/passages were screened for relevance; no exhaustive reading claim is made.
Inventory coverage was complete (73844/73848 files, zero pending); semantic coverage
was unmeasured and refresh deferred to the background indexer. Retrieved compiler
metadata was source-only. Package 15 ingredients have their separate Lean certificate.
Focused exhaustive text search found no critical Nyquist finite-part theorem.
This is an internal corpus boundary, not a global novelty claim.

Third search `/tmp/nyquist-critical-source-mean-deep.json` completed with partial=false,
no errors or unfinished stages; all 20 candidates and 20 source arguments inspected.
Inventory coverage: 73855/73855, zero pending. Semantic coverage unmeasured, refresh
deferred, source-only compiler metadata. The ordinary convolution mass identity is
a parent theorem; multiplicative autocorrelation hits do not apply. Direct inspection
of `SignedDyadicCollarPartition.lean` supplied the correct reflected convolution.

## Paper audit

The report proves |alpha_n-c delta_n|<=D delta_n/n<=D/n^2 with D=c 2^(m+1),
absolute convergence of B, the primitive bound 2(3D+2c)exp(-T), and signed
broad-test error (8D+4c)Lip(H)/L. It derives source regularity, signed Fubini,
normalized scaling and vanishing energy from actual compact C^2 sources. A fixed
bump and its difference with a disjoint translate realize both mean alternatives;
the latter has normalized correlation -1/2 at the separating lag. The cases n=1,
m=0, all L>0 and zero test H were checked. No absolute integrability of e-c is
claimed, and no conditional infinite integral is hidden in B's definition.

Formalization remains a future task, not an unfinished Lean branch. The certificate
count stays 15. This paper is not presented as Lean-verified.

## Log

- 2026-10-18 — Created before the hard proof. Additive source-mean corpus search
  completed; no new Lean written and no result counted.
- 2026-10-18 — Completed and audited paper proof; moved to fully proven paper stage
  during user-requested closeout after the goal was cleared.
