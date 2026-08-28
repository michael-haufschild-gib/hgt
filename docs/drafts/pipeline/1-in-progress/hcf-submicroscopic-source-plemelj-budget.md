# HCF submicroscopic source Plemelj budget

- **ID:** HCF-PLEMELJ-001
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `rh-current-frontier-map.md` · Route HCF corrected source budget
- **Statement:** `[BRIDGE]` For every real center `t`, the HCF critical-line energy trace is the
  iterated source limit obtained by first taking `eta -> 0+` against the canonical compact cutoff
  `realCompactIntervalCutoff n`, then taking `n -> infinity`.  The prelimit uses only
  `boundaryDensity XiC eta`; consequently the corrected HCF lattice budget has a definition
  containing no `XiZeroCopy` before source expansion.

## Goal

Replace the divisor-first Abel/exterior/Stokes trace by a height-local pole--Gamma--von-Mangoldt
boundary observable.  In centered spectral coordinates set

`w_t(x) = normSq (criticalFeatureCauchyKernelTest t x)`

and, for `n : Nat` and `eta > 0`,

`P_(n,eta)(t) = integral_R w_t(x) * realCompactIntervalCutoff n x
  * boundaryDensity XiC eta x dx`.

For fixed `n`, set `P_n(t) = lim_(eta -> 0+) P_(n,eta)(t)`; this limit is source-defined using
`Filter.limUnder`.  Target bridge is `P_n(t) -> criticalLineCriticalFeatureEnergyTrace t` as
`n -> infinity`.  The lower-boundary Schwarz reflection rewrites the same compact prelimit as the
imaginary part of `continuedPrimeArchSourceRelativeTrace (x - eta*I)` wherever the continued
source is admissible.  Associated lattice source budget is the explicit pole--Gamma--von-Mangoldt
raw jet minus `sum_{k in K} P_n(k)`.
This closes source scalarization only.  The separate quantitative target is

`B_corrected(K_T) <= 21/100 * N(T) + o(N(T))`,

with `4/25` stronger.  No implication from source scalarization to that estimate is assumed.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `tendsto_criticalFeatureSourcePlemeljTrace`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

1. Multiply the HCF weight by `realCompactIntervalCutoff n`; prove continuity and compact support.
2. Apply `tendsto_xiBoundaryDensity_setIntegral`.  Its local factorization proves that real Xi
   zeros contribute analytic multiplicity, nonreal conjugate pairs cancel, and the zero-free
   remainder vanishes.  No global divisor interchange is needed.
3. Define the fixed-cutoff source value with `Filter.limUnder`; uniqueness identifies it with the
   finite multiplicity-weighted real-zero sum.
4. Let `n -> infinity`.  Cutoffs converge pointwise to one, remain in `[0,1]`, and HCF line energy
   is summable, so dominated convergence gives the full critical-line trace.
5. Use Schwarz reflection and the existing Xi/source logarithmic-derivative identity to rewrite
   admissible compact prelimits as positive-real-shift pole--Gamma--von-Mangoldt evaluations.
6. Sum over finite `K` only after the source theorem.
7. Audit the remaining quantitative defect.  A pointwise absolute estimate is forbidden: it
   destroys the pole--Gamma/boundary main-term cancellation.  Seek a signed height-local
   covariance or prove a method ceiling.

## Door passport

- Source definition contains only `criticalFeatureCauchyKernelTest`, the canonical compact cutoff,
  Lebesgue integration, `XiC`, and `logDeriv XiC`.  On admissible lower boundaries this is the
  continued pole--Gamma--von-Mangoldt trace at positive ordinary shifts `1/2 + eta + i*x`.
- `XiZeroCopy` appears only in proof of equality, after scalar source observable is fixed.
- Existing Abel and exterior Cesàro projectors fail this passport because their prelimit weights
  are functions on `XiZeroCopy`.
- External audit: Poisson/Plemelj boundary recovery and near-critical logarithmic-derivative
  moments are established subjects; no external novelty is claimed for boundary recovery.
  Corpus-specific HCF source instantiation was not found.  Near-critical mean-value results found
  in the literature use RH or additional small-gap hypotheses and cannot discharge the
  unconditional `21/100` gate.

## Hostile audit

- No global horizontal line is assumed divisor-free.  `logDeriv` is totalized, and the local
  boundary-divisor theorem handles the finitely many zeros in each compact factorization.
- Arbitrarily shallow off-line zeros are not ignored.  At each compact cutoff they occur in
  conjugate pairs and their boundary jump cancels before cutoff exhaustion.
- Source replacement alone gives no numerical gain.  Any claimed `21/100` estimate must bound
  the signed pole--Gamma/boundary defect, not the absolute values of its two leading terms.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** pending
- **Strongest positive survivor:** pending
- **New insight:** pending
- **Status:** local Plemelj core already exists in corpus; HCF cutoff instantiation and exhaustion
  are the exact new bridge.  Paper proof dependency audit in progress; external novelty label
  `[BRIDGE]`.

## Log

- 2026-08-28 — created directly in `1-in-progress`; exact conjecture frozen after corpus and primary-literature audit.
- 2026-08-28 — replaced unjustified full-line one-parameter interchange by dependency-closed
  compact-boundary limit followed by summable cutoff exhaustion.
