# Nyquist weight order and the threshold for an integrable residual

- **ID:** nyquist-weight-order-threshold-2026-10-17
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scope:** Infinite-Grid Tail Rigidity Beyond Trap 5; explicit weight producers.
- **Source:** The integrable polar residual package and the field guide
  `formal/GaloisForLFunctions/BiScaleUncertainty/README.md` (read-only).
- **Statement:** For beta>0 and Taylor degree m>=0, the logarithmic-cell
  Taylor producer for cosh(beta x) has an integrable residual exactly when
  beta<m+1.
- **Status:** Dependency-closed paper proof complete; Lean in progress, uncounted.
- **Paper:** `docs/reports/BiScaleUncertainty/NyquistWeightOrderThreshold.md`.

## Goal

Determine the exact exponential weights for which cell-average polar production
admits a bounded correction on arbitrary bounded continuous signed inputs.
Identify the least explicit weight-producer order that restores a summable error.
This changes the weight approximation, without assuming a bound on derivatives
or spectral second moments of the source.

## Explicit construction

On I_n=[log n,log(n+1)], let w_beta(x)=cosh(beta x), and set

    p_(beta,m,n)(x)=sum_(j=0..m) w_beta^(j)(log n) (x-log n)^j/j!.

The residual kernel is w_beta-p_(beta,m,n) on each half-open cell.
The proved cell-mass asymptotic for beta>0 is

    alpha_(beta,m,n) / n^(beta-m-2) -> beta^(m+1)/(2(m+2)!).

Consequently, below the threshold, the actual all-tail residual operator has
exact norm A_N with

    A_N ~ beta^(m+1)/(2(m+2)!(m+1-beta)) * N^(beta-m-1).

At and above the threshold, the positive kernel has infinite mass and
unbounded action on compactly supported continuous inputs of supremum norm one.
The beta=0 case has zero residual. One actual nonnegative smooth source family,
chosen independently of beta,m,N, has normalized correlations H_j(x)=H(x/(j+1))
and energies bounded by K/(j+1). Its residuals tend to A_N below the threshold
and to infinity at or above it. Thus the norm is sharp even under any positive
energy ceiling on actual smooth compact sources.

## Approach and prior-corpus gate

Taylor's integral remainder and the two cell-width bounds expose a positive
power-series comparison. Check all exponent endpoints, positivity, infinite-tail
summation and the precise leading coefficient before promoting this candidate.
Then reuse the actual partition and operator construction from the preceding
package, with all new analytic bounds derived from the explicit weight.

Focused current-corpus search `/tmp/nyquist-exponent-frontier-deep.json`
completed without errors or unfinished stages. All 20 candidate statements and
20 source arguments were inspected. Inventory coverage was complete and current;
semantic coverage was unmeasured, refresh deferred to the background indexer,
and every candidate was source-only. The suggested ingredient set concerns
decaying Levy weights, not growing-weight Taylor residuals. Existing results
found here include the preceding beta=1/2, m=0 construction and its inputs;
they do not establish the proposed threshold classification. A focused lexical
cross-check is `/tmp/nyquist-exponent-taylor-lexical.txt`.
The previous point-sample search
`/tmp/nyquist-point-producer-deep.json` found derivative-free cell and dyadic
quadrature bounds retaining the polar-density cost. A derivative bound on the
source is not a resolution of that remaining uniform-control problem.

## Gates

- [x] Current corpus inspected; exact novelty boundary established.
- [x] Dependency-closed paper proof and sharp positive-survivor audit.
- [ ] Actual positive kernel, bounded operator and threshold formalized in Lean.
- [ ] All direct leaves, axioms, API entries, imports and formal lint checked.
- [ ] Count once only if the complete classification adds a substantive tool.

## Execution plan

1. Refresh the corpus boundary and identify exact Taylor, power-tail and source-scaling inputs.
2. Prove positivity, explicit cell bounds, the sharp mass asymptotic and all threshold cases on paper.
3. Prove the bounded operator and exact compact-input decomposition below the threshold;
   construct actual smooth low-energy source witnesses at and above it.
4. Formalize the complete connected theorem in direct Lean leaves, one process at a time.
5. Audit all declarations, axioms, API entries, imports and lint; update the ledger only then.

Ten direct leaves pass and are wired: `NyquistWeightJets`,
`NyquistWeightTaylorRemainder`, `NyquistWeightCells`,
`NyquistWeightCellAsymptotic`, `NyquistPowerTails`,
`NyquistPositiveTailComparison`, `NyquistWeightKernel`,
`NyquistWeightTailMass`, `NyquistWeightOperator`, and
`NyquistWideSourceEnergy`. All final logs are clean except two informational
`ring` suggestions in `NyquistWeightCellAsymptotic` (no errors or warnings).

These certificates cover the explicit Taylor jets and positive remainder,
all-cell power bound, sharp cell asymptotic, exact integrability threshold,
explicit and sharp subcritical tail mass, locally integrable actual kernel,
positive bounded integral operator with exact norm, and literal infinite
positive mass at/above threshold. The common actual smooth source family has
pointwise correlation limit one, a quantitative growing plateau, and energy
bound K/(j+1). Its sharpness endpoints remain to be composed.

Remaining proof organization:
- Critical/supercritical prefixes: transfer ratios through positive divergent
  prefixes, using telescoping logarithmic/power increments. The relevant
  derivative and slope APIs pass their names probe. The prefix-transfer leaf
  is being checked; it is not yet counted as verified.
- Exact signed cell moments and compact-input producer decomposition, absolute
  cell summation, and the uniform-convergence equivalence.
- Actual-source norm sharpness and supercritical divergence under every
  positive energy ceiling, using the checked common source family.
- Minimum integer degree, the three calibrations, and the complete package's
  direct-leaf, axiom, API, import, index, and lint audits.

Trap 10 alignment: these are explicit unconditional Nyquist-cell producers.
The beta=1/2, degree-zero calibration must identify the existing
`nyquistPolarConstant` producer. No receiver-only Chebyshev premise or
pre-floor subtraction enters this tail-rigidity package. The factorial-stencil
route is a separate topic and does not replace the assigned research topic.

The original 100-package objective remains active with 14 certified packages.
This card carries task tracking because `update_plan` is unavailable.

## Paper and input audit

The complete proof checks every exponent endpoint, the positive Taylor remainder,
an explicit all-cell majorant, sharp cell/tail/prefix constants, exact kernel
integrability and operator norm, compact-input decomposition, minimal integer
order, and actual smooth source sharpness with a common quantitative energy
ceiling. The source family has pointwise limit one and lacks uniform signed
grid tails; no stronger topology counterexample is claimed.

Fresh `/tmp/nyquist-weight-taylor-inputs.json` completed without errors or
unfinished stages. All 20 candidates and 20 source arguments were inspected;
inventory was complete, coverage was one generation behind, semantic coverage
unmeasured and compiler evidence source-only. Actual mathlib Taylor remainder
and power-series tests were read directly. `BroadSpectralCostRealization` was
read through its scaling argument: its first-moment and increment estimates
give the stronger explicit energy bound K/(j+1), replacing a merely qualitative
convergence argument. The fixed nonnegative bump construction in
`DistantCopyPolarTopology` was checked directly. Existing calculus, power-series
tests and broad-source scaling are reused inputs, not counted as new results.

The strongest positive survivor is the full producer-order hierarchy and its
sharp norm on actual smooth correlations under arbitrarily small positive
energy ceilings. Formalize this complete result; do not count just its negative
integrability threshold or an easier isolated helper.

## No-go closure

If the proposed threshold or asymptotic fails, extract the exact corrected
classification or replacement producer. Do not retire the route with a negation
alone. The complete paper result is proved; its Lean certificate remains open.
