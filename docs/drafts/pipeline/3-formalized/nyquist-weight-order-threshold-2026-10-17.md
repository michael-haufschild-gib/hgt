# Nyquist weight order and the threshold for an integrable residual

- **ID:** nyquist-weight-order-threshold-2026-10-17
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Scope:** Infinite-Grid Tail Rigidity Beyond Trap 5; explicit weight producers.
- **Source:** The integrable polar residual package and the field guide
  `formal/GaloisForLFunctions/BiScaleUncertainty/README.md` (read-only).
- **Statement:** For beta>0 and Taylor degree m>=0, the logarithmic-cell
  Taylor producer for cosh(beta x) has an integrable residual exactly when
  beta<m+1.
- **Status:** Complete paper theorem formalized and audited; package 15/100.
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
- [x] Actual positive kernel, bounded operator and threshold formalized in Lean.
- [x] All direct leaves, axioms, API entries, imports and formal lint checked.
- [x] Count the complete producer-order classification once, as package 15.

## Execution plan

1. Refresh the corpus boundary and identify exact Taylor, power-tail and source-scaling inputs.
2. Prove positivity, explicit cell bounds, the sharp mass asymptotic and all threshold cases on paper.
3. Prove the bounded operator below the threshold and exact compact-input decomposition at every beta>=0;
   construct actual smooth low-energy source witnesses at and above it.
4. Formalize the complete connected theorem in direct Lean leaves, one process at a time.
5. Audit all declarations, axioms, API entries, imports and lint; update the ledger only then.

All seventeen direct leaves pass and are wired: `NyquistWeightJets`,
`NyquistWeightTaylorRemainder`, `NyquistWeightCells`,
`NyquistWeightCellAsymptotic`, `NyquistPowerTails`,
`NyquistPositiveTailComparison`, `NyquistWeightKernel`,
`NyquistWeightTailMass`, `NyquistWeightOperator`,
`NyquistWideSourceEnergy`, `NyquistPositivePrefixComparison`,
`NyquistPrefixScales`, `NyquistWeightPrefixMass`, `NyquistWeightProducer`,
`NyquistWideResidualLimit`, `NyquistWideResidualEscape`, and
`NyquistWeightCalibrations`. All final logs are clean except two informational
`ring` suggestions in `NyquistWeightCellAsymptotic` (no errors or warnings).

The direct checks cover the entire paper theorem: explicit jets and positive
remainders; all-cell bounds; exact integrability threshold and minimum degree;
sharp cell, tail and critical/supercritical prefix constants; exact bounded
operator norm; signed compact-input producer decomposition at every beta>=0;
absolute subcritical cell summation and uniform-convergence equivalence; one
actual smooth source family certifying both norm sharpness and divergence
under every positive energy ceiling; and all three calibrations. The
beta=1/2, degree-zero calibration identifies the original `nyquistPolarConstant`
producer, kernel and mass, and sharpens its tail asymptotic to 1/(4 sqrt N).

The formal indexing uses zero-based cells k with n=k+1, so tail N begins at
log(N+1), and a prefix of M cells has normalizations log(M+1) and (M+1)^r.
These are the paper's limits under the corresponding fixed shifts of indices.

The complete audit on 2026-10-18 covers 186 public declarations: 159 theorems
and 27 definitions. Every declaration has a scratch `#print axioms` certificate
using only `propext`, `Classical.choice`, and `Quot.sound` (or no axioms).
All 186 exact name/module API pairs and all 17 umbrella imports are verified.
Source hashes match the final direct checks; the read-only guide hash is
unchanged. `scripts/formal_tools.py index` exits 0.

Global `scripts/formal_tools.py lint` exits 1 solely on five unrelated missing
umbrella imports: `ConfinedCoherentPlasticGap`,
`SignedLcmFractionalDefectAndCompleteFibreCollapse`,
`SignedPrimePolarClampedPrimeSum`, `SignedPrimePolarFactorialAtomicPacket`,
and `SignedPrimePolarRealFactorialStencil`. No error concerns this package;
the snapshot reports no active proof hole. No repository-wide green claim.

Final leaf checks use `lake --old env lean -j 1 -o <olean> <leaf>`.
The axiom audit uses `lake --old env lean -j 1 /tmp/nyquist_weight_axioms.lean`.
Complete manifests are `/tmp/nyquist_weight_{declarations,source_hashes,axiom_coverage,verification}.json`;
audit logs are `/tmp/nyquist-weight-{axioms,index,lint}.log`.
Audit scripts are `/tmp/nyquist_weight_certificate.py` and `/tmp/nyquist_weight_verify.py`.

Trap 10 alignment: these are explicit unconditional Nyquist-cell producers.
No receiver-only Chebyshev premise or pre-floor subtraction enters this
package. The factorial-stencil route remains a separate research topic.
The field guide remains read-only and its hash matches the fully read version.

The original 100-package objective remains active with 15 certified packages.
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
energy ceilings. This complete result is formalized and counted once; its
negative threshold and helper lemmas are not separate contributions.

## No-go closure

If the proposed threshold or asymptotic fails, extract the exact corrected
classification or replacement producer. Do not retire the route with a negation
alone. Here the exact positive producer hierarchy and actual-source sharpness
are both proved on paper and certified in Lean.
