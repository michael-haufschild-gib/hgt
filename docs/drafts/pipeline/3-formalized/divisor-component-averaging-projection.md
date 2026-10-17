# Explicit component averaging in physical energy

- **ID:** divisor-component-averaging-projection
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Unit-cell averaging followed by finite-component centering constructs the unique nearest completed divisor state for every physical L² input, with exact convergent error.

## Mathematical result

For arbitrary d,D and q∈L²(ℝ), let b_k=∫_(k,k+1]q and F(t)=∫₀ᵗq.
Subtract the mean of b on each finite active-edge component, retain b on
infinite active tails, and synthesize unit-cell currents. This explicit
producer P_Aq has range exactly the physical energy completion, is bounded
linear, idempotent and contractive. Its squared approximation error is

    ‖q−P_Aq‖²=‖q−Qq‖²+Σ_(finite I=[a,b))(F(b)−F(a))²/(b−a).

The charge series converges by grouping actual ℓ² residual squares. Every
completed competitor has excess error exactly equal to its squared distance
from the produced data, proving unique best approximation. There is no
finite-family, spectral-gap, trace-summability or analytic admission premise.

The first cell and primitive trace at1 vanish. Actual negative truncation
q⁻ has zero cell analysis, and its energy is retained explicitly in
‖q−Qq‖²=∫_(-∞,0]q²+‖q−q⁻−Qq‖². For the full divisor family,
P_Aq=Qq−b_0 unitCell0 and error=‖q−Qq‖²+b_0².

Trap10 alignment: coefficients and error are instantiated on actual physical
velocities. No assumed Chebyshev bound or pre-floor counterterm. Research
stays on continuum coprime shear. No RH, full SourceGraph, full affine-unitary
or unweighted logarithmic H1 claim. The relocated README was read fully and
never edited. Classical Hilbert projection is a parent, not a novelty claim.

## Proof and verification

Dependency-closed paper preceded Lean:
`docs/reports/BiScaleUncertainty/DivisorComponentAveragingProjection.md`.
Five leaves in formal/GaloisForLFunctions/BiScaleUncertainty/:
DivisorCellEndpoints137lines/17public, DivisorComponentAverages129/16,
DivisorComponentCharge83/7, PhysicalCellAveraging136/19,
DivisorPhysicalProjection226/28. Total711lines/87public=72theorems+15defs.
Count this package once: contribution16/100.

All five serial direct `lake --old env lean -o <normal-output> <leaf>` checks
pass with empty logs and current outputs. Final scratch Lean audit passes:
all87 public names, only propext/Classical.choice/Quot.sound,17 principal
signatures and50 mathlib API probes. Five unique imports and87 exact catalog
entries verified. No full/umbrella build, numerical experiment or heartbeat
increase. The update_plan tool is unavailable; this card records completion.

Global lint --check-generated exits1 for eight unrelated unreachable modules:
DyadicRenewalChain, ExponentialTentMoments, NyquistPolarSourceEscape,
PhysicalCollarMixture, PhysicalPriceResponse, RegularizedGramGeometry,
RegularizedPhysicalGram, SignedPrimePolarSourceParameters; also concurrent
LEAN_API/LEAN_OVERVIEW drift. No own or proof-debt error. Index refreshed
separately; do not claim global lint passed or edit concurrent research.

Evidence: /tmp/divisor_averaging_axioms.lean,
/tmp/divisor-averaging-{axioms,index-post-lint,lint-final}.log,
/tmp/divisor-averaging-{audit-names,lint-errors}.json,
/tmp/divisor-averaging-api-entries.txt. Separate direct-leaf logs retained.
The successful final audit incorporates the API probes; obsolete standalone
probe artifacts are removed after certification.

## Corpus and primary sources

Query: `orthogonal cell component mean subtraction projection physical
velocity residual`, BiScaleUncertainty filter, --any,60-second budget.
All20 candidate statements and20 source arguments inspected. Existing cell
synthesis, completed spaces and component-constant residuals are parents.
No matching explicit arbitrary-component formula returned; not an absence
or novelty proof. partial=true, text/source interrupted, snapshot1446427 vs
current1446428, refresh incomplete, compiler mostly pending/source-only.
Evidence: /tmp/divisor-averaging-search.json. Primary MIT18.102 projection
notes and official mathlib projection documentation checked; links in paper.

Next unproved candidate:
`../0-backlog/integer-dilation-cell-coisometry.md`. No Lean assigned.
