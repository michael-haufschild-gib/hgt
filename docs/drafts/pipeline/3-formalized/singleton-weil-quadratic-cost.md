# Matching quadratic cost for singleton Weil supports

Status: dependency-closed paper proof; Lean formalization pending.

Only local Lean corpus and installed dependencies. No web, external papers,
or numerics. Target: matching quadratic growth, not an optimal constant.

## Evidence and target

`WeilLogShiftFiniteGramCostGrowth` proves total normalized certificate cost
greater than 2n² whenever arithmetic index n is present, and finite
certificate existence. `WeilLogShiftFiniteTailCompensation` supplies the
inverse-square kernel envelope. The actual autocorrelation is positive
at zero and nonnegative everywhere. The paired kernel is even.

Prove that every singleton arithmetic support admits exactly two Gram
tests, with total cost between 2n² and Cn² for one universal C>0 and the
same envelope constant B used by the lower bound.

## Dependency-closed paper proof

Let n=k+2 and P_n(y)=pairedLogKernel(y,n). The inverse-square envelope
gives P_n(0)→0; P_n(log n)=K(2log n)+K(0)≥K(0)>0.
For all sufficiently large k, P_n(0)≤K(0)/2.

Use points (0,log n), weights (1,1) and (1,-1), and scale 2/K(0).
The unscaled potential Gram sums on the positive unit coefficient are
2P_n(0)+2P_n(log n)≥2K(0) and
2P_n(0)-2P_n(log n)≤-K(0). Their negative-potential test values are
therefore at most -4 and at least 2. Scalar homogeneity gives the required
strict margin for every nonzero signed singleton coefficient. The two
tests are distinct and form a normalized certificate.

Each explicit test costs (2/K(0)) B (2+2n²). The pair thus costs at most
(16B/K(0)) n² for n≥1. B can be the lower-bound theorem's B; a separate
kernel envelope is allowed to determine the cutoff.

For every exceptional finite k, an existing normalized certificate yields
one witness for the positive unit vector and one for its negative. They
are distinct, and scalar homogeneity shows this pair is itself a complete
singleton certificate. Choose these pairs for the finite exceptional
range. Add their finite costs to the eventual upper constant; n²≥1
absorbs all exceptions. This gives one C for every k, with exactly two
tests, while the existing lower bound gives total cost>2n².

## Scope

The growth rate is quadratic for singleton coefficient supports under
the explicit normalized Gram cost. Only the eventual construction uses
two points per Gram test; exceptional tests may have larger Gram order.
No optimal multiplicative constant or uniform bound for higher-dimensional
supports is asserted. Finite existence and the matching upper bound are
the positive survivor of the previous budget obstruction.

## Gates

Direct leaf compilation; public axiom audit; umbrella wiring; index;
formal lint; indexed local search; owned scratch/process cleanup.


## Final verification — 2026-10-09

Status: FORMALIZED. This checkpoint supersedes the initial pending Lean status.

Local-corpus result: singleton normalized Gram certificates have exactly quadratic
cost growth in their arithmetic index n = k + 2. The same B > 0 supports a
universal lower bound, sum cost > 2 n², for EVERY certificate, and a uniform upper
bound, sum cost ≤ C n², achieved by a certificate containing exactly two tests.
The multiplicative constants are not claimed optimal. The explicit large-index
construction uses two points per test; the finite exceptional indices use the
existing corpus certificate theorem, so no two-point claim is made for them.

Formal leaf: formal/GaloisForLFunctions/RHTower/WeilLogShiftSingletonGramCost.lean.
Public declarations:
- RHTower.exists_two_test_singletonWeil_certificate
- RHTower.exists_singletonWeil_quadratic_cost_certificate

Native leaf compilation: exit 0, no diagnostics. Both declarations pass the
scratch axiom audit with exactly propext, Classical.choice, Quot.sound. Local
mathlib API term checks pass. Leaf and direct dependency artifacts are current.
RHTower umbrella import installed; formal index refreshed successfully.

Authoritative formal lint: exit 1, only unrelated umbrella reachability errors:
- RHTower.GammaHardyPhaseRateLevyKhintchine
- RHTower.RepPointPairOperator
- RHTower.RepPointPairRegularity
- RHTower.RepPointPairSymmetry
- HTGeometry.MonotoneQuantileTransport
- HTGeometry.PaperSymmetricDiscriminantEmbedding
- HTGeometry.QKrawtchoukCompanionTriangular

No new analytic premises, axioms, or convergence assumptions. No web searches,
external papers, or numerical experiments used. Research evidence remains local
Lean corpus only, following the user's reiterated restriction.

## Next unresolved question

Does an adjacent pair of arithmetic indices force cubic certificate cost?
The candidate direction (1, -1) cancels the leading paired-kernel response.
A locally proved exponential derivative envelope, if present or derivable in
Lean, could bound the adjacent-index kernel difference by a constant times
exp(2 |y|) / n³. This would turn the existing signed-witness cost argument into a
cubic lower bound. This is a conjectural next target, not a proved theorem or an
available lemma. Search and inspect local Lean before adopting any premise.

The full research goal remains active; this checkpoint completes one increment.


## Adjacent-pair follow-up completed — 2026-10-09

The cubic lower-bound question above is now proved in
WeilLogShiftAdjacentGramCost.lean. Its common-normalization theorem pairs the
singleton quadratic upper bound with a cubic lower bound for every adjacent-pair
certificate. See adjacent-weil-cubic-cost.md in this directory. A matching cubic
upper bound for adjacent pairs remains open in this workstream.
