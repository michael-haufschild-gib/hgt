# Logarithmic separation and finite-support Gram cost

Status: FORMALIZED. Paper proof and exact Lean receivers verified.
Only local Lean corpus is evidence. No web, external papers, or numerics.

## Target

Quantify cancellation for every pair of arithmetic indices inside an arbitrary
finite support, then upgrade full arithmetic cutoff cost from quadratic to cubic.
No analytic hypothesis is added. Matching upper bounds remain a separate problem.

## Inspected local ingredients

RiemannAutocorrWeightedTranslation supplies E>0 with
|K(y+h)-K(y)| ≤ E |h| exp(-2|y|) for |h|≤1.
WeilLogShiftFiniteTailCompensation supplies B0>0 with
P_n(y) ≤ B0 exp(2|y|)/n².
WeilLogShiftFiniteGramCostGrowth supplies the normalized certificate definition,
actual finite Gram forms, nonnegative costs, and certificate existence on every
finite support. WeilLogShiftAdjacentGramCost verifies the signed-witness method
for one adjacent pair. No support-inclusion or general separation receiver was
found in the indexed search or exhaustive WeilLogShift source search.

## Paper proof

For 1≤n≤m let delta=log(m)-log(n)≥0. If delta≤1, apply the translation estimate to
K(y+log n) and K(y-log n), with displacements delta and -delta. Since
log n-|y|≤|y±log n|, the paired difference is bounded by
2E delta exp(2|y|)/n². If delta>1, the individual positive envelopes and m≥n
bound the difference by 2B0 exp(2|y|)/n², hence by that quantity times delta.
Thus one positive B works for all n,m,y:
|P_m(y)-P_n(y)| ≤ B delta exp(2|y|)/n².

Inside any finite support s, choose distinct i<j and coefficient vector
c=e_i-e_j. Its sup norm is one and its actual finite potential equals
P_(i+2)-P_(j+2). The finite Gram sum therefore has absolute value at most
cost_B(w) delta/(i+2)². A normalized certificate supplies distinct witnesses
for c and -c; each satisfies (i+2)² < delta cost_B(w). Sum nonnegative costs to get
2(i+2)² < delta sum cost_B.

The elementary logarithm inequality gives delta≤(j-i)/(i+2). Multiplying the
preceding strict bound by i+2 and using nonnegative total cost gives
2(i+2)³ < (j-i) sum cost_B.

For s=range(N+2), choose i=N and j=N+1. Their gap is one, so every normalized
certificate has sum cost_B > 2(N+2)³. Finite certificate existence was already
proved for every support; this is a quantitative obstruction, not a nonexistence
claim.

## Work plan

1. Formalize the global paired-kernel logarithmic-separation envelope.
2. Formalize zero-extended signed directions on arbitrary finite supports.
3. Prove logarithmic and arithmetic gap bounds plus full-cutoff cubic corollary.
4. Native leaf checks; all public axiom checks; umbrella wiring; index; lint.

The full research goal remains active.


## Verified completion — 2026-10-09

All four work-plan steps completed. New formal leaves:
- formal/GaloisForLFunctions/RHTower/WeilLogShiftSeparationEnvelope.lean
- formal/GaloisForLFunctions/RHTower/WeilLogShiftFiniteClusterCost.lean

Public declarations:
1. RHTower.exists_pairedLogKernel_logSeparation_envelope
2. RHTower.exists_finiteWeilGram_separation_cost_bounds
3. RHTower.exists_finiteWeilGram_cutoff_cubic_cost_bound

The global envelope covers every 1≤n≤m, including logarithmic gaps larger than
one. The finite-support theorem covers every ordered pair i<j in every support,
with the direction zero on all remaining coordinates. In one universal positive
normalization B it proves
2(i+2)² < (log(j+2)-log(i+2)) totalCost_B,
and
2(i+2)³ < (j-i) totalCost_B.
Consequently every normalized certificate on range(N+2) has totalCost_B >2(N+2)³.
All casts and actual arithmetic kernel identities are carried by the Lean proof.
Certificate existence on every finite support remains supplied by the imported
corpus; this theorem is a lower-cost obstruction, not nonexistence.

Verification:
- Both native leaf builds: exit 0, no diagnostics after removing two unused ring
  tactics. No heartbeat or recursion changes.
- All three public declarations: exactly propext, Classical.choice, Quot.sound.
- Explicit mathlib API term checks: exit 0, no diagnostics.
- Both leaves and direct dependencies: current olean artifacts.
- RHTower umbrella contains both imports. Index refresh: exit 0.
- Formal lint: exit 1 only for four unrelated unreachable modules:
  RHTower.Sieve.UnitBlockPoissonKernel;
  HTGeometry.MonotonePhaseFirstDerivativeTest;
  HTGeometry.QKrawtchoukCompanionTriangular;
  HTGeometry.SmoothPlateau.
- No owned jobs remain running. No web, papers, numerics, full builds, or commits.

Evidence: /tmp/hgt-gram-separation-envelope-build.log,
/tmp/hgt-gram-cluster-cost-build.log, /tmp/hgt-gram-cluster-audit.log,
/tmp/hgt-gram-cluster-index.log, /tmp/hgt-gram-cluster-lint.log.

## Next question

Investigate higher-order cancellation in three or more nearby indices. The
inspected corpus bounds every fixed actual Riemann-kernel derivative, suggesting
that a normalized second difference on three adjacent arithmetic indices could
force quartic cost. This is not proved: second differences through the logarithm
must be derived, not added as a hypothesis. Search local Lean before starting.
The matching cubic upper bound for adjacent pairs also remains unresolved.

Full research goal remains active; this completes one increment.


## Higher-order follow-up completed — 2026-10-09

The three-index quartic conjecture above is proved in
WeilLogShiftQuarticClusterCost.lean. Its balanced endpoint weights cancel the
unequal logarithmic first moment exactly. The lower bound applies inside every
finite support containing the triple and to full arithmetic cutoffs. See
finite-weil-quartic-cluster-cost.md in this directory. Higher orders and matching
upper bounds remain unproved in this workstream.
