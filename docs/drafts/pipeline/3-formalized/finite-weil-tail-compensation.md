# Quantitative finite-head / infinite-tail compensation

Status: FORMALIZED — dependency-closed paper proof and Lean verification complete.

Mission: turn the finite Gram certificate into a native quantitative
constraint on full-cone Weil-positive sequences. Only local Lean corpus
and installed dependencies; no web, papers, or numerics.

## Corpus evidence

- `WeilLogShiftFiniteGramCertificate`: fixed finite normalized Gram tests
  bound finite coefficient norm by their maximum negative tolerance.
- `WeilFullConeNearNullPositiveDefinite`: Weil positivity gives a logarithmic
  deviation bound, actual potential summability, nonpositive potential Gram
  forms, exponential autocorrelation decay, and summability of
  `(2 log n + A)/n²`.
- The first local search for `Gram tail coefficient` returned 81 indexed
  hits, mainly unrelated Suzuki coefficient-tail Gram results. No matching
  native finite-Weil-head compensation result was identified.

## Paper proof

For a finite set s of tail indices, let c_i be the actual normalized
deviation at i+2. Remove the corresponding finite packet to define the
tail b; b is zero on the selected head and equals the original deviation
elsewhere. Both forced head coordinates 0 and 1 stay zero.

The existing logarithmic deviation bound proves convergence of
D = sum_n |b_n|/n². Existing exponential kernel decay and the triangle
inequality give one universal B>0 with
pairedLogKernel(y,n) ≤ B exp(2|y|)/n² for n≥1. The n=0 tail term vanishes.
Thus the literal tail potential converges and is bounded in absolute
value by B exp(2|y|) D. Subtracting the finite head from the actual convergent
series gives its HasSum value exactly as total potential minus head.

For a normalized Gram test w=(N,x,u,a), a≥0, define its explicit cost
C_w = a sum_{i,j}|u_i u_j| B exp(2|x_j-x_i|).
Its tail Gram value has magnitude at most C_w D. The full potential Gram
form is nonpositive under Weil positivity, so the negative-head Gram test
is at least -C_w D. The finite certificate selects finitely many w,
independent of the Weil-positive sequence. Take C_s=1+sum_w C_w>0.
Every selected head test is at least -C_s D; the certificate implies
norm(c)≤C_s D, with the literal weighted tail HasSum recorded.

## Meaning and limits

Every nonzero finite head of a Weil-positive deviation requires weighted
mass outside that head. No added summability or analytic regularity premise
is assumed: these are discharged from the existing Weil-positive contract.
C_s depends on the chosen support. No support-uniform estimate, infinite
injectivity, or RH conclusion follows merely because individual tails
converge. The positive survivor is a quantitative tail-compensation law.

## Verification — 2026-10-09

Leaf: `formal/GaloisForLFunctions/RHTower/WeilLogShiftFiniteTailCompensation.lean`.

- Final direct `lake --old env lean` leaf check with output olean exited 0,
  without warnings. New and direct-dependency oleans are current.
- All twelve public declarations passed `#print axioms`: only `propext`,
  `Classical.choice`, and `Quot.sound` occur. Mathlib API checks passed.
- Exactly one import in the RHTower umbrella. No full or umbrella build.
- Index refresh exited 0; module-filtered local lexical search recovered
  all twelve public declarations, with no missing names.
- Formal lint exited 1 solely on the unrelated missing umbrella import
  for `HTGeometry.QKrawtchoukCompanionTriangular`. No error names this leaf;
  the unrelated module was not changed.

Main results: `exists_weilFiniteHead_tail_weight_bound` records weighted
tail HasSum and the sequence-independent head bound.
`exists_weilFiniteTail_potential_envelope` records literal signed tail
HasSum and one remainder envelope constant uniform over supports and
Weil-positive sequences. `finiteWeilGramTailCost` exposes the individual
translation/amplitude costs used to construct the head constant.

## Follow-up formalized

`WeilLogShiftFiniteGramCostGrowth.lean` proves a stronger two-sign lower
bound: every normalized certificate containing arithmetic index n has
total explicit Gram cost greater than 2n². Distinct witnesses are needed
for the positive and negative unit coefficient. Weighted coefficient
sensitivity and finite certificate existence are preserved, and costs on
growing initial supports eventually exceed every fixed budget. See
[finite Weil Gram cost growth](finite-weil-gram-cost-growth.md).
This concerns normalized Gram cost, not every possible existential
head-tail constant under Weil positivity. No optimality is claimed.

The full corpus-research goal remains active.
