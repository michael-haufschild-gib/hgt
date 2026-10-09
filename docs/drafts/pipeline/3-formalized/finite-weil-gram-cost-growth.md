# Quadratic cost growth of finite Weil Gram certificates

Status: FORMALIZED — dependency-closed paper proof and Lean verification complete.

Only local Lean corpus and installed dependencies. No web, external papers,
or numerics. Existing finite certificates remain the positive survivor.

## Corpus audit

Local search `finiteWeilGram cost` returned the cost definition and its
private nonnegativity lemma in `WeilLogShiftFiniteTailCompensation`.
That leaf supplies a universal B>0 with the inverse-square kernel envelope.
`WeilLogShiftFiniteGramCertificate` supplies normalized norm certificates
for every finite support. No cost-growth law was found in those sources.

## Dependency-closed paper proof

Define W_s(c)=sum_{i in s}|c_i|/(i+2)². The kernel envelope, triangle
inequality, and finite sums give

  |Gram_w(c)| ≤ Cost_B(w) W_s(c).

Normalization means that for every c≠0 some selected test has value
strictly below -norm(c). The cost law is not a claim about unnormalized
qualitative sign detection.

For a coordinate vector e_i, norm(e_i)=1 and W_s(e_i)=1/(i+2)².
A normalized certificate contains w_plus with Gram_w_plus(e_i)<-1.
It also contains w_minus with Gram_w_minus(-e_i)<-1, so by linearity
Gram_w_minus(e_i)>1. These witnesses are distinct. The coefficient bound
forces each cost to exceed (i+2)². Nonnegativity of all costs then gives

  2(i+2)² < sum_{w in tests} Cost_B(w).

This applies to every normalized certificate, not just a chosen family.
Together with existing finite existence it yields finite feasibility and
unavoidable cost growth. On initial supports containing arbitrarily large
indices, every certificate eventually exceeds any prescribed budget.

## Scope and positive survivor

The obstruction concerns the explicit nonnegative Gram cost that includes
test amplitudes and exponential translation weights. It does not assert
a lower bound for every possible existential head-tail constant under
Weil positivity. No matching upper bound or optimality is claimed.

The positive survivor is the weighted coefficient sensitivity bound,
together with existence of a normalized finite certificate at every fixed
finite support. The cost-growth theorem supplies a precise quantitative
reason that support-uniform budget cannot be assumed.

## Verification — 2026-10-09

Leaf: `formal/GaloisForLFunctions/RHTower/WeilLogShiftFiniteGramCostGrowth.lean`.

- Final direct `lake --old env lean` leaf check with output olean exited 0,
  without warnings. New and direct-dependency oleans are current.
- All four public declarations passed `#print axioms`: only `propext`,
  `Classical.choice`, and `Quot.sound` occur. Toolchain API audit passed.
- Exactly one import in the RHTower umbrella. No full or umbrella build.
- Index refresh exited 0; module-filtered local lexical search recovered
  all four public declarations, with no missing names.
- Formal lint exited 1 solely on unrelated missing HTGeometry imports:
  PaperSplitIdealContraction, PaperSplitNormalSpace, and
  QKrawtchoukCompanionTriangular. No error names this leaf. Those unrelated
  files were not changed.

`exists_finiteWeilGram_cost_bounds` bundles weighted sensitivity, the
universal two-sign lower bound, and finite certificate existence.
`exists_finiteWeilGram_cost_escape` proves eventual escape from every
fixed cost budget along growing initial supports.

## Next conjecture

Test sharpness of the growth rate for singleton arithmetic supports.
Candidate: two-point tests at 0 and log(n), with real weights (1,1) and
(1,-1), give an eventual O(n²) upper bound. For a unit coefficient,
P_n(0)=2K(log n) tends to zero while P_n(log n)≥K(0)>0. Thus the two Gram
forms eventually have opposite signs bounded away from zero. A fixed
normalization would then have cost proportional to 1+n². This is not
proved here; audit the local corpus and each step before formalization.
No optimal constant is conjectured.

The full corpus-research goal remains active.
