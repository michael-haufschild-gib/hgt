# RN: intrinsic full-multiplicity native splitting

Status: FORMALIZED, 2026-10-17. All eight production Lean leaves passed direct
audits without diagnostics. Axiom audit passed. Repository-wide formal lint
is blocked by 13 unrelated modules missing umbrella imports; details below.

Objective: remove a structural obstacle in RN with an unconditional theorem,
not an estimate, RH equivalence, or receiver. Use current Lean corpus only.
No numerical experiments, external search, novelty audit, or full builds.

## Plan

1. Identify the frontier from corpus search and actual Lean declarations.
2. Conjecture an exact structural statement; attack it before formalization.
3. Complete its paper proof, then formalize and wire the new leaves.
4. Audit each leaf directly, inspect axioms in /tmp, run formal lint, clean up.

The update_plan tool is not available in this session; this card records the plan.

## Verified starting evidence

- PaperThetaNativeGrushin: an invertible augmented pencil on the whole
  bounded-continuous native space, using a genuine compact counter-source.
- PaperThetaNativeResonantSplitting: exact one-step range and kernel at every
  resonance; zero-trace particular solution and actual theta moment defect.
- PaperThetaNativeEntireRepair: entire repair of the original uniform pencil.
- PaperThetaNativeMeyerCompleteness: full generalized root blocks already
  equal original finite Meyer packets. This source is modified by pre-existing
  work; do not edit it or claim its result as a contribution here.
- PaperThetaNativeSourceSynthesis and PaperThetaNativeCohomology: faithful
  whole-source realization after genuine Gaussian regularization.
- ThetaRenewalCausalMoments: full prime/Gamma/polar action on every lower
  causal jet equals its next whole source moment, including actual Xi
  multiplicities.

## Conjecture loop

C1: classify every bounded-continuous generalized Xi mode by original Meyer
jets. Verdict: ALREADY PROVED in PaperThetaNativeMeyerCompleteness. Do not
duplicate it.

C2: remove Gaussian regularization from whole-source native synthesis.
OPEN: reciprocal Xi introduces exponential contour growth, whereas the
original source has rapid polynomial vertical decay. Existing summability
proof cannot be specialized to zero regularization. No impossibility claimed.

C3: construct the full confluent source/cusp projection
on arbitrary native forcing, retaining every Xi multiplicity and exact
solvability at repeated resonance. Determine whether current scalar moment
repair and original-source duality already imply a stronger result.

## C3 paper proof

At an actual Xi point put N = nativePencil, B = the first column of the
Grushin inverse at zero prescribed trace, v = its unit-trace kernel vector,
b = the compact counter-source, c = actual theta moment / counter-mass,
and L = the actual resolvent tail trace. Existing inverse identities give

    NB = 1 - b c,  BN = 1 - v L,
    Nv = 0, cN = 0, Lv = 1, LB = 0, cb = 1.

Let E be the full generalized nullspace, whose dimension m is the actual
Xi multiplicity by current native completeness. Write w_j = B^j v and
a_j = c(w_j). The first nonzero a_j occurs exactly at j=m-1:

1. If every a_j vanished, all w_j would form an infinite lowering chain
   in E with nonzero bottom, contradicting finite dimension.
2. If n is the first nonzero index, w_0,...,w_n are an independent chain
   in E, hence n+1 <= m.
3. O(x) = (c B^j x)_(0<=j<=n) satisfies O(Nx)_0=0 and
   O(Nx)_(j+1)=O(x)_j, because all earlier a_j vanish. Its kernel is
   N-invariant. Its intersection with ker N is zero since ker N is Cv
   and O(v)_n=a_n != 0. Induction on nilpotence height shows O is
   injective on E. Thus m <= n+1.

Consequently the m actual integral readings O:E->C^m are an isomorphism.
In particular, a rank-one normalization by c(v) is unavailable when m>1:
the channel identities force c(v)=0 in that case. The positive replacement
is the entire confluent observation map, whose invertibility is proved at
the actual multiplicity. No simplicity conjecture is introduced.
Define P = inclusion * (O|E)^(-1) * O on the WHOLE native space. Then
P^2=P, range P=E, ker P=ker O, and PN=NP. This constructs the full
projection from source readings, without a simplicity, separation, finite
forcing, positivity, or projection-existence premise.

For W=ker O and a=a_(m-1), set

    H y = B y - (c B^m y/a) v.

For y in W, NH y=y. All m readings of H y vanish: the first m-1
shift to readings of y; the last cancels exactly against a. Kernel
uniqueness gives HN x=x on W. Iteration therefore solves N^k on W at
every order. In the coordinates O on E, N is the shift

    O(Nx)_j = 0 (j=0), O(x)_(j-1) (j>0).

For an arbitrary order k, retain only slots j<k in O(g), reconstruct
them in E, and call the resulting finite correction D_k g. Define R_k g
by reconstructing the shifted readings O(g)_(j+k), with zero outside
the m slots. Then N^k R_k g = P g-D_k g. Therefore

    S_k g = H^k(g-Pg)+R_k g,
    N^k S_k g = g-D_k g.

D_k is idempotent. Its vanishing is equivalent to exactly the first
min(k,m) actual readings vanishing. Every solution of N^k x=g is S_k g
plus an element of ker N^k, and exists exactly when those readings vanish.
This is a constructed solver with a specific original-packet correction;
the range criterion is a corollary, not the contribution's endpoint.

All operators above are bounded in the original uniform norm: B,c,L are
bounded, and inversion only occurs in the finite-dimensional observed
block. The finite correction is an actual original native Meyer packet.
BV forcing is preserved by B (the existing literal Grushin solution and
the fixed Green equation) and by finite packets; hence the repaired
solutions retain compact AC and full arithmetic admission after the
fixed Green operator. This last transport must be checked directly in
Lean, not inferred from uniform-norm boundedness.

Write K=(D-i)^(-1), where D is the literal spatial theta action. The
existing Green equation gives (D-z)K=N_z, and K commutes with N_z.
Induction, applied to actual functions at each step, gives

    (D-z)^k K^k S_k g = N_z^k S_k g = g-D_k g.

K preserves BV: its bounded-continuous solution equals the existing
native BV solution by whole-domain uniqueness. Thus for k>0 the
constructed K^k S_k g belongs to the actual native domain, with compact
AC representative and the unchanged full prime/Gamma/polar Weil form.
No domain, trace matching, regularity, or arithmetic-admission premise
is left for the caller beyond supplying an original continuous BV forcing.

Verdict: survives the algebraic attack. This targets full original-space
resonant projection/solving, not the still-open directed arithmetic sign.

## C4: eliminate auxiliary counter-source dependence

C3 exposes a stronger invariant. Its complementary space W is exactly
range N^m: all m readings vanish on N^m x, and H^m supplies a preimage
for every element of W. Therefore P is the unique projection onto the
intrinsic maximal generalized kernel E along the intrinsic range N^m.
Any other one-channel parametrix for the same pencil gives the same P,
regardless of its counter-source, trace normalization, or partial inverse.

The reduced inverse T=H(1-P) satisfies NT=TN=1-P and PT=TP=0.
It is an actual bounded complementary solver. The projection and native
splitting thus no longer depend on an auxiliary Grushin bump choice.
Paper proof complete; Lean scratch audit passed. All four generic production
leaves passed direct `lake --old env lean -j 1 <file>` audits with no diagnostics.

## Audit constraints

Hypothesis discharge: the generic algebra packages exact inverse identities
in OneChannelParametrix. PaperThetaConfluentNativeChannel proves every field
for the literal native Grushin construction and proves finite dimension and
rank from the existing original-source Meyer theorem. Native conclusions
take only an actual Xi divisor point, an order, and original forcing; there
is no user-supplied parametrix, projection, simplicity, positivity, or
spectral-completeness premise.

Pre-existing changes: frontier map, RHTower umbrella, native root transport
and completeness, XiNewtonDiscCurvature, and unrelated cards/report. Preserve.
Search reports may be source-only or stale: declarations require direct Lean
audit before relying on a new formal result.

User constraint added during work: docs/reports/rh-current-frontier-map.md
is read-only. Record results here and in Lean, never edit that map.

## Formal deliverables

- HTGeometry/OneChannelRootObservability.lean: first surviving source reading
  occurs at the exact maximal-root dimension minus one; full observability.
- HTGeometry/OneChannelRootProjection.lean: whole-space projection and
  explicit two-sided inverse on its observed complement.
- HTGeometry/OneChannelPowerSolvability.lean: constructed solvers for every
  power, exact idempotent finite defects, and complete solution classification.
- HTGeometry/OneChannelCanonicalSplitting.lean: intrinsic kernel
  `range (N^m)`, independence from auxiliary parametrices, reduced inverse.
- RHTower/PaperThetaConfluentNativeChannel.lean: all generic identities and
  finite-dimension obligations proved for the literal native theta operators.
- RHTower/PaperThetaConfluentNativeSolvability.lean: bounded native operators,
  exact original Meyer range/kernel, every-order solvers and source defects.
- RHTower/PaperThetaConfluentNativeRegularity.lean: original BV preservation,
  equality of uniform and BV Green solutions, literal repeated spatial action.
- RHTower/PaperThetaConfluentNativeArithmetic.lean: explicit native-domain
  profiles for every positive order, actual repeated equations, compact AC,
  and full signed prime/Gamma/mass/polar Weil transport.

All paths above are under `formal/GaloisForLFunctions/`. Finished modules
are wired into their respective umbrellas; no umbrella build was run.

## Scope and remaining frontier

The removed obstruction is full-multiplicity source extraction and repeated
resonant solving on arbitrary original forcing, including actual native
regularity and arithmetic admission. The projection is intrinsic; it no
longer requires a chosen finite forcing packet or a simple-zero normalization.
This does not prove the directed arithmetic sign or remove Gaussian
regularization from global whole-source synthesis. Existing native Meyer
completeness is used as an input already proved in the corpus, not claimed
as new work.

## Final audits

Each of the eight leaves above was audited directly with
`lake --old env lean <module.lean>` (one process at a time, one or two Lean
worker threads), exporting its current `.olean` and `.ilean`. All exited 0
without diagnostics. No heartbeat override, numerical experiment, full build,
or umbrella build was used to validate the contribution.

Scratch `#check @...` verified that the concrete capstones take only actual
Xi points, orders, and original forcing. Scratch `#print axioms` checked
`obstruction_order`, `projection_independent`, and the concrete exact-order,
projection-kernel, solver, defect, spatial-equation, and full-arithmetic
theorems. Every closure contains only `propext`, `Classical.choice`, and
`Quot.sound`; no added axiom or `sorryAx`.

The authoritative `scripts/formal_tools.py lint` exited 1. Its complete error
set consists of these unrelated modules missing theorem-area umbrella imports:

```text
RHTower.CHMDCompactOrbitInertia
RHTower.CHMDCompactTestSynthesis
RHTower.FiniteWeilNodalAdjacentCoupling
RHTower.FiniteWeilNodalMixtureTransport
RHTower.HedenmalmSquarefreeSummatoryConormalTransport
RHTower.LeeYangPrimePivotSpinPartitionSpectrum
RHTower.OddSectorExactSpectralInterpolation
RHTower.OddSectorGroundZeroInterpolation
RHTower.SquarefreeDiscrepancyHilbertTransport
RHTower.ThetaCuspRatioBoundaryNormOrientation
RHTower.WeilCompactNegativeSubspace
RHTower.WeilCompactOrbitInertia
HTGeometry.DenseCoreFiniteConstraints
```

No RN leaf or forbidden-declaration error was reported. Those unrelated,
concurrently edited modules were left untouched. Existing large-file warnings
also remain. Task-scoped `git diff --check` passed.

An import-artifact audit covered all 9,426 local modules in the capstone's
dependency closure and found no missing `.olean` files. A targeted Lake
build was stopped when it began rebuilding a broad dependency chain; six
interrupted dependency artifacts were restored by direct leaf checks with
their sources unchanged. All owned build processes exited. Task scratch
proofs, searches, and diagnostic files were removed. The frontier map was
never edited by this work.
