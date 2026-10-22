# HF: source cup trace and native Gaussian removal

- **ID:** HF-NATIVE-20261017
- **Stage:** 1-in-progress
- **Route:** HF — Positive Hodge form on arithmetic cohomology
- **Status:** Research in progress; no qualifying contribution claimed.

## Scope

The full goal remains a significant obstruction-removing contribution for every
live route and candidate. XN was attempted previously without meeting that gate.
This turn selects HF. The frontier map is read-only. Only current Lean source is
mathematical evidence; no web, external novelty audit, old research notes,
numerical experiments, added axioms, full builds, or heartbeat overrides.

## Plan

1. Inspect the actual original-Meyer/native-BV realization, Gaussian dependence,
   and arithmetic pairing; use whole-corpus search to locate stronger results.
2. Form exact competing conjectures about removing smoothing while retaining the
   original source, differential action, and full arithmetic trace. Attack each
   before formalizing anything.
3. Prove an exact surviving statement on paper with every dependency discharged.
4. Formalize only a substantive survivor, audit with targeted foreground Lean,
   inspect axioms, wire its module, and run the formal lint gate.
5. Assess whether the result actually removes a hard HF obstruction; leave the
   full goal active unless every requested route has qualifying evidence.

`update_plan` is unavailable; this card preserves the plan across compaction.

## Starting frontier

The frontier map records a faithful original arithmetic cohomology realization
with one fixed Gaussian, a whole-source native differential intertwiner, and a
full-Jordan compact inverse. It explicitly leaves native-BV Gaussian removal,
arithmetic cup/trace identification, and source positivity open. These are leads
to verify against current Lean source, not assumed new results.

## Conjecture loop

### C1: original-topology Gaussian removal implies native-BV removal

**Verdict: incomplete; the proposed inference is invalid.**
`DeningerMeyerGaussianSourceApproximation` already proves Gaussian removal in
every original source gauge. `DeningerMeyerFiniteNativeDensity` already proves
finite native packets dense in original cohomology. Neither theorem gives
continuity of the unsmoothed native realization into global BV/full arithmetic
graph norm. The native contour argument pays reciprocal-Xi growth with a positive
Gaussian. No zero-Gaussian graph limit has been proved here.

### C2: convolution adjunction alone supplies the missing positive metric

**Verdict: REDISCOVERED adjunction; positivity does not follow.**
`DeningerMeyerConvolutionPaugam` already gives exact source convolution adjunction
for the full nondegenerate Paugam form. `DeningerMeyerConvolutionWeilTrace` gives
the complete arithmetic Weil trace, but explicitly does not identify arithmetic
sharp with the Hilbert adjoint. Extending the existing bilinear identity by
density would not pay this missing sign. No new receiver is warranted.

### C3: a fixed bounded insertion repairs ordinary-trace blindness to the cup

**Verdict: BRIDGE; paper proof below.** The ordinary convolution trace reads only
the value of the Mellin transform at each zero and misses its higher jets. The
full Paugam block reads the top complementary Hasse coefficient. A single
bounded insertion can read exactly this coefficient simultaneously at every
zero, without a multiplicity bound, damping, or a new analytic premise.

Write `H = l2 {(rho,j) : 0 <= j < m(rho)}` in the existing Hasse coordinates,
`T_g` for the actual whole-line convolution operator, and `a_k(g,rho)` for the
Mellin Hasse coefficient. Define the fixed contraction

`(E x)(rho,j) = x(rho,m(rho)-1)` if `Im rho > 0` and `j=0`, and zero otherwise.

For literal original sources put `K(g,h)=g*Jh-h*Jg`, using their existing source
convolution and reflection. The exact target is

`B([g],[h]) = Tr(T_{K(g,h)} E)`, while `Tr(T_{K(g,h)}) = 0`.

**Dependency-closed paper proof.**

1. Reversal `j -> m-1-j` permutes all Hasse coordinates isometrically. Projection
   onto upper-half-plane bottom coordinates is contractive. Their composition
   is E, hence E is bounded with norm at most one independently of multiplicity.
2. The proved full-Jordan source formula gives
   `(T_g x)(rho,j)=sum_{k=0}^j a_k(g,rho) x(rho,j-k)`.
   E sends the top basis vector of each upper block to its bottom basis vector
   and kills all other basis vectors. Consequently the diagonal of `T_g E` is
   zero except at these top slots, where it equals `a_{m-1}(g,rho)`.
3. `T_g` is trace class for every original all-weight source. Bounded composition
   preserves trace class. The absolutely convergent basis-trace identity and
   finite-fibre summation therefore give
   `Tr(T_g E)=sum_{Im rho>0} a_{m-1}(g,rho)`.
4. The existing convolution Leibniz identity identifies
   `a_{m-1}(K(g,h),rho)` with the complete Hasse Paugam block at rho, including
   every complementary derivative. The proved global block sum gives the target
   identity. Both sides descend through the genuine Poisson boundary.
5. The Mellin transform of K satisfies `F(1-s)=-F(s)`. The ordinary source trace
   is the absolutely convergent sum of F over every multiplicity copy.
   Functional-equation reflection permutes these copies, so this trace is its
   own negative and is zero.
6. If the inserted traces of K(u,v) vanish for every v, the exact identity and
   the existing zero-radical theorem for B force u=0. Thus the inserted trace
   retains the entire original class, unlike the ordinary scalar trace.

This repairs an exact operator-trace obstruction for the already constructed
alternating source product. It does not identify that product with a separate
geometric cup, prove native-BV Gaussian removal, or give a positive Hodge form.
Do not count it as the requested significant RH frontier advance without a
further source-sign mechanism. Targeted Lean and axiom verification passed.

## Formal survivor

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerMeyerPaugamInsertedTrace.lean`
implements the exact C3 proof and is imported by `RHTower.lean`.

- `deningerMeyerHilbertConvolution_topInsertion_trace` reads the highest Hasse
  coefficient of every upper block through one fixed bounded insertion.
- `deningerMeyerSourceCup_inserted_trace` identifies the inserted whole-source
  trace with the complete Paugam pairing.
- `deningerMeyerSourceCup_ordinary_trace` proves that the unmodified trace
  annihilates every alternating original-source product.
- `deningerMeyerSourceCup_trace_detects` proves that testing the inserted trace
  against all original sources detects exactly the genuine Poisson class.

The final targeted module command, run from `formal/`, exited 0:

`lake --old env lean -j 1 -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/Deninger/DeningerMeyerPaugamInsertedTrace.olean GaloisForLFunctions/RHTower/Deninger/DeningerMeyerPaugamInsertedTrace.lean`

A separate `/tmp` import and `#print axioms` audit of all eight public theorems
exited 0. Each uses only `propext`, `Classical.choice`, and `Quot.sound`.
`scripts/formal_tools.py index` exited 0 and indexed the declarations.
`git diff --check` passed. No numerical experiment, analytic premise, added axiom,
heartbeat override, full build, commit, or push was used.

The authoritative global `scripts/formal_tools.py lint --check-generated` exited
1 because twelve concurrent out-of-scope modules were unreachable from their
theorem-area umbrellas: `CHMDBVUniformConvergence`, `CHMDBVUniformGraph`,
`CHMDBoundedContinuousSource`, `CHMDCompactBVTranslations`,
`MobiusDivisorClockGraphSource`, `MobiusDivisorCriticalBVProfile`,
`ThetaCuspRatioBoundaryNormOrientation`, `BoundedVariationNormAlgebra`,
`BoundedVariationPrimitive`, `BoundedVariationUniformJump`,
`ClosedConeBochnerIntegral`, and `ContinuousKernelBochnerControl`. No error
identified this module. Global lint is not claimed to pass.

The read-only frontier-map SHA-256 remained
`6e287eaa43d5ee46e7e0ce07051102706936fbd38604e06d7423c895b717da1c`.

## Next exact question and limits

The next stronger conjecture is whether the fixed insertion preserves
`LinearMap.range deningerMeyerHasseHilbertLM`, the actual original-source image.
Finite causal synthesis proves this on finite packets, but Hilbert boundedness
and density alone do not prove it on the full image. This is not assumed by any
theorem above. A source-defined geometric cup/trace identification needs its own
construction and compatibility proof; an arbitrary square-zero algebra extension
would merely rename the already known bilinear form and is rejected.

Gaussian removal in native BV and the arithmetic sign remain unresolved. The
trace repair is a verified structural bridge, not a proof of either missing law.
It is not credited as the requested significant obstruction-removing RH advance.
The full 21-route/23-candidate goal remains active, with no route credited in this
thread. XN and HF have been attempted; select a different route next turn.

## Search coverage

Three whole-corpus deep searches and a targeted lexical search were executed
directly through `scripts/formal_tools.py research`. Deep searches completed
without a partial flag, but semantic coverage was not measured and compiler
metadata was mostly source-only, pending, or stale. The broad Gaussian query
returned irrelevant generic smoothing suggestions; these were rejected.
Applicable convolution, Hasse, Paugam, and native-source statements were checked
in the actual Lean files and the exact used dependencies compiled through the
new module. Exhaustive source-text search found no existing Paugam `opTrace`
insertion theorem. No external search or novelty claim was made.
