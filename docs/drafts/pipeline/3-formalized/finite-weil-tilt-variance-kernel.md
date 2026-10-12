# Finite Weil tilt variance kernel

Status: formalized and natively audited (2026-10-12).

## Objective and local evidence

Connect global equality of actual finite quadratic tilts to the variance of the
potential difference under any third quadratic tilt. Prove invariance of the
zero-variance observables and replace fast replication's law-inequality condition
by positive variance under an arbitrary, even depth-dependent, probe tilt.

Only local Lean sources provide mathematical evidence. All 37 scoped WeilLogShift
variance/covariance records were inspected across two pages. Existing results
give coordinate covariance limits and finite centering bounds. The HTGeometry
tilt/variance/kernel query returned no declarations. NavierStokesFiniteTiltConvexity
has strict finite scalar covariance under a nonconstant-score premise; this
increment concerns exact equivalences for the actual probability measures.

## Dependency-closed proof

1. For a probability measure and an L2 real observable f, Var(f)=0 iff f is
   almost everywhere constant. The forward direction is the local Mathlib
   zero-variance theorem; the reverse uses variance congruence and constant variance.
   L2 is essential because real-valued variance alone can discard infinite variance.
2. Each finite quadratic tilt is equivalent in null sets to its canonical base
   measure. The previous exact support theorem therefore transfers to every tilt:
   any predicate holds almost everywhere iff it holds at every source atom.
3. Existing finite-tilt integrability holds for every real function, including f
   and f squared. Hence every such f belongs to L2 without an added premise.
   Zero variance is exactly equality of all atom values with the value at atom 0.
4. The atom-value criterion does not depend on which tilt is used. Thus the full
   collection of zero-variance observables is identical under all coefficient triples.
5. Apply this to Q(a-A,b-B,d-D). The previous finite-law equality theorem yields
   equality of the two laws iff its variance is zero under ANY third tilt.
   Nonnegativity yields unequal laws iff that variance is strictly positive.
6. Substitute the strict criterion into fast replication, permitting arbitrary
   probe coefficients u(r),v(r),w(r). No analytic premise remains at the root;
   all finite depths, all coefficient triples, and arbitrary depth schedules apply.

## Plan

1. Native local API audit; generic zero-variance rigidity.
2. Actual tilted-support equivalence, unconditional L2, and common variance kernel.
3. Actual quadratic equality/strictness and fast-replication variance receiver.
4. Sequential native leaf checks; umbrella wiring; axiom, dependency, index,
   whitespace, and single repository lint audits.

## Working verification log

- Seven local API references and the constant-variance scratch proof passed natively.
- VarianceGaugeRigidity passed with an empty native log.
- WeilLogShiftTiltVarianceKernel passed with an empty native log. Its four
  theorems include arbitrary predicates, arbitrary real observables in L2,
  anchored zero-variance characterization, and independence from probe coefficients.
- WeilLogShiftQuadraticVarianceRigidity passed with an empty native log: equality
  of the two laws is equivalent to zero variance under any probe; inequality is
  equivalent to strict positivity. The replication leaf also passed with an
  empty native log.

## Formalized declarations

- HTGeometry/VarianceGaugeRigidity.lean: variance_eq_zero_iff_ae_const.
- RHTower/WeilLogShiftTiltVarianceKernel.lean: the actual finite quadratic tilt's
  ae_iff, memLp_two, variance_eq_zero_iff_values, and variance_eq_zero_iff theorems.
- RHTower/WeilLogShiftQuadraticVarianceRigidity.lean: actual finite-law equality
  iff probe variance is zero, and inequality iff probe variance is positive.
- RHTower/WeilLogShiftQuadraticVarianceReplication.lean: exact fast-separation
  criterion under arbitrary coefficient schedules for the probe law.

## Verification

- Four sequential native leaf checks passed with empty logs. Both umbrellas
  are wired; no umbrella or full build was run.
- Eight unique declarations, eight direct import edges, seven incoming imports,
  four fresh objects, direct dependency freshness, and unique umbrella imports.
- Scoped source-index publication covers all eight declarations, with no partial
  flags, markers, or stderr diagnostics.
- Source and umbrella whitespace checks passed.
- One repository lint run: eight unrelated errors and 367 warnings. Unreachable
  RHTower modules: CCMPolarOddPrimeJumps, Sieve.FourthDerivativeTestSharp,
  XiSliceHeatRateInteriorLindelof, ZetaFiveSeventhsLineBound, ZetaStripInterpolation.
  Unreachable HTGeometry modules: HurwitzZetaEulerMaclaurinBridge,
  QKrawtchoukCompanionTriangular. Existing sorry in
  RHTower/CCMPolarOddPrimeJumps.lean:104, ccmPolarOddSource_eq_core_add_atoms.
  No error belongs to the four leaves in this increment.
- Final native scratch audit passed eight axiom reports, seven API references,
  and the constant-variance example. Only propext, Classical.choice, and Quot.sound
  occur. Artifacts use /tmp/hgt-weil-tilt-variance-; native leaf logs use /tmp/hgt-
  followed by the leaf basename and .log.

## Boundary

This identifies the invariant kernel, not its uniform dimension or coefficient
basis. Quantitative variance limits, prescribed replication rates, and monotone
intermediate-target schedules remain separate frontiers. Existing mixed-moment
limits suggest a later route to explicit quadratic-variance limits; none is
claimed in this increment.
The invariant kernel is for tilts of the same finite base law at fixed r,k;
it is not a claim about kernels at different depths or the Gaussian limit.
The corpus-wide research goal remains active.
