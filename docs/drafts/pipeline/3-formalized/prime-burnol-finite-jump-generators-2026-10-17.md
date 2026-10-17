# Finite-jump classification of bounded actual-prime Burnol generators

- **ID:** prime-burnol-finite-jump-generators-2026-10-17
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — verified contribution 9 toward the active 100-theorem goal
- **Source:** whole Lean corpus; actual-prime holomorphic classification, physical-cone Bernstein representation, convolution/compound-Poisson calculus.
- **Statement:** A bounded complex operator preserving every literal critical-prime feature line generates a positive contraction semigroup iff it has a unique finite positive jump measure with no atom at zero and a nonnegative killing rate.

## Exact theorem

Let H be the literal `HTGeometry.BurnolHalfLineL2`, and let
`K_h f(t) = t/(t+h) f(t+h)` be its existing weighted translations.
For a bounded complex-linear A on H preserving every
`primeLogCriticalLaplaceFeatureL2 p` line, the following are equivalent:

1. For every real t >= 0, exp(t A) preserves the a.e. real-nonnegative cone and has norm <= 1.
2. There exist unique kappa >= 0 and finite positive measure nu on the nonnegative reals,
   with nu({0}) = 0, such that
   `A = integral K_h dnu(h) - (kappa + nu(univ)) I`.

The data recover the full evolution, including its convergent operator-exponential
series, positive realization for every admissible nu and kappa, exact norm
`||exp(t A)|| = exp(-kappa*t)`, and actual-prime eigenvalue
`-kappa + integral (exp(-h*log p)-1) dnu(h)`.
These are one classification contribution. No count for helpers or individual corollaries.
This candidate concerns bounded generators. No assertion of a complete classification of
unbounded generators or all strongly continuous semigroups is made.

## Significance and prior-art audit

The new object is the infinitesimal dynamics. Its hard implication is that positivity of every exponential forces a finite
jump measure after a scalar diagonal correction; the atom at zero must then be removed to
make the jump/killing decomposition unique. The converse constructs an entire class of actual
prime-compatible positive dynamics without an RH premise or source-admission condition.

Whole-corpus deep search: 73,164 inventoried files, 1,082,922 declarations; partial=false;
semantic coverage unmeasured and compiler metadata mostly stale/source-only. Direct source
inspection remains authoritative. Three completed deep queries covered affine-scale Gamma
matroids, toric differential relation presentations, and positive semigroup/Levy generator
classification. Their temporary outputs were inspected; coverage and source findings are retained
here. The affine-scale Gamma lead remains uncounted:
generic Laurent differential matroids and complete jet-pivot relation ideals already exist.

Existing `PrimeBurnolSymbolClassification`, `PrimeBurnolPositiveMeasureClassification`,
`BurnolPositiveShiftMeasure` classify static bounded operators and positive measures.
`ConvolutionAtomBounds` constructs compound-Poisson laws but does not recover a generator
from positivity of its exponential. `CHMDBoundedPrimeGenerator` is an adjoint-square generator
on a different mass space. `LiClockThetaSignedGammaPositiveJumpCriterion` treats a specific
Gamma mixture and an RH-equivalent sign condition; it does not give the proposed unconditional
classification of all bounded critical-prime generators.

## Dependency-closed paper proof [PROVED HERE]

1. Actual-prime rigidity extends the eigenvalue function of A to a bounded holomorphic symbol
   a on the right half-plane, with |a| <= ||A||. Operator exponentiation has symbol exp(t*a).
2. Positivity of exp(t A) makes exp(t*a(x)) real and completely monotone for every t >= 0.
   Differentiation at t=0 first gives a(x) real. For every positive-order alternating finite
   difference, differentiation at t=0 preserves nonnegativity because its value at zero is zero.
   The zeroth difference of a(x)+||A|| is nonnegative by the symbol bound. Hence
   a+||A|| is completely monotone. Its continuity and boundedness supply Bernstein's finite
   measure tau. Actual-prime totality identifies A+||A|| I with its shift mixture.
3. Split tau into its atom m at zero and nu=tau restricted to (0,infinity). Then
   A=K_nu-c I, c=||A||-m. Let x decrease to zero in the contractive eigenvalue inequality
   a(x)<=0: mass(nu)<=c. Thus kappa=c-mass(nu)>=0.
4. As x tends to infinity, the Laplace transform of nu tends to zero by dominated convergence
   and nu({0})=0. Therefore c=-lim a(x). As x decreases to zero, kappa=-lim a(x).
   These two limits and positive Laplace uniqueness make both nu and kappa unique. An equivalent
   finite-measure proof used in Lean adds the two nonnegative scalar constants as zero atoms
   on opposite sides, applies mixture injectivity, and compares the zero atoms first.
5. Conversely, for any finite positive nu and kappa>=0, K_nu is positive and bounded, with
   norm mass(nu). The norm-convergent exponential series has positive terms and acts on each
   prime feature with the displayed exponential eigenvalue. Multiplication by
   exp(-t*(kappa+mass(nu))) preserves positivity. The exponential norm estimate gives the upper
   bound exp(-kappa*t); real feature eigenvalues as x decreases to zero give the matching lower
   bound. The exponential addition law gives the semigroup property and norm continuity.

Details of the infinitesimal step: write D_n=(-1)^n Delta_delta^n. For n>0,
F(t)=D_n(exp(t*a))(x) has F(0)=0 and F(t)>=0 for t>0, so its right derivative
F'(0)=D_n(a)(x) is nonnegative. Only a finite linear combination is differentiated.
The imaginary part of exp(t*a(x)) vanishes for all t>=0, so its right derivative
at zero is Im(a(x))=0. The real symbol bound gives a(x)+||A||>=0. Thus the complete
monotonicity claim includes every order, with no differentiability assumption in x beyond
the existing holomorphic symbol. Antitonicity and boundedness give the finite right limit
required by `exists_finiteLaplaceMeasure_of_completelyMonotoneOn`.

The contraction argument uses ||exp(A)||<=1 at time one: its real feature eigenvalue
is exp(a(x)), hence a(x)<=0. The two measure limits follow from domination by one.
For uniqueness, equal generators give equal Laplace transforms after their scalar constants
are identified by the infinity limit; positive Laplace uniqueness identifies the measures,
then their masses identify kappa. For the converse the cone is closed in L2, so positive
partial sums of the norm-convergent exponential series have a positive limit. No interchange
of an operator-norm Bochner integral with a discontinuous shift family is used.

The exact norm lower bound follows from normalized nonzero real-rate feature vectors:
||exp(t*A)||>=exp(t*a(x)), and x decreases to zero. Norm continuity and the series follow
from boundedness of A. This completes the paper dependency audit. The advance over the
static result is the necessary and sufficient infinitesimal condition, canonical zero-atom
removal, unique jump/killing recovery, and complete positive dynamical realization.

No numerical evidence, old research prose, web sources, assumed RH, or unproved arithmetic
admission is used. The frontier map is read only.

## Gates

- [x] 0 -> 1: exact natural operator class, unconditional iff, actual-source realization, proof mechanism.
- [x] 1 -> 2: dependency-closed paper proof and novelty/significance review.
- [x] 2 -> 3: targeted single-process Lean builds, public signature and axiom audit, umbrella wiring,
  generated metadata and authoritative lint result recorded.
- [ ] 3 -> 4: publication-ready standalone treatment.

## Log

- 2026-10-17 — Created after rejecting the affine-scale matroid lead as insufficiently independent.
  Count remains 8/100. No new Lean code yet.
- 2026-10-17 — Paper proof closed. Bounded-generator scope is deliberate; the stronger full
  unbounded Levy classification is not asserted. All formalization and counting gates remain open.
- 2026-10-17 — `HTGeometry/InfinitesimalCompleteMonotonicity.lean` target compiled clean with
  `lake --old env lean -j 1 -o ...`; realness of the generator symbol and complete monotonicity
  of its scalar correction are now formal. Operator evolution and canonical measure extraction
  remain. Count stays 8/100.
- 2026-10-17 — `RHTower/PrimeBurnolOperatorExponential.lean` target compiled clean: norm-convergent
  operator-series eigenvalue calculation, physical-cone positivity for positive generators,
  actual-prime evolution eigenvalues, and full holomorphic evolution symbol. Uniqueness can
  equivalently be proved without the infinity limit: add positive zero atoms to the two sides,
  use mixture injectivity, compare their zero atoms, then cancel the common scalar. This uses
  only finite measures and proves the same canonical decomposition.
- 2026-10-17 — Canonical measure scratch proof compiled clean: `BurnolJumpData` contains only
  a finite positive measure, zero-atom exclusion, and a nonnegative killing rate; its generator
  map is injective. Target leaf `RHTower/PrimeBurnolJumpMeasure.lean` now building. No count yet.
- 2026-10-17 — `PrimeBurnolJumpMeasure.lean` target compiled clean. The forward extraction scratch
  now includes the full canonical datum construction. Its proof only needs contractivity at time
  one, together with positivity at every nonnegative time; the converse will recover contractivity
  at every time from the nonnegative killing rate. This sharpening belongs to the same contribution.
- 2026-10-17 — `RHTower/PrimeBurnolGeneratorMeasure.lean` target compiled clean. Both the positive
  scalar-correction measure theorem and full canonical datum recovery theorem are formal,
  with only actual-prime line preservation, all-time physical positivity, and time-one
  contractivity as hypotheses. Converse evolution formulas are under verification.
- 2026-10-17 — `RHTower/PrimeBurnolJumpEvolution.lean` target compiled clean: every datum realizes
  positive evolution, exact norm `exp(-t*killing)`, norm continuity, semigroup law, a convergent
  positive jump series, and the literal weighted-jump integral. The final iff, uniqueness, and
  explicit unit-jump admission are now building in `PrimeBurnolFiniteJumpClassification.lean`.
- 2026-10-17 — All six target leaves compiled with empty logs. Final iff, time-one sufficiency,
  and explicit `K_1-I` positive norm-one evolution passed. All 44 public declaration names were
  checked against the whole source corpus with no collisions. Six leaves wired once into their
  theorem-area umbrellas. Axiom audit, ten primary signature checks, and two definition/structure
  inspections are running; count remains 8/100 until the remaining integration gates are recorded.
- 2026-10-17 — Final audit complete. All 44 public declarations have exactly
  `[propext, Classical.choice, Quot.sound]`; ten primary signatures and both the natural generator
  predicate and canonical datum structure were inspected. No RH, unknown source admission, or
  unproved independence premise occurs. All six source hashes remain unchanged and their compiled
  objects are fresh. Index generation passes. Global `lint --check-generated` has one error:
  unrelated concurrent `RHTower.BlindCoreFarkasSeparation` is unreachable from its umbrella, plus
  381 existing large-file warnings. No generated drift or forbidden declarations. Global lint is
  **not** claimed green. All owned wiring and proof gates pass; consistent with the ledger's
  earlier audits, the unrelated module does not invalidate this closed contribution. Count once.
- 2026-10-17 — Removed exactly 30 owned scratch, search and verification temporary files after
  retaining the certificate below; absence verified. No work remains on this contribution.

## Lean certificate

Primary theorem:
`RHTower.primeBurnol_positive_contraction_generator_iff_unique_jump`.
Its input is the actual bounded operator; the predicate spells out literal critical-prime line
preservation and physical positive contraction evolution. `BurnolJumpData` has only a finite
positive NNReal measure, zero-atom exclusion and nonnegative killing rate.

The recovery theorem `primeBurnol_positive_contraction_generator_exists` needs only contractivity
at time one. `BurnolJumpData.generator_admission`, `generator_apply`, `evolution_norm`, and
`evolution_jumpSeries` provide full realization, the literal jump integral, exact decay, and a
norm-convergent Poisson series. `primeBurnol_unitJump_evolution` discharges every measure admission
for the explicit native operator `K_1-I`, whose positive evolution has norm one.

Every leaf was compiled with `lake --old env lean -j 1 -o <leaf.olean> <leaf.lean>`; no full build
or heartbeat increase. Axiom printing was confined to `/tmp`. All six imports occur exactly once
in their theorem-area umbrellas.

| Leaf under `formal/GaloisForLFunctions/` | SHA-256 |
| --- | --- |
| `HTGeometry/InfinitesimalCompleteMonotonicity.lean` | `f528b4b19921aac313164132add47e8e7fccbb34a6c1262fd28be0be7e1fc5dd` |
| `RHTower/PrimeBurnolOperatorExponential.lean` | `4d3788783e6f54d501b5d928f17365ba23999149d99c56b3b67137681a26545a` |
| `RHTower/PrimeBurnolJumpMeasure.lean` | `340ec4b403f64b7f9961bb78618912ae43bcd7ca1745487372d385bc9e74ad1c` |
| `RHTower/PrimeBurnolGeneratorMeasure.lean` | `1b3f0f99c29d96660f85c994badfa5260a98abbe39b62fdee6ded50a96290f01` |
| `RHTower/PrimeBurnolJumpEvolution.lean` | `c31a53b06880d54cc3bd731ead98cfc87f5181b1c88ccd38a3e22b2925f7591b` |
| `RHTower/PrimeBurnolFiniteJumpClassification.lean` | `792de6e18b8176a8224f372783f553aed3b286c4132ca34bcc704e5b6f408e80` |
