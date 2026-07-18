# Formalize the stage-2 new-scientific-knowledge corpus

- **ID:** `formalize-stage2-new-scientific-knowledge-corpus`
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION PROGRAM
- **Source:** `../2-fully-proven/new_scientific_knowledge/`
- **Statement:** Formalize every proved theorem and corollary in the 102 source cards,
  using only unconditional Lean declarations in `formal/GaloisForLFunctions/HTGeometry` and
  `formal/GaloisForLFunctions/RHTower`.

## Completion criterion

A source card is complete only after every theorem and corollary asserted as proved on paper has
an unconditional Lean theorem with the same mathematical content. Existing bridge lemmas,
conditional wrappers, named `Prop` aliases, finite stand-ins for analytic statements, and
formalizations of only one implication do not discharge a stronger paper theorem.

For each completed card:

1. record the exact Lean declarations and modules;
2. check the smallest owning module in the foreground;
3. inspect theorem axioms from a scratch file;
4. wire the owning theorem-area umbrella;
5. refresh the generated Lean API/gap/overview indexes;
6. pass the formal lint gate; and
7. move the source card to stage 3 only when its entire proved surface is represented.

## Build discipline

- At most one Lean process may be active across this shared workspace.
- Every check is foreground and guarded by a process check.
- Use the active `formal/.lake` cache and build only the smallest changed leaf or umbrella.
- Do not run a broad build when a leaf check decides the issue.
- Do not use numerical pre-certification or any other computation as evidence.
- Proofs are unconditional; missing foundations are implementation work, not permission to weaken
  the theorem.

## Current lane

The first implementation target is `split-source-boundary-universality`. The existing source
theorems already give the arbitrary-family mixed dependence criterion. The missing paper surface is
the simultaneous coboundary quotient, localization to the differential-operator fraction field,
its represented matroid, and the finite-set rank equality.

The first reusable leaf is a generic localized quotient matroid for an arbitrary module. It uses
the already formalized symmetric-algebra criterion to represent linear independence without a
finite-coordinate or finite-dimensional hypothesis.

## Known foundation clusters

- The Manin-horizon cards require genuine abelian-variety, universal-vectorial-extension, Manin-map,
  differential-field-rank, and Kolchin-group foundations not currently present in the project or
  mathlib.
- The projective-horizon monodromy/building cards require projective geometry, finite morphisms,
  generic etaleness, degree/Bezout multiplicity, splitting fields, and building homotopy foundations.
- The triptic residue cards require the analytic meromorphic/triptic realization and residue
  reciprocity, beyond the existing abstract Kummer group theory.
- These are active implementation clusters, not exclusions from this program.

## Corpus ledger

- [ ] `abelian-multiplication-tail-manin-horizon` — four paper surfaces inventoried; fixed-field
  intersection core exists, while abelian varieties, universal vectorial extensions, the Manin
  map, Kolchin groups, and differential-field rank must be implemented
- [ ] `active-quasi-abelian-facet-palette-necessity` — theorem/corollary surface inventory pending
- [ ] `active-quasi-abelian-palette-exact-ht-dimension-classification` — theorem/corollary surface inventory pending
- [ ] `additive-heat-aperture-shifted-zeta-echo-ladder` — theorem/corollary surface inventory pending
- [ ] `additive-heat-aperture-zeta-zero-echo` — theorem/corollary surface inventory pending
- [ ] `all-depth-compatible-pair-face-differential-matroid` — theorem/corollary surface inventory pending
- [ ] `all-depth-pair-face-signature-completeness` — theorem/corollary surface inventory pending
- [ ] `all-order-multiple-elliptic-gamma-structural-differential-matroid` — theorem/corollary surface inventory pending
- [ ] `all-order-multiple-sine-stanley-reisner-differential-matroid` — theorem/corollary surface inventory pending
- [ ] `almost-periodic-autonomous-ade-finite-frequency-law` — theorem/corollary surface inventory pending
- [ ] `almost-periodic-implicit-ade-relative-frequency-law` — theorem/corollary surface inventory pending
- [ ] `archimedean-relative-prime-cocycle-curvature` — theorem/corollary surface inventory pending
- [ ] `barnes-differential-source-face-matrix-factorization` — theorem/corollary surface inventory pending
- [ ] `barnes-multiple-gamma-translation-annihilator` — theorem/corollary surface inventory pending
- [ ] `boundary-wedge-uniform-ht-dimension-gap` — theorem/corollary surface inventory pending
- [ ] `bounded-relation-log-magnitude-hypertranscendence` — theorem/corollary surface inventory pending
- [ ] `charged-scalar-core-fixed-current-torsor` — theorem/corollary surface inventory pending
- [ ] `commutative-d-group-source-boundary-universality` — Theorems A/B and the sharp-kernel
  corollary inventoried; depends on the localized source quotient plus genuine algebraic D-group
  and logarithmic-derivative foundations
- [ ] `complete-scalar-persistent-gauge-reduction` — theorem/corollary surface inventory pending
- [ ] `constrained-prolate-arithmetic-dilation-operator-limit` — theorem/corollary surface inventory pending
- [ ] `constrained-prolate-fixed-mode-spectral-ladder` — theorem/corollary surface inventory pending
- [ ] `constrained-prolate-fourier-parity-floor-separation` — theorem/corollary surface inventory pending
- [ ] `constrained-prolate-full-radial-prime-charge-law` — theorem/corollary surface inventory pending
- [ ] `constrained-prolate-radial-leakage-divisibility-spectrum` — theorem/corollary surface inventory pending
- [ ] `constrained-prolate-two-mode-ground-state` — theorem/corollary surface inventory pending
- [ ] `differential-variational-building-balance-law` — theorem/corollary surface inventory pending
- [ ] `double-sine-defect-coset-differential-matroid` — theorem/corollary surface inventory pending
- [ ] `double-sine-translation-annihilator` — theorem/corollary surface inventory pending
- [ ] `eigenplurivolume-log-crepant-orbifold` — theorem/corollary surface inventory pending
- [ ] `elliptic-gamma-rank-three-da-spectrum` — theorem/corollary surface inventory pending
- [ ] `elliptic-shadow-ht-capacity-nonattainment` — theorem/corollary surface inventory pending
- [ ] `embedded-manin-horizon-isogeny-reconstruction` — theorem/corollary surface inventory pending
- [ ] `faithful-facet-separation-dimension-ht-realization` — theorem/corollary surface inventory pending
- [ ] `finite-archimedean-gamma-product-boundary-law` — theorem/corollary surface inventory pending
- [ ] `finite-real-shift-gamma-projective-boundary-law` — theorem/corollary surface inventory pending
- [ ] `fixed-divisor-full-complex-translation-freeness` — theorem/corollary surface inventory pending
- [ ] `floquet-orbifold-tail-emergence` — theorem/corollary surface inventory pending
- [ ] `gamma-projective-boundary-finite-phase-law` — theorem/corollary surface inventory pending
- [ ] `gauss-component-quasi-inner-residue-hierarchy` — theorem/corollary surface inventory pending
- [ ] `gaussian-torsion-language-hypertranscendence` — theorem/corollary surface inventory pending
- [ ] `hedenmalm-pair-weil-polarization-law` — theorem/corollary surface inventory pending
- [ ] `helson-universal-ht-arbitrary-divisor-orthogonality` — theorem/corollary surface inventory pending
- [ ] `herglotz-full-translation-ht-krein-index-orthogonality` — theorem/corollary surface inventory pending
- [ ] `ht-period-rank-one-scalar-stanley-reisner-principalization` — theorem/corollary surface inventory pending
- [ ] `ht-tail-no-hair-and-embedded-reconstruction-boundary` — theorem/corollary surface inventory pending
- [ ] `hypertranscendental-clock-incompressibility` — theorem/corollary surface inventory pending
- [ ] `hypertranscendental-hochster-source-coherence-duality` — theorem/corollary surface inventory pending
- [ ] `hypertranscendental-pair-localization-noncompression` — theorem/corollary surface inventory pending
- [ ] `infinite-bohr-ht-boundary-maximal-ht-outer-orbit` — theorem/corollary surface inventory pending
- [ ] `irrational-elliptic-gamma-hypertranscendence-matroid` — theorem/corollary surface inventory pending
- [ ] `irrational-elliptic-gamma-pointed-bi-anomaly-fracture` — theorem/corollary surface inventory pending
- [ ] `irrational-triptic-source-effectivity-character` — theorem/corollary surface inventory pending
- [ ] `isogeny-tail-maurer-cartan-holography` — theorem/corollary surface inventory pending
- [ ] `jet-horizon-translation-gauge-classification` — theorem/corollary surface inventory pending
- [ ] `maximal-ht-parabolic-orbit-collapse` — theorem/corollary surface inventory pending
- [ ] `multiple-elliptic-gamma-relative-log-characteristic-arrangement` — theorem/corollary surface inventory pending
- [ ] `multiple-elliptic-gamma-transverse-constraint-depth` — theorem/corollary surface inventory pending
- [ ] `multiple-gamma-effective-fracture-descent-orthogonality` — theorem/corollary surface inventory pending
- [ ] `multiple-gamma-period-excess-closure-phase-transition` — theorem/corollary surface inventory pending
- [ ] `multiple-gamma-physical-characteristic-fat-point` — theorem/corollary surface inventory pending
- [ ] `nonautonomous-ht-tail-projective-time-law` — theorem/corollary surface inventory pending
- [ ] `nonautonomous-isogeny-tail-time-splitting` — theorem/corollary surface inventory pending
- [ ] `nonautonomous-rational-complete-tail-orbifold-classification` — theorem/corollary surface inventory pending
- [ ] `nonautonomous-rational-first-order-tail-orbifold-law` — theorem/corollary surface inventory pending
- [ ] `noncompact-period-quotient-facet-escape-law` — theorem/corollary surface inventory pending
- [ ] `nonlinear-rational-observation-curve-horizon-reconstruction` — theorem/corollary surface inventory pending
- [ ] `orbifold-tail-holographic-reconstruction` — theorem/corollary surface inventory pending
- [ ] `order-three-elliptic-gamma-bottom-face-joint-atomicity` — theorem/corollary surface inventory pending
- [ ] `order-three-elliptic-gamma-full-structural-differential-matroid` — theorem/corollary surface inventory pending
- [ ] `order-two-elliptic-gamma-full-structural-differential-matroid` — theorem/corollary surface inventory pending
- [ ] `order-two-multiple-gamma-period-deletion-phase-split` — theorem/corollary surface inventory pending
- [ ] `periodic-pencil-intrinsic-ht-dimension-two` — theorem/corollary surface inventory pending
- [ ] `phase-holomorphic-autonomous-ade-frequency-rank` — theorem/corollary surface inventory pending
- [ ] `prescribed-gap-process-order-one-maximal-ht-profield` — theorem/corollary surface inventory pending
- [ ] `prime-euler-unit-tangent-completeness` — theorem/corollary surface inventory pending
- [ ] `prime-modulated-weyl-idealizer-collapse-on-xi-sampling` — theorem/corollary surface inventory pending
- [ ] `projective-horizon-all-depth-cusped-building` — theorem/corollary surface inventory pending
- [ ] `projective-horizon-building-schwarzian-complementarity` — theorem/corollary surface inventory pending
- [ ] `projective-horizon-critical-binomial-multiplicity` — paper theorem inventoried; current
  Lean has the critical Jacobian/minor core, while the exact finite-map Bezout and generic-etale
  multiplicity theorem remains to be built
- [ ] `projective-horizon-depth-two-building-collapse` — theorem/corollary surface inventory pending
- [ ] `projective-horizon-depth-two-current-algebra-transition` — theorem/corollary surface inventory pending
- [ ] `projective-horizon-full-symmetric-monodromy` — paper theorem inventoried; requires the
  exact cover, ramification, transposition-generation, and splitting-field/Galois foundations
- [ ] `projective-horizon-one-sided-depth-transition` — theorem/corollary surface inventory pending
- [ ] `projective-horizon-one-step-postcritical-rigidity` — paper theorem inventoried; primitive
  field and etale-descent reconstruction foundations remain to be implemented
- [ ] `projective-horizon-rank-one-full-monodromy` — paper theorem inventoried; reciprocal
  coefficient/cotangent cores exist, while the triangular cover and full splitting-field
  monodromy theorem remain
- [ ] `projective-horizon-solomon-tits-topological-charge` — theorem/corollary surface inventory pending
- [ ] `projective-horizon-tits-building` — theorem/corollary surface inventory pending
- [ ] `projective-ht-horizon-symmetric-space-boundary` — theorem/corollary surface inventory pending
- [ ] `rational-coarse-graining-orbifold-tail-classification` — theorem/corollary surface inventory pending
- [ ] `scalar-differential-inversive-core-projective-law` — theorem/corollary surface inventory pending
- [ ] `scalar-ht-horizon-celestial-sphere` — theorem/corollary surface inventory pending
- [ ] `scalar-ht-persistent-clock-character-law` — theorem/corollary surface inventory pending
- [ ] `split-source-boundary-universality` — in progress: exact mixed dependence and raw/log rank
  preservation already exist; implementing the simultaneous coboundary quotient, fraction-field
  localization, represented matroid, and finite-set rank equality
- [ ] `stable-coframe-log-calabi-yau-rigidity` — theorem/corollary surface inventory pending
- [ ] `symmetry-caged-fixed-divisor-full-orbit-freeness` — theorem/corollary surface inventory pending
- [ ] `toric-log-calabi-yau-tail` — theorem/corollary surface inventory pending
- [ ] `torsion-universal-phase-polynomial-magnitude-hypertranscendence` — theorem/corollary surface inventory pending
- [ ] `torusless-quasi-abelian-fixed-factor-all-order-jet-ampleness` — theorem/corollary surface inventory pending
- [ ] `triptic-ht-kummer-content-root-classification` — abstract Kummer group-theoretic core
  exists; the analytic meromorphic/triptic realization and exact DA-kernel identification remain
- [ ] `triptic-orbit-residue-reciprocity` — exact residue/DA/annihilator surfaces inventoried;
  the analytic triptic orbit and residue-reciprocity foundations remain to be implemented
- [ ] `universal-first-order-entire-cascade-unit-cost` — theorem/corollary surface inventory pending
- [ ] `weighted-euler-tangent-global-graph-decoupling` — theorem/corollary surface inventory pending
