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

- Although the earlier hard single-process restriction was retired, the 2026-07-18 efficiency
  correction restores a single root-issued **compiler lease**: agents parallelize mathematical
  reasoning, API search, and disjoint source preparation, but at most one Lean process runs at a
  time.  An agent asks root before taking the lease and releases it immediately after the check.
- A compiler check is justified only after a coherent theorem layer or obstruction-closing proof
  increment is prepared.  Do not elaborate after tiny edits and do not run `lake build` merely to
  repeat a successful direct source check.
- Defer exact module builds, scratch axiom audits, umbrella builds, generated indexes, and lint to
  one serialized tranche gate after several leaves are ready.  Never overlap that gate with leaf
  elaboration.
- Use the active `formal/.lake` cache and build only the smallest changed leaf or umbrella.
- Do not run a broad build when a leaf check decides the issue.
- Do not use numerical pre-certification or any other computation as evidence.
- Proofs are unconditional; missing foundations are implementation work, not permission to weaken
  the theorem.

## Rolling parallel pipeline

Use four live roles, reassigned at batch boundaries rather than one agent per card:

1. **Card compiler.** Stay one reusable foundation cluster ahead.  Produce the exact paper
   theorem/corollary inventory, existing declaration map, missing-lemma DAG, candidate Lean
   signatures, proof plan, ownership/import boundary, and the decisive completion test.  Resolve
   mathematical ambiguity before handing the packet to an implementation lane.
2. **Implementation lanes.** Two agents own disjoint scratch and leaf files and accumulate
   substantial prepared declaration layers.  They share the single compiler lease at meaningful
   checkpoints; compiler failures feed back into the packet whenever they expose a mathematical
   or representation error.
3. **Root implementation/integration.** Root remains a third implementation lane except at batch
   gates, when it builds all newly green targets together, audits their axioms together, wires
   umbrellas once, and runs generated-index/lint checks once.

An upstream agent may supply a short untested scaffold containing imports, exact statements, and
obvious rewrite structure.  It must not hand off a large speculative proof: unresolved Lean terms
are compiler debt, not parallel progress.  Parallelize by shared foundations rather than by card;
one foundation leaf should discharge every dependent card capstone.

When the four in-task slots are full, additional background tasks may be used only as read-only
card compilers.  They do not build Lean or edit the shared checkout; their completed packets enter
the same dependency-prioritized implementation queue.  Extra same-tree implementation tasks would
reintroduce file ownership and compiler-contention failures, so implementation remains in the
coordinated four-slot pool.

## Current tranche

- `split-source-boundary-universality`: the formerly missing simultaneous coboundary quotient,
  fraction-field localization, represented differential matroid, and finite-packet rank formula
  now exist in `LocalizedQuotientMatroid`, `SourceBoundaryQuotientMatroid`, and
  `SplitSourceBoundaryMatroid`.  The exact owning target and scratch axiom audit pass; the remaining
  work is the serialized umbrella/index/lint gate and card promotion.
- scalar/Lüroth lane: `DifferentialKernelCharacteristic` now constructs a genuine minimal-rank
  irreducible characteristic relation with initial and separant outside the evaluation kernel;
  `DifferentialCharacteristicPseudoReduction` now proves nonmonic pseudo-division, differential
  high-jet and leader reduction, derivation-stable saturation, and the characteristic-package
  capstone.  The active exclusive leaf is `DifferentialLurothCoefficient`, implementing primitive
  two-copy denominator clearing and Ritt's normalized coefficient-ratio theorem.
- bounded/ADE/torsion lane: the bounded-relation and polynomial torsion-language cards are
  leaf-complete.  The active exclusive leaf is `GaussianTorsionLanguageTailLock`; its finite
  Fourier approximation compiler and Gaussian tail domination are checked.  The current source
  batch now constructs intrinsic signed-offset faces, proves exact key/full-weight-polynomial
  invariance under expanding centered windows, extracts a fixed nonzero atom on the anchor's exact
  least-source face, maximizes the genuinely attained grouped-weight degree, and bounds every
  polynomial on that complete face by the same degree.  One batched direct check exposed only
  local casts/decidability/let-unfolding errors; all were repaired source-only without an immediate
  rerun.  The source batch now also contains the cancellation-safe fixed-node Lagrange
  interpolation theorem, translated-coefficient control, and a uniform grouped-weight bound after
  normalization by the genuinely attained degree, so cancellation among higher-order jet
  monomials is no longer an open step.  The active mathematical step is the concrete arbitrary-ADE
  Gaussian exterior split and unconditional contradiction capstone.
- projective fixed-field lane: `ProjectiveHorizonCurrentFixedField` connects the actual rational
  current action to the free-coordinate fixed-field theorem.  The 12-card compiler audit found that
  `ProjectiveHorizonDepthTwoCurrentTransition` already declares the full scalar free-current
  `E`--`F`/`H` relations, deep current-kernel transition, and depth-one Schwarzian inclusion, but is
  unwired and unverified and therefore discharges no literal horizon-tail card yet.  The active
  source-only leaf is the missing reciprocal-jet bridge: divided-power reciprocal recursion,
  inversion algebra equivalence and involution, conjugation of direct to inverse currents, and
  identification of the inverse-current kernel with the literal reciprocal-tail field.  This one
  bridge unlocks the deep-meet portions of four projective cards before the separate exact
  depth-one Schwarzian invariant and all-depth join reconstruction leaves.
- root lane: `RatFuncProjectiveNormalForm` now proves that every nonidentity coefficient-fixing
  automorphism of `K(X)` over an algebraically closed field is conjugate to a pure scaling or unit
  translation, and `RatFuncProjectiveCyclicClassification` refines this to identity, nontrivial
  finite cyclic scaling, infinite-order scaling, or unit translation.  The root has additionally
  completed `ExactDifferentialOrderAffine`: fixed-order ADE existence and exact minimal order are
  invariant under every invertible affine precomposition, unconditionally.  Its direct check,
  exact module build, standard-axiom audit, forbidden-token scan, and diff check are green and its
  umbrella import is wired.  `BellCoordinateJacobian` now additionally proves that the universal
  finite Bell-coordinate Jacobian is triangular with diagonal one and determinant exactly one;
  its exact module build and the same audits are green.  `TerminalLinearJacobian`,
  `BellSubstitutionJacobian`, and `TerminalLinearBellJacobian` then prove the exact bordered
  determinant formula, preservation of a lower polynomial Jacobian under Bell substitution, and
  the literal terminal-linear output formula with sign `(-1)^(n+1)` and terminal power
  `X_terminal^(n+1)`.  Their exact builds and standard-axiom/forbidden-token/diff audits are green,
  and all five cascade-foundation imports are wired.  The next root step is connecting iterates of
  a polynomial derivation to this terminal-linear Bell output family.  Source for
  `DerivationBellChain` and `DerivationTerminalLinearJacobian` now supplies that connection through
  the actual signed determinant, field-level nonvanishing theorem, and domain-Jacobian algebraic
  independence endpoint.  `TerminalScaledJacobian` now adds the second exact Bell row reduction:
  arbitrary lower derivatives of a terminal-scaled output cancel by row shear, leaving its terminal
  derivative and the lower Bell Jacobian.  The actual derivation adapter specializes this to
  `C * X^q`, proves the exact factor `(q : R) * C * X^(q-1)`, and exposes the corresponding
  nonvanishing and algebraic-independence capstones.  Its first batched build was cancelled when an
  unrelated external Lean process appeared; the resulting single chain-rule diagnostic was
  repaired from the already-green project proof pattern.  The enlarged three-module source tranche
  remains intentionally unrerun until the next coherent compiler gate.

## Completed compiler queue

The read-only compiler tasks are finished packets, not active implementation workers.  Their task
IDs are retained so implementation agents can recover the complete theorem inventories and proof
DAGs without repeating the audits.

- scalar/Lüroth: `019f7528-57a6-7343-b49f-546e0a8e5ffc`; first leaf is repaired minimal scalar
  differential rank, and the deepest parent is Ritt's normalized coefficient-ratio theorem.
- projective horizon/building: `019f7528-5afd-7e50-a771-b8522143791e`; first shared leaf is the
  multivariate free-coordinate partial-kernel fixed-field theorem.
- log-CY/toric/entire cascade: `019f7528-5e1e-7da1-ac64-cc38fdb06468`.
- bounded relation/ADE/torsion: `019f752c-7d8e-78c3-8e2f-a7a748b0435a`.
- gamma/multiple-gamma/elliptic-gamma: `019f752c-80d8-7d10-8116-7cc302bfea13`.
- quasi-abelian/divisor/Manin/isogeny: `019f752c-84c7-7740-bc50-242ee99e7b4c`.
- constrained-prolate/operator/spectral: `019f752c-8ad5-7983-9bff-99062316842d`.
- Euler/zeta/Bohr/Herglotz: `019f752c-901b-7981-b847-ee0dc41aa6e9`.

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
- [ ] `active-quasi-abelian-facet-palette-necessity` — active-quotient lattice injection and
  `aqaDim ≤ htDim` inventoried; `FiniteShadowCapacity` proves the abstract kernel-to-injectivity
  implication and finite matrix-shadow core, but the paper's proper Abelian-fibration
  finite-capacity theorem is not yet formalized
- [ ] `active-quasi-abelian-palette-exact-ht-dimension-classification` — compact-kernel
  finite-capacity, torusless all-order packet interpolation, `htDim = aqaDim`, and the six-term
  hierarchy inventoried; the current dimension equality theorem takes analytic extraction and
  realization as hypotheses, so it does not discharge the unconditional paper theorem
- [ ] `additive-heat-aperture-shifted-zeta-echo-ladder` — full polyhomogeneous expansion and
  remainder, two-step and closed parity coefficient laws, single-missing-rung equivalence, forward
  functional-equation tail, prime-power peeling, and real Hankel positivity inventoried;
  `HeatApertureEchoLadder`, `HeatApertureEchoTomography`, and `HeatApertureEchoHankel` cover the
  coefficient/value/tomography core, while the Jonquière local expansion and Gaussian
  asymptotic-integration theorem needed for the actual aperture expansion remain missing
- [ ] `additive-heat-aperture-zeta-zero-echo` — positivity and convergence of the quadratic heat
  observable, Fourier/Poisson representation, local polylog expansion, complex Gaussian moment,
  four-term small-aperture expansion, exact zero detector, nonzero tangent, finite part, and
  completed intensity inventoried; the card itself records that the polylog boundary asymptotics
  required for this paper theorem are not yet in the Lean surface
- [ ] `all-depth-compatible-pair-face-differential-matroid` — complete finite-family
  differential-transcendence rank formula, universal cyclic `B/I_d` carrier, arbitrary-coset face
  decomposition, descending relative-independence theorem, and multiplicative specialization
  inventoried; generic gluing/operator/Stanley--Reisner engines exist, but the concrete pair-face
  hierarchy identification, orbit-height and off-star laws, and unconditional rank-refined descent
  remain open exactly as the card records
- [ ] `all-depth-pair-face-signature-completeness` — DA iff all unpushed pair-face residues vanish,
  exact image `Q_d/DA ≃ Comp_d`, simultaneous divisor lifting, multi-telescoping, bottom-charge
  kernel, annihilator/translation spectrum, multiplicative theorem, and rank-three witness
  consequence inventoried; `TelescopeIdeal` formalizes only the Laurent ideal core and
  `PairFacePrivateSector` explicitly omits analytic exact-image realization, while the main theorem
  still depends on an unformalized depth-two completeness base
- [ ] `all-order-multiple-elliptic-gamma-structural-differential-matroid` — all-order localized
  Stanley--Reisner rank formula, exact DA annihilator, constant-coefficient linearity of every
  dependence, uniform nested-star gluing, descending face lifting, multiplicative product rank,
  cube rank, and no-emergent-nonlinearity consequences inventoried; abstract gluing and localized
  row-matroid machinery exist, but the order-one analytic atomicity, concrete hierarchy face
  independence, orbit-height/off-face laws, and simultaneous Galois descent remain unformalized
- [ ] `all-order-multiple-sine-stanley-reisner-differential-matroid` — degree-`N-1`
  Stanley--Reisner annihilator, all-face independence, additive and multiplicative rank formulas,
  and the exact one-face-layer Barnes-to-sine reflection quotient inventoried; generic gluing and
  quotient-rank algebra exist, while actual multiple-sine functions, positive-real double-sine
  defect-coset atomicity, face-orbit hypotheses, and simultaneous parameterized-difference input
  remain missing as the card explicitly records
- [ ] `almost-periodic-autonomous-ade-finite-frequency-law` — minimal separant, regular-chart hull
  cover, sharp `rankₚ Γ(f) ≤ 2n`, divisor-factor bound, and infinite-frequency autonomous-HT
  contrapositive inventoried; `CoveringDimension` now supplies generic dimension lemmas and
  `KolchinFrequencyBudgetPhase` only packages the frequency/dimension identification as an input,
  so Bohr hulls, minimal differential-polynomial theory, analytic implicit uniqueness, sharp chart
  dimension, Pontryagin identification, and Poincaré--Lelong continuity still must be formalized
- [ ] `almost-periodic-implicit-ade-relative-frequency-law` — joint coefficient/solution hull,
  finite regular-sample atlas, finite-dimensional kernel, relative Pontryagin rank, divisor law,
  and coefficient-domain HT contrapositive inventoried; abstract short-exact rank and covering
  dimension cores exist, but current wrapper inputs do not formalize the paper's Bohr-hull,
  separant, analytic fibre-embedding, duality, or divisor arguments
- [ ] `archimedean-relative-prime-cocycle-curvature` — translation-saturated Gamma base,
  nonflattenable prime cocycle, prime-log Gamma coordinates, all-jet coordinates, lattice fixed
  field, finite Stirling separation, full mixed zeta/Gamma-jet independence, and finite
  Gamma-jet annihilator/residual/determinant laws inventoried; Lean currently supplies the
  prime-log independence, simple-pole non-coboundary, Vandermonde/power-sum, and several Gamma
  shift determinant/residual cores, but not the Hardouin--Singer dependence criterion,
  differential-rational fixed-field theorem, or the paper's full mixed projective-boundary result
- [ ] `barnes-differential-source-face-matrix-factorization` — the concrete Barnes source module,
  exact two-periodic face complex, all nonempty-face Tor law, and derived two-degree conservation
  inventoried; `NormalCrossingFaceMatrixFactorization` proves the abstract mutual kernel/image
  equalities and two-periodic exactness, but the special-function module identification and the
  stated Tor computation remain to be formalized
- [ ] `barnes-multiple-gamma-translation-annihilator` — atomic scaled-digamma translates, exact
  pure and differential-translation annihilators, boundary-cylinder module, all-face descent,
  derived face fracture, rank-two reconstruction, mixed-difference threshold, and finite
  translate-product classification inventoried; Lean has the coprime-product ideal backbone,
  orbit-marker localization, rank-two regular-gauge core, normal-crossing factorization, and
  normalized-simplex contraction, while the Barnes analytic identification and concrete
  localized descent complex are still absent
- [ ] `boundary-wedge-uniform-ht-dimension-gap` — two-thickness/nonpurity, explicit
  two-coordinate periodic pencil and `ppDim=2`, intrinsic `htDim=2`, explicit faithful
  four-coordinate separation and its sharp lower bound inventoried; `WedgeFacetLowerBound` and
  `PPMatrixRankFormulaConsequences` already provide the exact uniform faithful and periodic-pencil
  layers, leaving the analytic realization defining intrinsic `htDim` and its equality to two
- [ ] `bounded-relation-log-magnitude-hypertranscendence` — the whole theorem surface is
  Lean-proved: unconditional ADE normalization/balanced survival, bounded-relation and
  private-prime confinement, finite Lindemann--Weierstrass separation, entire/full-support/HT
  assembly for every algebraic unit phase, arbitrary positive superlinear private-prime profile
  realization, and the corrected shifted `B*(n+1)^beta` value/first-/second-difference
  asymptotics (including `1<beta<2`); exact leaf build and capstone axiom audit are green, leaving
  only the serialized umbrella/index/lint gate before Stage 3
- [ ] `charged-scalar-core-fixed-current-torsor` — all five theorem clauses are Lean-proved:
  `StableCoreFunctoriality`, `ScalarLogCurrentReconstruction`, `RatFuncScaleFixedField`,
  `ScalarDifferentialTorsor`, and `ScalarFiniteDifferentialTorsor` cover the fixed
  hypertranscendental current, exact `T=L(q)`, rank-one equation, rational torsor coordinate, full
  derivation-preserving group `Fˣ`, exact finite/infinite holonomy fixed fields, and the finite
  cover group `mu_N(F)`; the exact owning build and combined axiom audit are green, leaving only
  the serialized umbrella/index/lint gate before Stage 3
- [ ] `commutative-d-group-source-boundary-universality` — Theorems A/B and the sharp-kernel
  corollary inventoried; depends on the localized source quotient plus genuine algebraic D-group
  and logarithmic-derivative foundations
- [ ] `complete-scalar-persistent-gauge-reduction` — stable-core reduction to a projective
  transformation, the mutually exclusive `1`, `mu_N`, `G_m`, and `G_a` branches, their exact fixed
  fields, and rank-one Picard--Vessiot torsors inventoried; the projective automorphism and
  scaling-or-unit-translation normal-form classification, multiplicative finite/infinite torsors,
  additive torsor and exact additive fixed field, and generator-order-zero reduction now exist.
  The unrestricted differential Lüroth theorem, stable-intersection restriction argument, exact
  cyclic-closure classification, and single mutually-exclusive four-branch capstone remain
- [ ] `constrained-prolate-arithmetic-dilation-operator-limit` — arithmetic projective and
  trace-norm convergence, vanishing negative spectral mass, Fredholm determinant convergence,
  positive limiting spectrum, and negative-trace prime response inventoried;
  `ArcsineZetaDerivativeSpectrum` proves the exact positive diagonal, summability, and total-mass
  identity, while the weighted PSWF projective convergence and its operator/determinant transfer
  are not yet formalized
- [ ] `constrained-prolate-fixed-mode-spectral-ladder` — one exact root in every consecutive
  leakage gap, `mu_k/d_(k+1) -> theta_k`, adjacent `lambda^8` separation, and limiting Hermite
  contrast eigenvectors inventoried; infinite-diagonal secular existence/uniqueness/interlacing,
  the exact Hermite algebra, and the all-depth two-mode Fuchs model exist, but actual Fuchs
  asymptotics, prolate-to-Hermite convergence, uniform infinite-tail control, the true ratio law,
  and eigenvector convergence remain
- [ ] `constrained-prolate-fourier-parity-floor-separation` — positive and negative floor limits,
  sharp `lambda^(-4)` parity ratio, eventual strict ordering, negative gap, simplicity, and
  eigenvector rate inventoried; `TwoModeFuchsLimit` covers the exact finite Fuchs-model `8/13`,
  `5/13`, ratio, quantified domination, and sharp rescaling, leaving transfer to the true
  infinite-dimensional prolate optimizers, the tail/min--max argument, simplicity, and the stated
  eigenvector rate
- [ ] `constrained-prolate-full-radial-prime-charge-law` — the full finite-aperture raw radial
  von Mangoldt charge and its explicit leakage-normalized limit inventoried; Lean proves the exact
  divisor collapse, summability/sign of the prime series, and equality with the positive arcsine
  spectrum mass, but not the PSWF diagonal limit or the three uniform off-diagonal estimates that
  are required to pass from this scalar to the cofinal charge
- [ ] `constrained-prolate-radial-leakage-divisibility-spectrum` — weak exterior radial-measure
  limit with total mass, diagonal dilation Gram spectrum, off-diagonal disappearance, finite
  divisibility correlations, and diagonal von Mangoldt charge inventoried; existing secular and
  arcsine/divisor modules cover the algebraic consequences, and the newer radial PSWF phase and
  interaction-picture files cover exact ODE infrastructure, while Dunster/Bessel envelope
  asymptotics, oscillatory weak convergence, and simultaneous weighted Gram diagonalization remain
- [ ] `constrained-prolate-two-mode-ground-state` — simple true constrained ground state,
  `O(lambda^(-7))` convergence to the CCM two-mode seed, `8/11` leakage ratio, and `3/11`
  normalized spectral gap inventoried; the concrete operator/signed/constrained spectra, exact
  infinite secular root theory, two-mode value, and Fuchs-model limits exist, leaving mode-number
  identification, true Fuchs and prolate-to-Hermite asymptotics, uniform tail control, and transfer
  of all three headline conclusions to the actual optimizer
- [ ] `differential-variational-building-balance-law` — canonical Ore/Kähler variational module
  and affine-building action, determinant-balanced relative positions, bounded-versus-positive
  linear translation dichotomy with attracting/repelling flags, rank-one collapse, free-field
  reconstruction, and rank-two shear witness inventoried; Lean has the Kähler connection and
  abstract subadditive/conjugacy translation-length kernel, but lacks Ore localization and torsion,
  pseudodifferential skew-field valuation, matrix invariant factors, affine buildings, and their
  exact differential-field instantiation
- [ ] `double-sine-defect-coset-differential-matroid` — exact defect DA criterion, same-coset
  neutrality, distinct-nonzero-coset joint independence, coset-count differential rank, translate
  matroid, and group-algebra operator rank inventoried; genuine differential-matroid/collision and
  gluing infrastructure plus additive orbit balance exist, while the double-sine analytic object,
  incommensurate-cylinder algebra, common fixed-field theorem, simultaneous paired telescoper,
  specialization, and pole-orbit independence proof remain
- [ ] `double-sine-translation-annihilator` — positive-real irrational-period HT, exact
  augmentation-ideal structural annihilator, finite translate-product classification, and
  reflection-induced Barnes rank collapse inventoried; `OrbitBalanceAugmentation` proves only the
  abstract augmentation kernel identity, with the double-sine functional equations, exponential
  cylinder independence, dense-period meromorphic fixed field, paired difference-Galois
  telescoping, specialization, and analytic HT/annihilator reverse inclusion still unformalized
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
- [ ] `gaussian-torsion-language-hypertranscendence` — the shared finite torsion-language
  exactification now handles the integral exponent `β=2`; the active exclusive leaf is the
  remaining infinite Gaussian face to finite tail-lock extraction and controlled truncation
- [ ] `hedenmalm-pair-weil-polarization-law` — theorem/corollary surface inventory pending
- [ ] `helson-universal-ht-arbitrary-divisor-orthogonality` — theorem/corollary surface inventory pending
- [ ] `herglotz-full-translation-ht-krein-index-orthogonality` — theorem/corollary surface inventory pending
- [ ] `ht-period-rank-one-scalar-stanley-reisner-principalization` — theorem/corollary surface inventory pending
- [ ] `ht-tail-no-hair-and-embedded-reconstruction-boundary` — theorem/corollary surface inventory pending
- [x] `hypertranscendental-clock-incompressibility` — formalized in full (Theorems A and B, the
  right inverse, both chain-rule identities, the dynamical corollary and the conductor length);
  card moved to `3-formalized/new_scientific_knowledge/ht/`
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
- [x] `order-three-elliptic-gamma-bottom-face-joint-atomicity` — complete: six-face joint
  atomicity, finite-family degree, and the multiplicative family formalized unconditionally
  (`OrderThreeBottomFaceJointAtomicity.lean`)
- [x] `order-three-elliptic-gamma-full-structural-differential-matroid` — complete: all-order
  structural span decomposition, deep-packet `(face, shift)` faithfulness, and the operator-row
  matroid and rank laws formalized unconditionally
  (`MultipleEllipticGammaStructuralSpanDecomposition.lean`,
  `MultipleEllipticGammaDeepPacketFaithfulness.lean`)
- [x] `order-two-elliptic-gamma-full-structural-differential-matroid` — complete: squarefree
  hierarchy identification, faithful coordinate packet, and the operator-row matroid and rank laws
  formalized unconditionally (`OrderTwoStructuralTranslateDecomposition.lean`,
  `OrderTwoStructuralMatroid.lean`)
- [x] `order-two-multiple-gamma-period-deletion-phase-split` — complete: transverse DA depth, the
  hierarchy relation, and both depth values formalized unconditionally
  (`MultipleEllipticGammaTransverseDADepth.lean`, `OrderTwoPeriodDeletionDADepth.lean`)
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
- [ ] `projective-horizon-depth-two-current-algebra-transition` —
  `ProjectiveHorizonCurrentFixedField` realizes the actual `E_k`, quadratic `F_k`, and `H_k`
  derivations, proves the needed commutators and annihilation propagation, and identifies the
  two-mode `E_0,F_1` fixed field with the full free-translation fixed field and hence the scalar
  field; the card-level exact surface audit and remaining capstones are active
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
- [ ] `split-source-boundary-universality` — exact mixed dependence, simultaneous coboundary
  quotient, fraction-field localization, represented differential matroid, and finite-packet rank
  equality are Lean-complete with standard axioms; serialized umbrella/index/lint gate and Stage-3
  promotion remain
- [ ] `stable-coframe-log-calabi-yau-rigidity` — theorem/corollary surface inventory pending
- [ ] `symmetry-caged-fixed-divisor-full-orbit-freeness` — theorem/corollary surface inventory pending
- [ ] `toric-log-calabi-yau-tail` — theorem/corollary surface inventory pending
- [ ] `torsion-universal-phase-polynomial-magnitude-hypertranscendence` — whole paper theorem and
  deterministic existence corollary are Lean-complete in
  `PolynomialTorsionLanguageDefectLimit`, `PolynomialTorsionLanguageEntireSeries`, and the new
  unit-filled universal phase; exact leaf builds and standard-axiom audits are green, leaving the
  serialized umbrella/index/lint gate and Stage-3 promotion
- [ ] `torusless-quasi-abelian-fixed-factor-all-order-jet-ampleness` — theorem/corollary surface inventory pending
- [ ] `triptic-ht-kummer-content-root-classification` — abstract Kummer group-theoretic core
  exists; the analytic meromorphic/triptic realization and exact DA-kernel identification remain
- [ ] `triptic-orbit-residue-reciprocity` — exact residue/DA/annihilator surfaces inventoried;
  the analytic triptic orbit and residue-reciprocity foundations remain to be implemented
- [ ] `universal-first-order-entire-cascade-unit-cost` — exact differential order and its
  unconditional invariance under invertible affine precomposition are Lean-complete in
  `ExactDifferentialOrderAffine`, and the universal Bell coordinate change has unit Jacobian in
  `BellCoordinateJacobian`; the exact terminal-linear Bell determinant reduction is Lean-complete
  through `TerminalLinearBellJacobian`.  Unverified source in `DerivationBellChain`,
  `TerminalScaledJacobian`, and `DerivationTerminalLinearJacobian` now realizes actual derivation
  iterates, both the terminal-linear and positive-power Bell row reductions, their exact signed
  determinants and nonvanishing forms, and the resulting algebraic independence capstones.  The
  Wiman-place, compatible valuation flag, nested-leading observability induction, Clunie
  state-independence, and Poincare-recession surfaces remain
- [ ] `weighted-euler-tangent-global-graph-decoupling` — theorem/corollary surface inventory pending
