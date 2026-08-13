# new_scientific_knowledge/other stage-3 sweep — ledger

Goal (session-scoped stop hook): every card in
`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/` fully formalized
unconditionally in Lean and moved to stage 3. 65 cards at start; 53 remain.

Promotion procedure (executed for Phase A, keep using):
1. verify card's Lean modules exist + umbrella-reachable (transitive import OK);
2. one batched foreground `lake build <mod1> <mod2> …` (26 modules → green, 10512 jobs);
3. `#print axioms` scratch via `lake env lean` on capstones → must be ⊆ {propext, Classical.choice, Quot.sound};
4. sed Stage line `2-fully-proven` → `3-formalized` (qualifiers kept);
5. `git mv` card → `3-formalized/new_scientific_knowledge/other/`;
6. if certificate `<name>.md` already occupies that name there, `git mv` cert → `<name>-formalized.md`;
7. fix links: certs' `Paper proof:` old `../../2-fully-proven/nsk/other/X.md` → `other/X.md` (certs in nsk/) or `X.md` (certs in nsk/other/); moved cards' `../../3-formalized/new_scientific_knowledge/` → `../`.
Namespaces vary per module: check `grep '^namespace'` before #print axioms
(some use GaloisForLFunctions, some GaloisForLFunctions.HTGeometry, some RHTower).
`formal lint passed` repo-wide on 2026-08-13.

## DONE (moved to stage 3, 2026-08-13)
bounded-relation-log-magnitude-hypertranscendence, charged-scalar-core-fixed-current-torsor,
double-sine-defect-coset-differential-matroid, gaussian-torsion-language-hypertranscendence,
torsion-universal-phase-polynomial-magnitude-hypertranscendence, complete-scalar-persistent-gauge-reduction,
coordinate-intrinsic-fusion-kolchin-principal-filter-law, route-c2-zero-safe-current-multiplicity-tomography,
scalar-differential-inversive-core-projective-law, von-mangoldt-toeplitz-countertrace-regularity-no-go,
nonreal-factorial-slope-formal-hypertranscendence, double-sine-translation-annihilator
(all: build green, capstone axioms clean; open boxes on cards are 3→4/novelty-audit only;
double-sine-translation-annihilator's unchecked "Barnes reflection" box is an off-critical-path
independent asset, main capstone daTranslationAnnihilator_doubleSine_imaginaryRay closed).

## Tranche 2 — certificate exists at stage 3, gate not closed on paper card (verify then promote)
- [ ] barnes-differential-source-face-matrix-factorization (cert s3/other; stage says exact theorem Lean-formalized)
- [ ] split-source-boundary-universality (cert s3; stage: Lean-proved / final integration gate pending)
- [ ] primitive-fibre-modular-renormalization-law (cert s3)
- [ ] von-mangoldt-bivariate-marginal-trace-lock-no-go (cert s3 top-level)
- [ ] wold-sieve-normal-cone-von-mangoldt-current (cert s3)
- [ ] ramsey-weyl-causal-phase-law (cert s3 top-level; cert status "unconditional algebraic and phase-germ core" — check completeness vs card)
- [ ] shift-one-seam-power64-cassini-jensen (cert s3)
- [ ] theta-cusp-calibrated-power-reciprocal-first-moment-law (cert s3 top-level)
- [ ] boundary-wedge-uniform-ht-dimension-gap (cert s3)
- [ ] projective-prime-weyl-leakage-fock-normal-cone (stage: Lean-proved, external novelty audit preliminary — no cert found yet, check)
- [ ] prime-tail-reflection-folded-second-order-resolvent (stage: Lean-proved)

## Tranche 3 — cards documenting partial/unknown Lean (read each, close gaps)
all-depth-pair-face-signature-completeness, all-order-multiple-sine-stanley-reisner-differential-matroid,
gauss-component-quasi-inner-residue-hierarchy, all-depth-compatible-pair-face-differential-matroid
(explicitly: unconditional Lean proof OPEN), irrational-triptic-source-effectivity-character (3 open lean boxes),
bessel-order-intensity-hypertranscendence (2 open), prime-valuation-dyadic-fermion-normal-cone-law,
finite-archimedean-gamma-product-boundary-law, active-quasi-abelian-palette-exact-ht-dimension-classification,
almost-periodic-autonomous-ade-finite-frequency-law, almost-periodic-implicit-ade-relative-frequency-law,
archimedean-relative-prime-cocycle-curvature, critical-half-density-prime-tail-resolvent-law,
noncompact-period-quotient-facet-escape-law, periodic-pencil-intrinsic-ht-dimension-two,
prime-wold-accelerated-type-modular-drift-law, torusless-quasi-abelian-fixed-factor-all-order-jet-ampleness,
universal-first-order-entire-cascade-unit-cost, fixed-divisor-full-complex-translation-freeness,
prescribed-gap-process-order-one-maximal-ht-profield, symmetry-caged-fixed-divisor-full-orbit-freeness,
abelian-multiplication-tail-manin-horizon, eigenplurivolume-log-crepant-orbifold,
embedded-manin-horizon-isogeny-reconstruction, isogeny-tail-maurer-cartan-holography,
prime-completion-annihilates-hypertranscendence-at-even-temperature,
rational-coarse-graining-orbifold-tail-classification, toric-log-calabi-yau-tail,
additive-heat-aperture-shifted-zeta-echo-ladder, power-canonical-product-exact-moment-borel-lattice-law,
prime-occupation-polarized-gamma-phase-survival, prime-tail-hedenmalm-wiener-hopf-transgression

## Tranche 4 — no Lean signal (likely full formalization needed)
additive-heat-aperture-zeta-zero-echo, prime-euler-unit-tangent-completeness,
differential-variational-building-balance-law, floquet-orbifold-tail-emergence,
jet-horizon-translation-gauge-classification, nonlinear-rational-observation-curve-horizon-reconstruction,
orbifold-tail-holographic-reconstruction, scalar-ht-horizon-celestial-sphere,
prime-modulated-weyl-idealizer-collapse-on-xi-sampling, weighted-euler-tangent-global-graph-decoupling

## Session log
- 2026-08-13: ledger created; Phase A (12 cards) audited and promoted; links reconciled; 53 remain.
