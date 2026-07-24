# Nevanlinna locally-finite/maximal-separation ergodic-frame phase universality law

- **ID:** nevanlinna-locally-finite-maximal-separation-ergodic-frame-phase-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of
  `nevLeaf_compactRestriction_eq_finiteDenominatorSection`,
  `exists_momentIdentical_pairwiseMaximalTotalVariation_family`, and
  `nevBauer_ergodicExtreme_infiniteSupportFrame_phase`
- **Statement:** For every normalized bounded-kernel Hamburger moment problem, canonical real
  Nevanlinna leaves form a locally finite-on-compacts, ergodic/extreme, pairwise mutually singular
  phase with maximal total-variation separation. Infinite-support projective mixtures form the
  complementary nonergodic/nonextreme phase, but retain infinite carrier support and complete-frame
  identifiability.

## Goal

Join local support geometry, global convex/dynamical phase, metric separation, and reconstruction
for the same canonical Nevanlinna boundary family.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof collision audit found no exact literature match

## Corpus inputs

- `nevLeaf_compactRestriction_eq_finiteDenominatorSection`
- `nevExtremalFamily_leaf`
- `NevanlinnaBoundaryFamily.barycenter_dirac`
- `NevanlinnaBoundaryFamily.barycenter_isErgodicConstraintStationaryLaw_iff_dirac`
- `nevBauer_extreme_iff`
- `mutuallySingular_leaf`
- `totalVariation_univ_eq_of_isProbability`
- `nevBauer_ergodicExtreme_infiniteSupportFrame_phase`

## Proof

**[PROVED HERE]** Fix a normalized positive moment form with bounded kernel and let `F` be its
canonical boundary family. For each real parameter `t`, barycentring the projective Dirac law at
`t` gives `F.leaf(t)`, definitionally the constructed `nevLeaf(t)`. The Dirac characterization of
stationary ergodicity and the Bauer extreme-point characterization therefore make this carrier both
ergodic and extreme.

For every compact real observation window `K`, the finite-denominator-fibre theorem supplies a
finite `A ⊆ K` on which restriction of `nevLeaf(t)` is already exact. Thus every pure real leaf is
locally finite on compacts. For distinct real parameters `t,u`, their denominator fibres are
disjoint and measurable, so the corresponding probability leaves are mutually singular. The
total variation of their signed difference on the whole line is therefore exactly two.

Now take an infinite-support projective parameter law. The existing ergodic/extreme/frame phase
theorem says its barycentric carrier has infinite real support, is neither stationary-ergodic nor
extreme, and its complete inverse-Cholesky frame tower uniquely recovers the parameter law among
all infinite-support laws.

Hence pure real leaves and infinite-support mixtures occupy sharply different local-support,
ergodic, convex, and metric phases, while the mixed phase remains globally identifiable. No
computation is used. ∎

## Strict gain over corpus endpoints

Local-finite extremality did not compare distinct leaves or classify infinite-support mixtures.
Maximal-total-variation indeterminacy did not identify its leaf family with the canonical Bauer
ergodic phase or record compact-local finiteness. The ergodic/frame theorem did not state local
finite tomography or maximal pairwise separation of pure leaves. The closure gives one canonical
two-phase law.

## Lean certificate

- Module:
  `GaloisForLFunctions.HTGeometry.NevanlinnaLocallyFiniteMaximalSeparationErgodicFramePhaseUniversalityLaw`
- Main theorem:
  `nevanlinna_locallyFiniteMaximalSeparation_ergodicFramePhaseUniversality`
- Exact-file command:
  `lake env lean GaloisForLFunctions/HTGeometry/NevanlinnaLocallyFiniteMaximalSeparationErgodicFramePhaseUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/HTGeometry.lean`.

## Novelty audit

No literature search occurred before dependency-closed paper and Lean proofs. Post-proof searches
for N-extremal Hamburger measures, local finiteness, mutual singularity and total variation,
Bauer/ergodic phase classification, infinite-support barycenters, and frame reconstruction found no
exact collision. Closest primary sources:

- C. Berg and R. Szwarc, *Special N-extremal solutions to indeterminate moment problems*,
  <https://arxiv.org/abs/2603.26302>, studies determinacy after weighted modification of
  N-extremal measures, not the two-phase local-support/ergodic/TV/frame classification.
- F. Štampach and P. Šťovíček, *The Nevanlinna parametrization for q-Lommel polynomials in the
  indeterminate case*, <https://arxiv.org/abs/1407.0217>, explicitly describes N-extremal
  measures for one moment sequence, without infinite-support mixture ergodicity or canonical-frame
  recovery.
- S. M. Zagorodnyuk, *The Nevanlinna-type parametrization for the operator Hamburger moment
  problem*, <https://arxiv.org/abs/1605.03217>, constructs an operator-valued parametrization, not
  compact-local finite tomography and maximal total-variation separation of pure leaves.
- M. Nedic and E. Saksman, *On the structure of Nevanlinna measures*,
  <https://arxiv.org/abs/2201.01039>, studies Herglotz--Nevanlinna representing measures and
  extremal support geometry in several variables, not this Hamburger boundary Bauer phase law.

## Log

- 2026-07-23 — terminal cluster scan identified three endpoint laws acting on the same canonical
  Nevanlinna boundary family but exposing disjoint phase coordinates.
- 2026-07-23 — dependency-closed paper proof completed before literature search or Lean source.
- 2026-07-23 — exact Lean proof passed warning-free and module wired into HTGeometry umbrella.
- 2026-07-23 — post-proof collision audit found no exact literature match.
