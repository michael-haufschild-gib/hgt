# nsk/other stage-3 sweep — state after 2026-08-16

Goal: promote every card in `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other`
to stage 3 with unconditional Lean.  **32 cards remain (26 non-ccm).**

Ledgers to tick on a promotion: this memory,
`nsk-other/session-2026-08-16-celestial-and-principal-symbol` (module details), and the on-disk
card `docs/drafts/pipeline/1-in-progress/other-stage3-closure-ledger.md`.

**The six `ccm-*` cards in that folder belong to a concurrently running CCM agent** (it writes its
certificates into `3-formalized/new_scientific_knowledge/ccm/`).  Leave them alone.

## Closed on 2026-08-16 (4)

1. `scalar-ht-horizon-celestial-sphere` — `HTGeometry/ProjectiveHorizonCelestialSphere.lean`,
   `HTGeometry/HyperbolicThreeSpaceBoundary.lean`, `HTGeometry/ScalarHorizonCelestialBoundary.lean`.
2. `nonlinear-rational-observation-curve-horizon-reconstruction` —
   `HTGeometry/JetPrincipalSymbolExtraction.lean`, `HTGeometry/DerivationAlgebraicDescent.lean`,
   `HTGeometry/RationalObservationCurveNormalization.lean`.
3. `toric-log-calabi-yau-tail` — `HTGeometry/ToricIsogenyTailLaw.lean`.
4. `eigenplurivolume-log-crepant-orbifold` — `HTGeometry/EigenPluriVolumeLogCrepant.lean`.

Method that worked for 3 and 4: **the corpus already owned almost everything**.  Before writing any
Lean, grep the corpus for the nearest sibling theorem and check whether the card's statement is a
specialization (autonomous case of a protocol, weight-`k` case of weight one, …).  `toric` needed
only the constant-protocol bridge; `eigenplurivolume` needed only `ord (J^k) = k · ord J`.

## Why the remaining 26 are slow — blocker per card

- **Casale/Malgrange classification of rational maps of `P¹` with a nonconstant rational
  differential invariant** (power / Chebyshev / Lattès): blocks
  `rational-coarse-graining-orbifold-tail-classification` (its step 2 is exactly Casale),
  `floquet-orbifold-tail-emergence`, `orbifold-tail-holographic-reconstruction`.
  Possible attack route: the corpus already owns `HTGeometry/LieCartanFormalVectorFields.lean`
  (`IsVfSubalgebra`, order filtration lemmas) — Lie's classification of finite-dimensional
  transitive subalgebras of formal vector fields on a line is the Lie-theoretic core of the
  groupoid classification.  Everything else on those cards is already Lean
  (`OrbifoldCurrentTailInclusion.lean` has the whole "if" direction).
- **Kolchin topology / differential algebraic groups / DCF model theory**:
  `abelian-multiplication-tail-manin-horizon`, `embedded-manin-horizon-isogeny-reconstruction`,
  `jet-horizon-translation-gauge-classification` (needs a differentially closed field layer).
- **Algebraic-group scheme representability**: `isogeny-tail-maurer-cartan-holography`.  A huge
  scaffolding already exists (see its Lean-status section: 20+ modules); what is left is
  theorem-specific representability and differential genericity.
- **Complex/quasi-Abelian geometry**: `active-quasi-abelian-palette-…`,
  `torusless-quasi-abelian-fixed-factor-…`, and the Siegel bound
  `trdeg_C M(C^n/Λ) ≤ n` for `noncompact-period-quotient-facet-escape-law`.
- **Bohr almost-periodic function theory / frequency modules**: the two `almost-periodic-*` cards.
- **Difference-Galois (Dreyfus) classification**: `bessel-order-intensity-hypertranscendence`.
- **Ore localization of rings of differential operators + affine buildings**:
  `differential-variational-building-balance-law`.
- **Gamma-product asymptotics in vertical strips / transseries model of `K_E`**:
  `finite-archimedean-gamma-product-boundary-law`, `archimedean-relative-prime-cocycle-curvature`.
- **Infinite products, Euler sine product, zeta values**:
  `prime-completion-annihilates-hypertranscendence-at-even-temperature`.
- **Elliptic-gamma differential matroids at all depth**:
  `all-depth-compatible-pair-face-differential-matroid`,
  `all-depth-pair-face-signature-completeness`, `irrational-triptic-source-effectivity-character`.
- **Analytic number theory / operator theory**: `prime-valuation-dyadic-fermion-normal-cone-law`,
  `prime-wold-accelerated-type-modular-drift-law`,
  `prime-modulated-weyl-idealizer-collapse-on-xi-sampling` (needs smooth jet interpolation,
  a superlinear aperiodicity lemma, and an unconditional infinite-critical-line-zeros input).
- **Named concrete open core, proof plan already written**:
  `gauss-component-quasi-inner-residue-hierarchy`.  Its only missing Lean is core **(T)** for
  `m ≥ 2`, and the tail of the card contains a complete band-split proof plan
  (`J = ⌊n/4⌋`, finite Parseval, `norm_gaussSampleRatio_pow_le`, kernel bound `C/(1+|l-j|)`).
  Existing lane: `RHTower/GaussPrincipalStepBlock.lean`, `GaussSampleTranslationL2.lean`,
  `GaussRatioWeightedDefect.lean`, `GaussUniformTranslationL2.lean`, `GaussDiagonalLogResidue.lean`.
  **This is the most concretely specified remaining target.**
- **Large active card**: `universal-first-order-entire-cascade-unit-cost` (653 KB work log; the
  frontier is item 2' instantiation and item 3 assembly — see
  `nsk-other/stage3-sweep-ledger-2026-08-13`).
