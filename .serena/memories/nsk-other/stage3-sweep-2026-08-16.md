# nsk/other stage-3 sweep — state after 2026-08-16 (second pass)

Goal: promote every card in `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other`
to stage 3 with unconditional Lean.  **32 cards remain (26 non-ccm).**

Ledgers to tick on a promotion: this memory, the per-card memories below, and the on-disk card
`docs/drafts/pipeline/1-in-progress/other-stage3-closure-ledger.md`.

**The six `ccm-*` cards belong to a concurrently running CCM agent.**  Leave them alone.

## Closed on 2026-08-16 (4)

1. `scalar-ht-horizon-celestial-sphere`
2. `nonlinear-rational-observation-curve-horizon-reconstruction`
3. `toric-log-calabi-yau-tail`
4. `eigenplurivolume-log-crepant-orbifold`

Method that worked: **the corpus already owned almost everything**.  Before writing Lean, grep for
the nearest sibling theorem and check whether the card's statement is a specialization.

## Advanced substantially on 2026-08-16 (not closed)

- `rational-coarse-graining-orbifold-tail-classification` — see
  `nsk-other/orbifold-substitution-endomorphism-2026-08-16`.  The Casale-free route is now Lean
  down to a single classical statement.  ORDER ONE IS CLOSED; in general a nonconstant finite-order
  eigenvector of `Phi_R` forces **either** an invariant `k`-differential with `k != 0` and nonzero
  eigenvalue **or** an invariant affine structure at some jet level `≥ 2`
  (`exists_nonzero_isInvariantDifferential_or_hasNormalizingShift`).  So the Casale blocker for
  this card and for `floquet-orbifold-tail-emergence`,
  `orbifold-tail-holographic-reconstruction` is now: *a rational map of degree ≥ 2 preserving a
  rational affine connection on P¹ is exceptional*.
- `gauss-component-quasi-inner-residue-hierarchy` — see `nsk-other/gauss-core-T-closed-2026-08-16`.
  `(T)` is proved, and now for the whole piecewise-exponential symbol algebra.  Only the relative
  `m`-fold telescope remains, and it needs a two-piece invariant amplitude class (recorded).

## Why the remaining 26 are slow — blocker per card

- **Rational affine connections / Casale-type classification**:
  `rational-coarse-graining-orbifold-tail-classification`, `floquet-orbifold-tail-emergence`,
  `orbifold-tail-holographic-reconstruction` (see above — much sharper now).
- **Kolchin topology / differential algebraic groups / DCF model theory**:
  `abelian-multiplication-tail-manin-horizon`, `embedded-manin-horizon-isogeny-reconstruction`,
  `jet-horizon-translation-gauge-classification`.
- **Algebraic-group scheme representability**: `isogeny-tail-maurer-cartan-holography`.
- **Complex/quasi-Abelian geometry**: `active-quasi-abelian-palette-…`,
  `torusless-quasi-abelian-fixed-factor-…`, and the Siegel bound for
  `noncompact-period-quotient-facet-escape-law`.
- **Bohr almost-periodic function theory**: the two `almost-periodic-*` cards.
- **Difference-Galois (Dreyfus)**: `bessel-order-intensity-hypertranscendence`.
- **Ore localization + affine buildings**: `differential-variational-building-balance-law`.
- **Gamma-product asymptotics / transseries model of `K_E`**:
  `finite-archimedean-gamma-product-boundary-law`, `archimedean-relative-prime-cocycle-curvature`.
- **Infinite products, Euler sine product, zeta values**:
  `prime-completion-annihilates-hypertranscendence-at-even-temperature`.
- **Elliptic-gamma differential matroids at all depth**:
  `all-depth-compatible-pair-face-differential-matroid`,
  `all-depth-pair-face-signature-completeness`, `irrational-triptic-source-effectivity-character`.
- **Analytic number theory / operator theory**: `prime-valuation-dyadic-fermion-normal-cone-law`,
  `prime-wold-accelerated-type-modular-drift-law`,
  `prime-modulated-weyl-idealizer-collapse-on-xi-sampling` (Theorem A is fully Lean; the Xi
  application needs Selberg's positive-proportion theorem and Bochner–Schwartz).
- **Large active card with a fully designed remaining programme**:
  `universal-first-order-entire-cascade-unit-cost` — items A2–A5 in
  `nsk-other/cascade-card-frontier-2026-08-13`.  This is the most mechanically specified target
  left; next concrete module is `AlgebraicBorderShape.lean` (A2).
