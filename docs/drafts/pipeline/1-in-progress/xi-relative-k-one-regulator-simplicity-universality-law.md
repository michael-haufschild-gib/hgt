# Xi relative-K1 regulator simplicity universality law

- **ID:** xi-relative-k-one-regulator-simplicity-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of `xiLocalJordanNormal_iff_multiplicity_one`,
  `localDivisorJetInfinitesimalUnit_eq_one_iff`,
  `localDivisorJetLogUnit_eq_zero_iff`, and
  `xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate`
- **Statement:** At every Xi divisor support point, local Hedenmalm Jordan normality, triviality
  of the canonical infinitesimal relative-`K₁` unit, and vanishing of its finite logarithmic
  regulator are equivalent. Globally, either relative-`K₁` condition is equivalent to Xi
  simplicity and hence to the complete eight-chart Hedenmalm simplicity certificate.

## Goal

Identify whether the relative local-divisor algebra retains exactly the same multiplicity datum
as the analytic, Hilbert-space, Jordan, Bezoutian, continuation, and theta-source simplicity
charts.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof collision audit found no exact literature match

## Corpus inputs

- `xiSupportMultiplicity_pos`
- `xiLocalJordanNormal_iff_multiplicity_one`
- `all_xiLocalJordanNormal_iff_simple`
- `localDivisorJetInfinitesimalUnit_eq_one_iff`
- `localDivisorJetLogUnit_eq_zero_iff`
- `xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate`

## Proof

**[PROVED HERE]** Fix a divisor support point `ρ` and write
`m = xiSupportMultiplicity ρ`. Support positivity gives `m > 0`. The local Hedenmalm Jordan
classification says that its canonical Jordan block is normal exactly when `m = 1`. The
relative-`K₁` classification says that the canonical unit `1+X` in `ℂ[X]/(X^m)` is trivial
exactly when `m = 1`; the characteristic-zero truncated logarithmic regulator classification says
that `log(1+X)` vanishes exactly under the same condition. Chaining the three biconditionals gives
the pointwise law.

Quantifying over all support points identifies either relative-algebra condition with normality of
every local Jordan block, hence with global Xi simplicity. The already-proved Hedenmalm
universality theorem then identifies this same condition with its complete eight-chart
certificate. No computation is used. ∎

## Strict gain over corpus endpoints

The Hedenmalm universality certificate did not contain any relative algebraic-`K₁` or logarithmic
regulator chart. The local-divisor relative-`K₁` module only gave right-half RH implications after
adding a ladder hypothesis. This closure gives an unconditional pointwise classification and a
global equivalence, showing that relative unit and regulator data are neither weaker nor stronger
than the entire existing simplicity certificate.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.XiRelativeKOneRegulatorSimplicityUniversalityLaw`
- Main theorem:
  `xiSimplicity_completeRelativeKOneRegulatorUniversality`
- Pointwise theorem:
  `xiLocalJordanNormal_iff_relativeKOneTrivial_and_logRegulatorVanishing`
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/XiRelativeKOneRegulatorSimplicityUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

No literature search occurred before dependency-closed paper and Lean proofs. Post-proof searches
for relative `K₁` of truncated polynomial rings, nilpotent logarithms, Jordan normality, and zero
multiplicity found no exact collision. Closest primary sources:

- L. Hesselholt, *The tower of K-theory of truncated polynomial algebras*,
  <https://arxiv.org/abs/math/0702877>, computes maps between relative higher `K`-groups of
  truncated polynomial algebras in finite characteristic, not a complex-divisor simplicity
  classifier or a Jordan/regulator equivalence.
- V. Angeltveit, T. Gerhardt, M. A. Hill, and A. Lindenstrauss, *On the algebraic K-theory of
  truncated polynomial algebras in several variables*, <https://arxiv.org/abs/1206.0247>,
  computes algebraic `K`-theory via cyclotomic methods, not the canonical `1+X` class attached to
  analytic zero multiplicity.
- R. Horiuchi, *Verschiebung maps among K-groups of truncated polynomial algebras*,
  <https://arxiv.org/abs/1712.03189>, studies functorial maps between relative `K`-groups, with no
  Hedenmalm, Xi-divisor, Jordan-normality, or logarithmic-regulator phase law.

## Log

- 2026-07-23 — local divisor-jet/Hedenmalm terminal scan exposed the relative-`K₁` closure.
- 2026-07-23 — dependency-closed paper proof completed before literature search or Lean source.
- 2026-07-23 — exact Lean proof passed warning-free and module wired into RHTower umbrella.
- 2026-07-23 — post-proof collision audit found no exact literature match.
