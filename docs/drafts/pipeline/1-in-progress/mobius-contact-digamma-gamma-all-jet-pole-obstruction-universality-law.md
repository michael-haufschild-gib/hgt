# Möbius-contact digamma–Gamma all-jet pole-obstruction universality law

- **ID:** mobius-contact-digamma-gamma-all-jet-pole-obstruction-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of `MobiusGammaContactTransgression`,
  `DigammaGammaFactorialBlowUp`, `DigammaGammaLocalHypertranscendence`, and
  `AccumulatingPoleAlgebraicity`
- **Statement:** The finite Möbius contact defect is the all-order factorial microscope for
  `digamma ∘ Gamma`. Every contact-normalized jet converges to the reciprocal digamma boundary;
  the composite is globally hypertranscendental, locally non-differentially-algebraic on every
  nonempty regular open set, and not algebraic over the full meromorphic germ field at any
  negative integer.

## Goal

Push contact normalization through the complete differential and local-meromorphic obstruction
hierarchy of the first logarithmic derivative after Gamma composition.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof collision audit found no exact literature match

## Corpus inputs

- `mobiusGammaContactPartialCharge_eq`
- `iteratedDeriv_digammaGamma_factorialBlowUp_tendsto`
- `hypertranscendental_digamma_comp_Gamma`
- `no_local_differential_relation_digamma_comp_Gamma`
- `ReciprocalGammaPoleBranch.digamma_comp_Gamma_not_locallyMeromorphicallyAlgebraic`
- `chosenReciprocalGammaPoleBranch`

## Proof

**[PROVED HERE]** Let `c_n=(-2-mobiusGammaContactPartialCharge n)/2`. Exact transgression gives
`c_n=reciprocalGammaFactorialScale n`; therefore the contact zoom
`h(-n+c_n x)` is exactly the established factorial blow-up zoom. Substitution in the
all-derivative convergence theorem shows that every order-`j` contact jet of
`digamma(Gamma z)` converges to the corresponding jet of
`digamma((-x)^(-1))`. The corpus’s initial-form descent then supplies global
hypertranscendence and excludes differential-algebraic relations on every nonempty regular open
set. Finally choose the certified reciprocal-Gamma pole branch at each negative integer. Its
satellite poles with nonzero residues accumulate at the center, so the local accumulating-pole
criterion excludes even polynomial relations with arbitrary meromorphic coefficient germs there.
No computation is used. ∎

## Strict gain over corpus endpoints

Contact normalization had reached Gamma-iterate jets but not the logarithmic-derivative
composition or meromorphic coefficient fields. The digamma–Gamma endpoints used an internal
factorial scale and were split across global, local differential, and local meromorphic modules.
This closure identifies one arithmetic boundary observable as the common microscope behind all
four obstruction levels.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.MobiusContactDigammaGammaAllJetPoleObstructionUniversalityLaw`
- Main theorem:
  `mobiusContactDigammaGamma_completeAllJetPoleObstructionUniversality`
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/MobiusContactDigammaGammaAllJetPoleObstructionUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

No literature search occurred before dependency-closed paper and Lean proofs. Post-proof searches
for `digamma ∘ Gamma`, compositional hypertranscendence, inverse-Gamma satellite poles, and local
meromorphic algebraicity found no exact collision. Closest primary sources:

- Z. Mijajlovic and B. Malešević, *Analytical and differential-algebraic properties of Gamma
  function*, <https://arxiv.org/abs/math/0605430>, studies differential-algebraic properties of
  Gamma and related functions, not the composite `digamma ∘ Gamma` or its pole clusters.
- B. Adamczewski, T. Dreyfus, and C. Hardouin, *Hypertranscendence and linear difference
  equations*, <https://arxiv.org/abs/1910.01874>, treats solutions of linear difference equations,
  not this nonlinear composition or meromorphic-germ obstruction.
- J. Huang and T. W. Ng, *Hypertranscendency of Perturbations of Hypertranscendental Functions*,
  <https://arxiv.org/abs/2007.10037>, provides composition criteria in a different setting but no
  contact-normalized all-jet limit or accumulating inverse-Gamma pole theorem.

## Log

- 2026-07-23 — composition and accumulating-pole scan exposed complete digamma–Gamma obstruction.
- 2026-07-23 — dependency-closed proof completed.
- 2026-07-23 — exact Lean proof passed warning-free and module wired into RHTower umbrella.
- 2026-07-23 — post-proof collision audit found no exact literature match.
