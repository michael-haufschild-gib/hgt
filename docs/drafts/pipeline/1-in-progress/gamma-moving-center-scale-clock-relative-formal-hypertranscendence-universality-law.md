# Gamma moving-center scale-clock relative formal-hypertranscendence universality law

- **ID:** gamma-moving-center-scale-clock-relative-formal-hypertranscendence-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of
  `gammaPoleScaleAndInverseBranchCoefficientRationalEval_injective`,
  `gammaInversePoleClockObservableFormalGerm_formallyHypertranscendental`, and
  generic formal-jet substitution
- **Statement:** The formal germ whose constant coefficient is the reciprocal signed factorial
  pole scale and whose positive coefficients are all nonlinear normalized inverse-Gamma branch
  coefficients satisfies no nonzero finite-order algebraic differential equation even over the
  full moving-center field `ℂ(N)`.

## Goal

Upgrade inverse-Gamma clock observability from fixed complex coefficients to the moving pole
coordinate field while retaining the factorial scale discarded by the original clock germ.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof collision audit found no exact literature match

## Corpus inputs

- `GammaPoleRationalBase`
- `gammaPoleScaleAndInverseBranchCoefficientFamily`
- `gammaPoleScaleAndInverseBranchCoefficientRationalEval`
- `gammaPoleScaleAndInverseBranchCoefficientRationalEval_injective`
- `formalJetsOver`
- `formalJets_substitution_injective`
- `aeval_formalJetsOver_ne_zero_of_coeff_algebraicIndependent`

## Proof

**[PROVED HERE]** First generalize finite formal-jet separation from `ℂ` to any characteristic-zero
field `K`. The proof used in the corpus is field-theoretic: arbitrary finite origin jets are
realized by a Taylor polynomial with coefficients divided by factorials; constant-coefficient
evaluation then forces divisibility by the point variable; iteration forces divisibility beyond
the finite point-degree of any nonzero differential polynomial. Nothing in this argument depends
on completeness or analysis of `ℂ`.

For a `K`-algebra `A`, let `a₀,a₁,…` be algebraically independent over `K`. Apply generic
formal-jet separation to the universal series with coefficients `X₀,X₁,…` over `K`, then map
coefficients by evaluation `Xⱼ ↦ aⱼ`. Algebraic independence makes this evaluation injective, so
no nonzero coefficient of the universal evaluated differential polynomial can disappear. Thus
`Σ aⱼTʲ` is formally hypertranscendental over `K`.

Now take `K = ℂ(N)` and `A = NatGerm`. Injectivity of
`gammaPoleScaleAndInverseBranchCoefficientRationalEval` is exactly algebraic independence over
`K` of the `Option ℕ`-indexed family consisting of the reciprocal signed factorial at `none` and
the inverse-branch coefficient `j` at `some j`. Reindex by the bijective enumeration
`0 ↦ none`, `j+1 ↦ some j`; algebraic independence is preserved. The resulting power series is
therefore formally hypertranscendental over `ℂ(N)` at every finite jet order. No computation is
used. ∎

## Strict gain over corpus endpoints

The original inverse-clock theorem allowed only complex coefficients and omitted pole scale. The
moving-center three-chart atlas proved polynomial coordinate injectivity over `ℂ(N)` but did not
convert it into differential-algebraic nonvanishing. Their closure supplies both upgrades at once:
relative coefficients and a scale-headed all-order clock germ.

## Lean certificate

- Module:
  `GaloisForLFunctions.HTGeometry.GammaMovingCenterScaleClockRelativeFormalHypertranscendenceUniversalityLaw`
- Main theorem:
  `gammaPoleScaleHeadedInverseClockFormalGerm_formallyHypertranscendental_over_ratFunc`
- Generic relative theorem:
  `aeval_formalJetsOver_ne_zero_of_coeff_algebraicIndependent_over`
- Exact-file command:
  `lake env lean GaloisForLFunctions/HTGeometry/GammaMovingCenterScaleClockRelativeFormalHypertranscendenceUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/HTGeometry.lean`.

## Novelty audit

No literature search occurred before dependency-closed paper and Lean proofs. Post-proof searches
for inverse-Gamma branches, Gamma hypertranscendence, moving rational parameter fields, and
formal-series coefficient independence found no exact collision. Closest primary sources:

- B. Adamczewski, T. Dreyfus, and C. Hardouin, *Hypertranscendence and linear difference
  equations*, <https://arxiv.org/abs/1910.01874>, develops hypertranscendence criteria for
  difference equations and discusses Hölder's Gamma theorem, not inverse-pole branch coefficient
  germs over a moving-center field.
- B. Adamczewski, J. P. Bell, and E. Delaygue, *Algebraic independence of G-functions and
  congruences à la Lucas*, <https://arxiv.org/abs/1603.04187>, gives Kolchin-type independence
  methods for G-functions, not a generic formal-jet theorem driven by an arbitrary independent
  coefficient family.
- W. D. Brownawell and M. A. Papanikolas, *Linear independence of Gamma values in positive
  characteristic*, <https://arxiv.org/abs/math/0106054>, treats special values of a function-field
  Gamma function, not characteristic-zero inverse branches or factorial-scale-headed clocks.

## Log

- 2026-07-23 — cross-read of moving-center atlas and inverse-clock terminal modules exposed the
  missing relative formal consequence.
- 2026-07-23 — dependency-closed paper proof completed before literature search or Lean source.
- 2026-07-23 — generic characteristic-zero base-field jet separation and Gamma specialization
  passed exact Lean warning-free; module wired into HTGeometry umbrella.
- 2026-07-23 — post-proof collision audit found no exact literature match.
