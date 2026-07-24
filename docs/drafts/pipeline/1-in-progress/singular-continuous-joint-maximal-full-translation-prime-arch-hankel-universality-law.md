# Singular-continuous joint maximal/full-translation prime--arch Hankel universality law

- **ID:** singular-continuous-joint-maximal-full-translation-prime-arch-hankel-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of
  `singularContinuousCarrier_maximalTranslation_cauchyHerglotzFreeness_denseResidual`,
  `singularContinuousFullTranslation_primeArchHankelUniversality`, and residual-filter
  intersection
- **Statement:** On the common positive Nevanlinna chart, the maximal intrinsic-translation
  Cauchy--Herglotz phase and the complete finite translated-family phase have a dense residual
  intersection. Every carrier in that joint phase is simultaneously singular-continuous,
  maximally translation free, relation-free for every finite family of distinct translates,
  globally Cauchy--Herglotz hypertranscendental, and a strict Hamburger Hankel ray whose
  prime--archimedean adjoining cone carries the exact RH, Sonin, reconstruction, and Hedenmalm
  classifiers.

## Goal

Intersect two independently established residual phases that live on the same carrier chart and
retain all analytic and spectral conclusions on one witness rather than on separately chosen
generic carriers.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof collision audit found no exact literature match

## Corpus inputs

- `singularContinuousCarrier_maximalTranslation_cauchyHerglotzFreeness_denseResidual`
- `singularContinuousFullTranslation_primeArchHankelUniversality`
- `Filter.inter_mem`
- `dense_of_mem_residual`

## Proof

**[PROVED HERE]** Fix the Nevanlinna carrier family and all hypotheses common to the two source
theorems. Both theorems use the same reference probability measure, frozen continuous jet
control, kernel `S`, and open unit ball `positiveChart`.

Let `maximalPhase` be the intersection of:

1. coefficient-rigidity for every finite differential pattern on the intrinsic one-shift
   palette; and
2. failure of every upper-half-plane differential-algebraic relation for the weighted Cauchy
   transform.

Let `fullPhase` be coefficient-rigidity for every finite differential pattern on the countable
shift palette. The first source theorem proves `maximalPhase` residual. The second proves
`fullPhase` residual. The residual filter is closed under finite intersection, hence

`jointPhase = maximalPhase ∩ fullPhase`

is residual. The positive chart is a nonempty open subset of the closed kernel of a continuous
linear map on a complete `L∞` space, so it is Baire; every residual subset is therefore dense.

For `w ∈ jointPhase`, apply both source theorems to the same density
`1 + w` and the same weighted boundary carrier. Membership in `maximalPhase` yields intrinsic
maximal translation differential freeness and local Cauchy/Herglotz relation-freeness.
Membership in `fullPhase` yields absence of every mixed differential relation among every finite
family of distinct translated Cauchy transforms and translated normalized Herglotz
presentations, plus global hypertranscendence of both presentations. The structural conclusions
give one atomless singular probability measure with Hamburger moments `s`; its moment Hankel
matrices are positive definite at every finite depth with positive determinants.

Finally, the strict moment ray `s` is the same ray used by the prime--archimedean adjoining
theorem in the second source law. Its four exact classifiers therefore remain attached to every
carrier in the joint residual phase:

- RH iff the `s`-adjoined prime--archimedean cone is strict;
- that cone iff exact source-moment reconstruction;
- that cone iff all nondegenerate Sonin determinant collars; and
- that cone together with Xi-zero simplicity iff the Hedenmalm RH-and-simplicity certificate.

No computation is used. ∎

## Strict gain over corpus endpoints

The maximal-freeness theorem did not attach its generic carriers to any prime--archimedean,
Sonin, or Xi classifier and did not supply simultaneous mixed relation-freeness for every finite
translated family. The prime--archimedean theorem used a different residual phase and did not
assert intrinsic maximal translation freeness or upper-half-plane Cauchy relation-freeness on
its carrier. Residual intersection proves all conclusions for the same density and carrier.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.SingularContinuousJointMaximalFullTranslationPrimeArchHankelUniversalityLaw`
- Main theorem:
  `singularContinuous_jointMaximalFullTranslation_primeArchHankelUniversality`
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/SingularContinuousJointMaximalFullTranslationPrimeArchHankelUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

No literature search occurred before dependency-closed paper and Lean proofs. Post-proof searches
for generic singular-continuous measures, residual Herglotz/Cauchy-transform freeness, Hamburger
Hankel positivity, Sonin spaces, and RH positivity classifiers found no exact collision. Closest
primary sources:

- D. Lenz and P. Stollmann,
  *Generic sets in spaces of measures and generic singular continuous spectrum for Delone
  Hamiltonians*, <https://arxiv.org/abs/math-ph/0410021>, proves generic
  singular-continuity in spaces of measures, not differential freeness of translated
  Cauchy--Herglotz families or an RH classifier.
- H. Choi and F. Jafari,
  *Positive definite Hankel matrix completions and Hamburger moment completions*,
  <https://arxiv.org/abs/1509.06296>, studies positive-definite Hamburger completions, not a
  residual Nevanlinna carrier phase or prime--archimedean adjoining law.
- A. Connes and C. Consani, *The scaling Hamiltonian*,
  <https://arxiv.org/abs/1910.14368>, discusses Sonine spaces and Weil positivity for RH, not
  residual singular-continuous Hamburger carriers with simultaneous differential-freeness
  regimes.
- H. Bellemare, Y. Langlois, and T. Ransford,
  *A positivity conjecture related to the Riemann zeta function*,
  <https://arxiv.org/abs/2011.02847>, studies positivity observed in a matrix attached to the
  Nyman--Báez-Duarte criterion, not strict moment-Hankel adjoining cones.

## Log

- 2026-07-23 — fresh cross-folder terminal scan exposed two distinct residual phases on the same
  positive Nevanlinna chart.
- 2026-07-23 — dependency-closed paper proof completed before literature search or Lean source.
- 2026-07-23 — exact Lean proof passed warning-free and module wired into RHTower umbrella.
- 2026-07-23 — post-proof collision audit found no exact literature match.
