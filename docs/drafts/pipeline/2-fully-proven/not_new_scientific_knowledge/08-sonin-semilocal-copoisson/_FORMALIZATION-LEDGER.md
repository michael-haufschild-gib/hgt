# 08-sonin-semilocal-copoisson — stage-2 → stage-3 formalization ledger

Goal: formalize unconditionally in Lean every proven theorem of every card in this folder, add the
missing infrastructure, then move each card to
`docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/08-sonin-semilocal-copoisson/`.

Rules in force: no added hypotheses standing for analytic inputs, no axioms, no `sorry`;
never full builds / umbrella builds (`lake env lean <file>` to check, `lake build <module>` only for
the oleans an `#print axioms` scratch needs); search the corpus before building anything.

## Card triage (17 cards)

| # | card | state | notes |
|---|---|---|---|
| 1 | archimedean-prolate-jacobi-limit-circle-transition | TODO | needs discrete limit-circle theory; card's λ=0 exponents are wrong (see below) |
| 2 | boolean-sonin-full-history-mate-fracture-law | TODO | |
| 3 | connes-semilocal-finite-part-orbital-source-class | TODO | |
| 4 | finite-euler-connection-cauchy-phase-chambers | TODO | |
| 5 | prime-tail-copoisson-essential-boundary-bockstein | TODO | |
| 6 | rectangular-semilocal-observer-tail-separation | TODO | |
| 7 | route-b-semilocal-sonin-interim-verdict | TODO | |
| 8 | semilocal-dual-pair-euler-connection-source-law | TODO | |
| 9 | semilocal-euler-kernel-chart-differentiability | TODO | |
| 10 | semilocal-jacobi-linear-growth-prolate-domain-gate | IN PROGRESS | best-positioned; corpus already owns the archimedean Gamma measure + Jacobi coefficients |
| 11 | sonin-burnol-conductor-cutoff-bounded-graph-law | TODO | |
| 12 | sonin-place-transition-cutoff-dichotomy | TODO | |
| 13 | sonin-prime-seam-exterior-factorization | TODO | |
| 14 | sonin-small-cutoff-ground-row-survival | TODO | |
| 15 | sonin-two-particle-prime-coherence | TODO | |
| 16 | squarefree-cutoff-jump-root-avoidance-inertia | TODO | |
| 17 | transported-prolate-relative-resolvent-corner | TODO | |

## Corpus assets found (do not rebuild)

- `HTGeometry/MomentInnerProduct.lean` — `momentInner`, `PositiveMomentForm`.
- `HTGeometry/OrthogonalMomentPolynomials.lean` — `monicOrtho`, degree/monicity/orthogonality.
- `HTGeometry/AdaptiveOrthogonalSourceJacobiEnergy.lean` — `monicOrthoNormSq`, `monicOrthoAlpha`,
  `monicOrthoBeta` (`monicOrthoBeta s (n+1) = H_{n+1}/H_n`).
- `HTGeometry/FavardJacobiMomentRealization.lean` — `monicOrthoNormSq_favardMoment`.
- `RHTower/SoninSemilocalGammaMeasureCharacteristic.lean` — `semilocalArchimedeanGammaMeasure`,
  `semilocalArchimedeanGammaDensity`.
- `RHTower/SoninSemilocalJacobiRecurrence.lean` — `semilocalArchimedeanJacobiCoefficient n =
  √((n+1/2)(n+1))` = the card's `a_n(∅) = √((2n+1)(2n+2))/2`.
- `RHTower/SoninSemilocalJacobiOrthonormal.lean` — orthonormality of the archimedean family.
- `RHTower/SoninSemilocalFinitePrimeMeasure.lean` — `semilocalFinitePrimeEulerDensity`
  (finite family `p : Fin n → ℕ`), positivity, integrability, Poisson expansion.
- `RHTower/JacobiDeficiencyRankTwoAmbiguity.lean` — `IsJacobiSolution`, `jacobiSolutions`,
  `jacobiDeficiency`, `rank_jacobiDeficiency_le_one`, `jacobi_deficiency_indices`,
  `exists_isSelfAdjoint_extension_of_deficiency_one`.
- `RHTower/SemilocalProlateCriticalPotential.lean` — the four-point critical-potential identities.

## Mathematical corrections found while auditing the cards

- **card 1** (`archimedean-prolate-jacobi-limit-circle-transition`), section "Lean route":
  the `λ = 0` frozen-coefficient discriminant analysis is invalid.  At a **double** characteristic
  root the frozen roots do not approximate the true solution ratios to order `1/n`
  (test case `u_{n+1} − 2u_n + u_{n−1} = 0`: frozen roots `{1,1}`, true exponents `{0,1}`).
  The exact discrete Wronskian `ρ_n(u_{n+1}v_n − u_n v_{n+1}) = const` forces
  `s_1 + s_2 = −1`, not the card's `−2`.  Correct indicial equation at `λ = 0`:
  `s² + s + (3/4 − z)/4 = 0`, i.e. `s = (−1 ± √(1/4 + z))/2`; at `z = 0` the exponents are
  `−1/4, −3/4`.  The card's conclusion (limit point at `λ = 0`) survives, because the dominant
  exponent `−1/4 > −1/2`.
