# Euler squarefree-affine incidence--Fisher universality law

- **ID:** `euler-squarefree-affine-incidence-fisher-universality-law`
- **Law:** LAW502
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper proof and direct Lean check complete)
- **Register:** `[UNIVERSAL-LAW] [CORPUS-SYNTHESIS]`
  `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`
- **Target:** `formal/GaloisForLFunctions/RHTower/EulerSquarefreeAffineIncidenceFisherUniversalityLaw.lean`

## Theorem

At the critical boundary `sigma -> 1+`, the projective Fisher energy of the full affine Euler
source, including every square channel, is asymptotically identical to the relative-clock
incidence energy of the squarefree Möbius source:

```text
E_full-Euler(sigma) - E_squarefree-incidence(sigma) -> 0.
```

Thus square completion is invisible not only to the four-unit Fisher limit but also after direct
comparison with the independent divisor-incidence geometry.

## Theorem-generated derivation

Whole-corpus same-folder theorem-leaf pairing exposed:

- `tendsto_eulerSquarefreeAffineFisherEnergy_sub_squarefree`, which identifies the full affine
  Euler Fisher energy with squarefree Möbius Fisher energy;
- `tendsto_squarefreeMobiusCriticalFisher_sub_incidenceEnergy`, which identifies squarefree
  Möbius Fisher energy with its relative-clock incidence energy.

No direct theorem comparing the full affine Euler source with the incidence energy occurs in the
corpus. The target was obtained only after reading these two terminal declarations.

## Dependency-closed paper proof

Write `E`, `F`, and `I` for full affine Euler Fisher, squarefree Möbius Fisher, and squarefree
relative-clock incidence energies. Existing theorems give

```text
E - F -> 0,
F - I -> 0.
```

Continuity of addition yields

```text
(E - F) + (F - I) -> 0 + 0.
```

The left side is identically `E - I`; hence `E - I -> 0`. No numerical computation is used.

## Strict corpus delta

Corpus contains both adjacent asymptotic identifications and separate four-unit limits, but no
direct full-Euler/incidence connector. New theorem removes squarefree Fisher energy as an
intermediate coordinate and states source-completion invariance directly at incidence level.

## Lean result

`formal/GaloisForLFunctions/RHTower/EulerSquarefreeAffineIncidenceFisherUniversalityLaw.lean`
proves
`tendsto_eulerSquarefreeAffineCriticalProjectiveFisherEnergy_sub_incidenceEnergy`.

Direct exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/EulerSquarefreeAffineIncidenceFisherUniversalityLaw.lean`

The module is imported by `GaloisForLFunctions/RHTower.lean`.

## Post-proof novelty audit

Performed only after dependency-closed Lean proof passed.

- Nielsen, *Comparing the Zeta Distributions with the Pareto Distributions from the Viewpoint of
  Information Theory and Information Geometry* (2022), studies Fisher information of zeta
  distributions and its von Mangoldt expansion, but not squarefree conditioning, divisor-incidence
  gap energy, or invariance under adjoining every Euler square channel.
- Literature searches for squarefree Möbius Fisher information, divisor-incidence energy, and
  full-Euler/squarefree asymptotic equivalence found no matching direct law.

Verdict: `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`. Novelty is limited to direct asymptotic
identification of completed affine Euler Fisher geometry with squarefree divisor-incidence
geometry; no novelty is claimed for zeta-distribution Fisher information itself.

## Gates

- [x] Whole-corpus theorem-leaf discovery
- [x] Prior corpus and failed-route audit
- [x] Dependency-closed paper proof
- [x] Lean formalization; direct `lake env lean`
- [x] Post-proof literature audit
- [ ] Axiom and umbrella audit
