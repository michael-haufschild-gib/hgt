# Self-dual completed Bost--Connes system: the functional equation as an operator-algebra duality

- **ID:** `self-dual-completed-bost-connes-system`
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** collapse theorem of
  `../3-formalized/not_new_scientific_knowledge/born-temperature-kms-factor-type-duality.md` §8
- **Statement:** `[CONJECTURE]` There exists a C*-dynamical system whose partition function is the
  completed `Lambda(beta) = pi^(-beta/2) Gamma(beta/2) zeta(beta)` — the Bost--Connes prime modes
  welded to one continuous archimedean scale mode contributing `Gamma(beta/2)` — such that
  `beta -> 2-beta` is a duality of the system itself (an operation on its algebra/dynamics), not an
  identity of analytically continued scalars, with phase diagram symmetric about `beta=1`.

## Goal

The Born-temperature card proved that the ordinary Bost--Connes system cannot carry the functional
equation: its symmetry group `R_+ x Zhat*` has no `beta -> 2-beta` element, the Gamma-completion is
Born-invisible (a scalar on the diagonal channel), and the reflected-sector duality demanded at `xi`
zeros collapses to the identity wherever its phase condition holds. The residue is exact: a native
FE needs a *different* system in which the reflection acts on the off-diagonal algebra. Constructing
it would make the completed functional equation a Kramers--Wannier-type operator duality, with the
critical line as the self-dual locus of a genuine statistical system rather than a label. The
non-circularity demand transfers unchanged: `xi`, its divisor, and square-summability assumptions
must not enter the construction.

## Gates

- [ ] 0 → 1 in-progress: the algebra carrying the archimedean mode is fixed; the candidate duality
  map is written down on generators; the failure tests (scalar invisibility, group-averaging,
  measured trace) are re-run against it.
- [ ] 1 → 2 fully-proven: existence of the system, its KMS_beta classification, and the duality
  with fixed locus `beta=1` proved on paper.
- [ ] 2 → 3 formalized: partition-function weld and duality skeleton in Lean; operator content as
  explicit hypotheses.
- [ ] 3 → 4 publication-ready: novelty audit against Connes--Consani archimedean/adelic
  constructions and lattice Kramers--Wannier duality.

## Approach

1. The archimedean mode first: a one-mode system with partition function `Gamma(beta/2)` (a
   continuous-spectrum scale degree of freedom; `Gamma(beta/2) = integral over the half-line of a
   Boltzmann weight in the scale variable`). Ask what dynamics on which algebra produces it as a KMS
   partition function.
2. Weld: tensor/crossed-product it with the Bost--Connes system so the total partition function is
   `Lambda(beta)`; check whether `beta -> 2-beta` extends from the scalar identity
   `Lambda(beta)=Lambda(2-beta)` (wait — that identity holds for the *completed zeta in `s`*, i.e.
   `Lambda(s)=Lambda(1-s)`; under the Born dictionary `beta=2 sigma` this is exactly
   `beta -> 2-beta` on the real segment) to an algebra map exchanging high- and low-temperature
   sectors.
3. Kill tests inherited from the parent card: the map must act on the off-diagonal algebra
   (diagonal action is Born-invisible and dead); it must not be a scalar identity of partition
   functions; the factor-type wall must appear as the obstruction that the duality *resolves*
   (exchanging a type-`III_1` and a type-I phase is impossible normally — the duality must
   therefore be non-normal, antilinear, or a genuinely new categorical morphism, and naming that
   category is the first deliverable).
4. Degenerate control: drop the archimedean mode — the parent card proves no duality exists for
   bare Bost--Connes; the archimedean mode is therefore load-bearing or the conjecture is false.

## Log

- 2026-07-12 — created in 0-backlog from the collapse theorem of the Born-temperature card: the
  reflected-KMS duality for bare Bost--Connes is contentless; the surviving question is whether the
  completed `Lambda` is the partition function of a system with a native `beta -> 2-beta` duality
  acting off-diagonally.
