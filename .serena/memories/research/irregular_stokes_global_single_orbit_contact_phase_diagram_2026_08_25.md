# Global single-orbit completed-Xi contact phase diagram (2026-08-25)

Formalized complete abstract unit-Rees landing classification for arbitrary genus, nonempty marked-point family, arbitrary branch counts, and exactly one Stokes orbit at each point.

Files:
- `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesCubicSingleOrbitContactBudgetClassification.lean`
- `docs/drafts/pipeline/3-formalized/route-p-cubic-single-orbit-global-contact-phase-diagram.md`
- import added to `formal/GaloisForLFunctions/RHTower.lean`

Definitions:
- local ordered normalized contact budget `C_a = sum_{i,j} contactNumerator_a(i,j)/N_a`;
- global coefficient `A(g,d) = fusionCoefficient(g,p+1) + sum_a (1+m_a^2-C_a)/m_a^2`.

Theorems:
- exact contact law `W_unit(x)=A(g,d)*commonRank(x)^2`;
- every landing satisfies `(-A)r^2=-R_Xi`;
- landing fibre nonempty iff `A<0`, with explicit common rank `sqrt((-R_Xi)/(-A))` and local charge `r/m_a`.

Proof edge: orbit surjectivity `Fin(m_a) -> Fin 1` forces every `m_a>0`, so converse divisions are valid. This absorbs single-branch Euler collapse and two-branch sphere threshold as special cases.

Validation:
- direct targeted module elaboration passed;
- `/tmp` axiom audit of exactly two new definitions and three public theorems returned `[propext, Classical.choice, Quot.sound]` for all;
- no umbrella build, global lint, or full rebuild; `/tmp` scratch removed.

Scientific status: local Euler/contact scalarization is established parent-theory `[BRIDGE]`; exact completed-Xi phase diagram remains `[NOVELTY UNVERIFIED]` after primary-literature audit. This classifies abstract receivers only; arithmetic source-to-charge and actual meromorphic-connection realization remain open. Frontier map remained read-only; its dirty status belongs to concurrent work.