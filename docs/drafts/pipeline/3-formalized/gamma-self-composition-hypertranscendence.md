# Hypertranscendence of Gamma self-composition

- **ID:** gamma-self-composition-hypertranscendence
- **Stage:** 3-formalized
- **Type:** THEOREM · HYPERTRANSCENDENCE
- **Status:** `[PROVEN] [LEAN FORMALIZED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The self-composite `z ↦ Γ(Γ(z))` is hypertranscendental.  Stronger, no algebraic
  differential relation holds on any nonempty open patch of its regular set.

## Proof mechanism

The generic Gamma factorial constraint-reflection theorem gives the implication

\[
\Gamma\circ\Gamma\ \text{differentially algebraic}
\quad\Longrightarrow\quad
\Gamma\ \text{satisfies one nonzero polynomial jet relation on }\Re z>0.
\]

Any such local relation for Gamma continues across the connected complement of its poles.  Multiply
the continued relation by the order-zero Gamma jet: off the poles the original relation vanishes,
and at every pole mathlib's totalized Gamma value is zero.  This produces a global nonzero
differential polynomial annihilating Gamma, contradicting the formal Hölder theorem.

For the local strengthening, the regular set is

\[
\Omega_{\Gamma\circ\Gamma}
=\{z:\Gamma(z)\notin\{0,-1,-2,\ldots\}\}.
\]

It is the already formalized regular set used for `ψ ∘ Γ`: its complement is countable and it is
path connected.  A relation on one nonempty regular open patch therefore propagates to every late
factorial microscope.  The microscope-local Gamma reflection theorem then yields the same forbidden
right-half-plane relation for the outer Gamma germ.

## Why this crosses the old wall

The backlog route correctly killed abstract `HT ∘ HT` closure, Nevanlinna-order arguments, and
finite chain-rule manipulations.  The factorial proof is source-specific: it uses the exact pole
residues `(-1)^n/n!`, a static highest-weight/point-degree initial form, and the Möbius limit
`x ↦ -1/x`.  It never evaluates a generic outer relation at an uncontrolled transcendental point.

## Gates

- [x] 0 → 1 in-progress: exact source-specific implication and local continuation route proved on
  paper
- [x] 1 → 2 fully-proven: local Hölder bridge and regular-patch propagation checked against the
  existing analytic-continuation and formal Hölder interfaces
- [x] 2 → 3 formalized: global and local capstones, targeted builds, lint, and axiom audit pass
- [ ] 3 → 4 publication-ready: exact-priority audit across composition and Gamma-iteration
  literature independently replicated and the germ/domain convention fixed for publication

## Formal realization

- `formal/GaloisForLFunctions/HTGeometry/GammaGammaFactorialBlowUp.lean`
  - `locallyPolynomialJetRigidAt_Gamma`
  - `hypertranscendental_Gamma_comp_Gamma`
- `formal/GaloisForLFunctions/HTGeometry/GammaGammaLocalHypertranscendence.lean`
  - `differentialRelation_GammaGamma_propagates`
  - `no_local_differential_relation_Gamma_comp_Gamma`

Both modules compile directly and through their individual Lake targets.  The six audited capstones
depend only on `propext`, `Classical.choice`, and `Quot.sound`.  The formal lint gate passes.  No
full project build was used.

## Novelty and parent boundary

- The generic claim that hypertranscendence survives arbitrary hypertranscendental composition is
  false by local inverse cancellation.
- Huang--Ng's outer-after-inner theorem requires the hypertranscendental inner function to be
  entire, so it excludes the meromorphic inner Gamma function.
- The project corpus previously recorded `Γ ∘ Γ` as an open immediate prize after several failed
  routes.  Current exact searches locate no prior hypertranscendence theorem for this composite.
- The candidate new scientific content is the theorem for the self-composite and its regular-germ
  strengthening, not Hölder's theorem or abstract affine-rescaling machinery.

The priority search covered exact `Γ(Γ(z))`/iterated-Gamma queries, Huang--Ng's composition
theorems, the Mijajlović--Malešević differential-algebra survey and Gamma applications,
Bergweiler's meromorphic-iteration survey, and recent differential/difference independence papers
for Gamma.  No source located states either theorem above.  Novelty therefore remains a candidate
priority claim pending independent expert review, not a certified historical first.

## Log

- 2026-07-15 — opened after the formal Gamma factorial constraint reflector crossed the
  evaluation-at-a-transcendental-point obstruction isolated in
  `transcendental-composition-ht.md`.
- 2026-07-15 — paper proof and both global/local Lean capstones completed; promoted to stage 3 after
  targeted compilation, formal lint, and axiom audit.
