# Route R degree-six BV--Green cyclic-reader wall

- **ID:** route-r-degree-six-bv-green-cyclic-reader-wall
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/route-r-degree-six-bv-green-physical-cyclic-producer.md`
- **Statement:** The literal degree-six BV--Green Hochschild boundary has an explicit normalized source reader cyclic on its defining product pair; existence of such a reader agreeing with Route R's fixed physical marginal is pointwise equivalent to critical-line placement and globally equivalent to RH.

## Goal

Separate unconditional source cyclicity from the RH-bearing same-fibre physical comparison, so future
producer attempts cannot hide the missing theorem in a trace, normalization, completion, or quotient.

## Gates

- [x] 0 → 1 in-progress: exact source and physical claims separated
- [x] 1 → 2 fully-proven: dependency-closed source calculation and bidirectional classifier
- [x] 2 → 3 formalized: `RouteRDegreeSixBVGreenPhysicalCyclicDescentWall.lean`; targeted build green; capstone axiom audit passed
- [ ] 3 → 4 publication-ready: not a standalone preprint

## Formal theorem

For `d_k(T) = (T e_k)_k`, define

\[
  \tau_6 = \frac{5}{6} d_1 + d_6.
\]

Then `tau_6(Q)=1`, its values on `S_6^* Q S_6` and `Q S_6 S_6^*` are both
`1/6`, and hence it annihilates the literal degree-six Hochschild boundary.  Every reader cyclic
on that pair annihilates the boundary.

`RouteRDegreeSixBVGreenPhysicalCyclicDescent rho` requires a normalized pair-cyclic reader whose
boundary value equals the already fixed Route R physical marginal.  Lean proves

\[
  \mathrm{PhysicalCyclicDescent}(\rho)
  \iff \mathrm{physicalBoundary}(\rho)=0
  \iff \Re(\rho)=\tfrac12,
\]

and the quantified statement is equivalent to `RiemannHypothesis`.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/RouteRDegreeSixBVGreenPhysicalCyclicDescentWall.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Build: `lake build GaloisForLFunctions.RHTower.RouteRDegreeSixBVGreenPhysicalCyclicDescentWall`
- Capstone axioms: `[propext, Classical.choice, Quot.sound]`
- Forbidden declarations: none
- Repo-wide lint reached umbrella ownership and reported only unrelated concurrent modules missing
  from the `RHTower`/`HTGeometry` umbrellas; this module is wired and had no lint diagnostic.

## Frontier consequence

Source Hochschild presentation, normalized cyclic-reader existence, and boundary annihilation are
closed.  Remaining producer theorem must independently prove that fixed same-fibre physical
evaluation descends through this source cyclic quotient.  By the classifier, that assertion cannot
be obtained by definition or assumed as a generic trace law: it is exactly RH-strength.

## Log

- 2026-08-06 — paper proof and Lean formalization completed; physical producer remains open.
