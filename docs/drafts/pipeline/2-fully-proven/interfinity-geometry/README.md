# Interfinity geometry — paper-proof units

- **Stage:** 2-fully-proven
- **Parent program:** `../../1-in-progress/interfinity-geometry/interfinity-geometry-program.md`
- **Lean status:** not formalized; this folder is the Step-2 handoff

Each card below has a dependency-closed paper theorem and proof.  Cards are split by mathematical
interface so later Lean work can formalize small units without importing the whole research
program.

## Cards

1. `stable-primitive-exactness-topology.md` — all-degree quotient, exact sequence, persistence,
   death topology, immortality law, Scott/Sierpinski realization.
2. `spectral-terminal-horizon-model.md` — finite-part coboundary, stable cut, fixed-ray residue,
   complex-time phase locking.
3. `multi-time-polyhedral-horizon.md` — cubical exactness polyhedron, Boolean fixed faces, phase
   conormal.
4. `terminal-nerve-and-coherent-source-functor.md` — coherent/Fock equivalence, Gram-labelled
   simplicial persistence, nonfillable horn, Bargmann Bianchi law.
5. `terminal-transgression-curvature-flux.md` — flat commutator residue, cofinal-normalizer
   rigidity, curved bulk-boundary flux law.
6. `arithmetic-three-chart-stable-boundary.md` — source-pure degree-two quotient identifying
   mixed Stokes density, Sonin torsion, and Route-R BV--Wold holonomy.

## Formalization order

Recommended order: 1 → 6 → 5 → 4 → 2 → 3.  Card 1 is linear quotient algebra; card 6 is finite
difference algebra plus limits; card 5 is monoid cocycle calculus.  Cards 2 and 3 require the most
distribution theory.
