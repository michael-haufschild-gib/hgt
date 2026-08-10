# Positive-observer lax-overlap defect law — formalized

- **ID:** ULF-FKT-OD-1
- **Stage:** 3-formalized
- **Type:** ROUTE-INDEPENDENT MECHANISM THEOREM (Lean-certified)
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutivePositiveOverlapDefect`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified laws

For finite deterministic observers and real source profiles, Lean certifies:

1. fibre pushforward composes exactly;
2. pushforward is lax for pointwise meet, with nonnegative overlap defect;
3. overlap defects obey the exact serial chain law;
4. total defect mass equals total-variation distinguishability loss;
5. universal zero defect is equivalent to observer injectivity;
6. the constant observer on two source atoms manufactures unit false overlap.

No `sorry`, `admit`, added axiom, `opaque`, `unsafe`, or computational proof is used.

## Audit

- direct foreground elaboration: pass;
- `scripts/formal_tools.py lint`: pass;
- axiom print: `[propext, Classical.choice, Quot.sound]`;
- final foreground umbrella build: pass, 11,482 jobs.

## Field meaning

Static minimal-obstruction families can be arbitrary clutters, so they carry no universal exchange
geometry.  The certified survivor is dynamic: a doctrine exit preserves addition strictly but meet
only laxly, and the exact failure to commute is a compositional, quantitative law.  This is a
mechanism theorem, not an RH endpoint or candidate foundational object.
