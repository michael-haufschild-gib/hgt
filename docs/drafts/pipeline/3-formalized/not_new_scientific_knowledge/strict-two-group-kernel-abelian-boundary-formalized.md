# Higher identity symmetry cannot contain the nonabelian quantum forces

- **ID:** `strict-two-group-kernel-abelian-boundary`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / HIGHER-GAUGE NO-SELECTION BOUNDARY
- **Paper proof:** `strict-two-group-kernel-abelian-boundary.md`
- **Scientific status:** `[LEAN-PROVED] [REDISCOVERED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean module:** `GaloisForLFunctions.HTGeometry.PeifferKernelAbelianBoundary`

## Exact formal result

`PeifferBoundary` records a group homomorphism

\[
\partial:H\to G,
\]

an operation of \(G\) on \(H\), identity action, and the second Peiffer identity

\[
(\partial h)\triangleright k=hkh^{-1}.
\]

The module proves unconditionally:

1. `PeifferBoundary.kernel_commutes` — every \(h\in\ker\partial\) commutes with every \(k\in H\);
2. `PeifferBoundary.ker_le_center` — \(\ker\partial\le Z(H)\);
3. `PeifferBoundary.kernel_pair_commutes` — any two kernel elements commute; and
4. `PeifferBoundary.injective_kernel_source_commutes` — every group embedding faithfully into
   \(\ker\partial\) is commutative.

The proof uses only the stated algebraic data. No crossed-module, 2-group, Lie-group, Standard
Model, gravity, or physical claim is assumed.

## Scientific boundary

Every crossed module supplies `PeifferBoundary` data, so the result formalizes the exact algebraic
core behind abelianness of identity-level 2-group symmetry. This is standard parent mathematics.
It rules out placing the full nonabelian weak and colour groups entirely in a higher identity
kernel, but it does not derive any physical higher group or force.

The positive research survivor is that a viable higher actuality atlas must retain
\(S(U(2)\times U(3))\) in first-level nonabelian stabilizers; higher cells may encode only abelian
phase, centre, gerbe, or anomaly coherence.

## Verification

- [x] source checked with
  `lake env lean GaloisForLFunctions/HTGeometry/PeifferKernelAbelianBoundary.lean`
- [x] final module build:
  `lake build GaloisForLFunctions.HTGeometry.PeifferKernelAbelianBoundary`
- [x] axiom audit: only standard Lean/mathlib foundations (`propext`, `Classical.choice`,
  `Quot.sound` where inherited by subgroup-centre infrastructure); no project axiom
- [x] `scripts/formal_tools.py lint`

## Gates

- [x] 0 → 1: exact architecture under attack stated
- [x] 1 → 2: dependency-closed paper proof
- [x] 2 → 3: final build, axiom audit, and lint
- [ ] 3 → 4: not publication target; parent-theory bridge only

## Log

- 2026-07-29 — formalized the minimal Peiffer argument and its faithful-source obstruction without
  axioms, placeholders, or physical assumptions.
