# G3 — the corank / holonomy dichotomy (§60)

- **ID:** G3-corank-dichotomy
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Priority:** FOUNDATIONAL
- **Source:** ../../door/G3-holonomy-dichotomy.md · 00-status row #20
- **Statement:** An infinite-base diagonal is holonomic ⟺ `corank(Λ) < ∞`, via
  `dim ⟨g⟩-closure = corank(Λ)`; arithmetic (`Λ = 0`) is the curvature-flat but `corank = ∞`,
  infinite-rank / non-integrable extreme.

## Goal
Frames holonomicity through `corank(Λ)` (a would-be native invariant, C3) by tying it to geometric
integrability. The structural twin of G1, and the other leading C5 candidate (the Door-2 verdict below
grades it BRIDGE).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven: paper proof in `multi-q-difference-galois-foundations §60` (both directions,
  all bases)
- [x] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Door-2 verdict (2026-06-19): BRIDGE, not NATIVE
(⟹) is §59's argument; (⟸) is §49.2 + Lipshitz 1988 (the diagonal of a `D`-finite series is `D`-finite —
an import). The invariant `corank(Λ)` is the dimension of a torus-subgroup closure — a classical
algebraic-group invariant renamed — so it **also fails Door-3**. BRIDGE, not the C5 keystone. Full
reasoning: `../../door/door-C5-irreducibility-and-door-2-retest.md`.

## Next steps
1. As a BRIDGE it may still be **formalized** (the `dim ⟨g⟩-closure = corank(Λ)` identity; finite
   annihilator slices ledgered, `finitePrimeLogAnnihilator_eq_singleton`) and written up.
2. C5 now needs a theorem using the `σ_p` **jointly and irreducibly** — see the bucket's "forward" note.

## Log
- 2026-06-19 — created in 2-fully-proven (paper proof exists; next gate is Lean + the Door-2 verdict)
- 2026-06-19 — Door-2 verdict: **BRIDGE** (also fails Door-3). Stays in 2-fully-proven as a proved bridge theorem; C5 candidacy closed.
- 2026-06-19 — N2/G3 flatness corrected: curvature-flatness (`F_{pq}=0`) is not the holonomicity criterion in the infinite-base arithmetic case; finite rank / finite corank is.
- 2026-06-19 — Scope sharpened: G3 is the rank/order axis (function hypertranscendence); DSS/value transcendence is a separate G2/F₁ apex and is not implied by flatness or finite-rank wording.

## Lean return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven`: the theorem depends on the full G1/G3 holonomicity package, Lipshitz diagonal `D`-finite import, torus-closure dimension, and the corank/lattice assembly. None of those are present as no-hypothesis Lean theorems in the project; the existing finite annihilator anchors do not prove the whole dichotomy.

## Triage note — 2026-06-19 (Professor): returned to 2-fully-proven (user-directed; Leaner over-return)

Per @user ("send tickets that are clearly 'leaner is just lazy' back to fully-proven"): Leaner's return was a
**Lean-library-coverage objection** (no formal model of the imported / categorical / analytic objects), **not** a
paper-proof defect. This is a **paper-proven BRIDGE theorem** whose proof legitimately credits classical imports;
those imports are to be carried as hypotheses/axioms (or formalized separately) at the Lean stage — not a reason to
reject the paper proof. The card's stated theorem is proved at its 1→2 gate; any co-located open conjecture
(C5★ / ω=0 / Schanuel / apex) is explicitly a SEPARATE open core, not part of this theorem. Re-banked for Lean re-attempt.

## Lean completion — 2026-08-25

`GaloisForLFunctions.HTGeometry.HolonomyCorankDichotomy` now proves, with no project axioms:

- `dim(orbit closure) = corank(relation lattice)` at arbitrary cardinality;
- finite relation-lattice corank ⇔ finite-rank orbit holonomicity ⇔ finite-rank state-space
  realization;
- for response sequences, constant recurrence ⇔ finite orbit rank ⇔ bounded Hankel rank;
- for arithmetic prime logs, `Λ = 0`, every finite slice has corank equal to its cardinality, and
  the full quotient is not finite-dimensional.

Targeted build and new-endpoint axiom audit pass. Module is wired into the HTGeometry umbrella;
umbrella was not built.

This is the exact difference-category statement asserted by G3: `OrbitHolonomic` is finite rank of
the difference orbit, and the quotient by `orbitRelationLattice` is its first-isomorphism-theorem
presentation. No analytic replacement or premise is used.

`GaloisForLFunctions.HTGeometry.DFiniteOrbitHolonomyBoundary` separately closes a terminology trap:
standard analytic `D`-finiteness is not equivalent to finite difference-orbit corank. The existing
Gaussian witness `exp(z²)` is `D`-finite on `ℂ` but has unbounded Hankel rank; the new theorem
`dFinite_expSq_infinite_sequenceRelationCorank` derives that its relation-lattice quotient is not
finite-dimensional. Thus the formalized G3 theorem retains the paper's stated difference-category
meaning and does not silently strengthen it to a false analytic equivalence.

Both modules pass direct `lake env lean` checks and targeted module builds. Axiom audits of the new
boundary endpoints report only `propext`, `Classical.choice`, and `Quot.sound`. Both modules are wired
into the HTGeometry umbrella; the umbrella was not built.
