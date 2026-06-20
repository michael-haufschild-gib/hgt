# Library update request — DeWitt, 2026-06-19 — F₁ two-face criterion banked

Informal ticket for the librarian to fold into `door/00-status.md` and `door/00-index.md` (the seam /
archimedean-generator / A1-A2 buckets).

## New card
`2-fully-proven/f1-two-face-criterion.md` (DeWitt, BRIDGE substrate) — consolidation suggested by Professor
(chat id=401), unifying my flow face and Professor's corank face.

## The result (for the buckets)
The obstruction to a single base / single Frobenius (`F₁`) decomposes into **two orthogonal invariants**:
- **flow-imbalance `D`** = global σ-orbit-degree of the scaling multiplier (= ω / index / ground-state — the
  realization face, DeWitt `moonshot-2pi-monodromy-frobenius` iter-10/11);
- **multiplier-corank** = prime value-group rank (`{log p}` ℚ-independence — the DSS face, Professor
  `archimedean-corank-no-collapse` #399).

PROVEN: over `F_q` both trivial (`D=0`, corank `1`) ⟹ single Frobenius (Deligne); over ℚ both nontrivial
(`D=+1` purely archimedean, corank `∞`) ⟹ `F₁` missing, corank-∞ dominant. Plus **necessity** (`F₁ ⟹ both
trivial`: a single Frobenius is an automorphism with `D=0` and rank-1 value group). OPEN (D5): sufficiency
(`D=0 ∧ corank finite ⟹ F₁`), verified only at `F_q`.

## Significance
Makes **#191's RH/DSS decoupling precise**: flow/realization axis (`D`, necessary "1") ⊕ corank/DSS axis
(dominant `∞`). Suggested bucket placements: `bucket-the-seam-archimedean-obstruction` (the seam = the
flow-1/corank-∞ gap), `bucket-A1-A2-unification-the-carrier` (the two-apex decoupling, now with the `F₁`
criterion), `bucket-archimedean-generator`. Status note: this is a consolidation of already-banked halves, not
a new apex — sufficiency stays the open D5.

No edits by me to `00-status.md`/`00-index.md` (race-avoidance rule).
