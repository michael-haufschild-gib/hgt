# Library update request — INDEX + STATUS agent — add the corank-seam-invariant topic

**For:** the agent that maintains `docs/drafts/door/00-index.md` and `docs/drafts/door/00-status.md`
(librarian). **Date:** 2026-06-19. **Edit-race avoidance:** I did not touch the ledger files; please apply.
**Action:** register the new 0-backlog card **`../0-backlog/corank-seam-invariant.md`** in **both** files,
exactly as below.

---

## A. `00-status.md` §C — add one row (next number is **#124**)

Append to the §C table:

```
| 124 | **corank as the unifying seam invariant** — `corank(Λ_M)=rank(ℤ^{(P)}/Λ_M)=dim⟨g⟩-closure` (G3) is **one invariant with three proven faces**: G1 holonomicity (`<∞⟺`holonomic, #119), G2 continuation/period transcendence (`trdeg≤corank`, exact `=1` over `F_q`, #122), G4 weight torus (`dim W=corank=1` over `F_q`, #123); **finite over every border** (`=1` over `F_q`, `Λ_ff=ker deg`, #121). **Conjecture:** over ℚ `corank=∞` is *realized* (not just an upper bound) on all three faces simultaneously, and the gap `∞−1` **is** the missing single Frobenius / archimedean seam (`ζ` non-holonomic ⟺ no single Frobenius ⟺ corank=∞ ⟺ seam non-trivial); open content = a single **G1-anchored lower-bound realization** over ℚ. Door-3: **corank-native ⟺ seam non-trivial** (corank analogue of the proven `C3-native⟺C5★`); kept distinct from C5★ (this = the *archimedean* lock, C5★ = the *branchhood* lock) | [[bucket-the-seam-archimedean-obstruction]] | CONJECTURE | FIELDS MEDAL |
```

Then update the **§D tally / headline counts** for the +1 row:
- row count `123 → 124`;
- **CONJECTURE / stated conjectures** count `+1` (the "29 stated conjectures" figure and the §D
  CANDIDATE/CONJECTURE tally — bump the conjecture line by one). No change to proven/import/Lean counts.

Optionally add a §B "pick something to prove" pointer (FIELDS MEDAL, seam): the G1-anchored corank
lower-bound realization.

## B. `00-index.md` — add the card to the seam bucket; extend its scope clause

In the **`[[bucket-the-seam-archimedean-obstruction]]`** row (cross-cutting table, ~line 41):

1. **Work-package column** — append the new card filename to the list:
   `… ; `tate-prime-rigidity.md`; `baker-for-stieltjes.md`; `corank-seam-invariant.md` |`
2. **Scope column** — append one clause noting the unification (the new content this card adds):
   `… ; #124 unifies the three corank faces (G1 holonomicity / G2 transcendence / G4 weight torus) as one
   invariant and states the seam as a single G1-anchored ℚ lower-bound realization (corank-native ⟺ seam).`

(Optional cross-link: the `[[bucket-function-field-proving-ground]]` row already cites #121/#16/#123; a
back-pointer to #124 as the ℚ-side unification is welcome but not required.)

---

## C. Context / non-duplication (read before applying)

- The user observed corank had **no pipeline ticket** of its own — it existed only as a proven invariant
  (G3/#119/#121/#122/#16) plus the seam **door bucket**. The new card promotes the seam-corank `∞−1`
  conjecture from the bucket to a concrete pipeline problem **on the corank face**, unifying the three
  scattered faces into one object. The *open* content is a single **G1-anchored lower-bound realization**
  over ℚ (does `corank=∞` get *attained*, or only bound the faces?).
- **Non-duplication, flagged:**
  - vs `../2-fully-proven/corank-transcendence-continuation-bridge.md` (#122) — that is the **G2 face**
    (proven upper bound + exact FF `trdeg=1`); #124 is the **unified invariant** + the open cross-face
    realization. No overlap in open content.
  - vs `../1-in-progress/baker-for-stieltjes.md` — that holds the **analytic Stieltjes** ℚ realization;
    #124 supplies the **corank framing** + the G1-anchored implication structure, and hands the Stieltjes
    analysis back to it.
  - vs the in-flight `2026-06-19-wheeler-seam-three-faces.md` ticket — **complementary, not duplicate.**
    Wheeler characterizes the seam as a *σ-equivariant-splitting* obstruction with faces **C3/G2/C5**
    (the mechanism); #124 characterizes the *same* seam via the **corank** invariant with faces
    **G1/G2/G4** (the number). They meet only at G2 and "the seam." **Cross-link** both onto the seam
    bucket as two faces-decompositions; do **not** merge or collapse into one row.

## D. Pipeline state (FYI, no ledger action needed)

- New card is in **0-backlog**, gate 0→1 not yet cleared. First step (on the card): assemble the
  three-faces proposition from #119/#121/#122 (bookkeeping of proven results), then resolve the
  G1-anchored implication structure among the three ℚ realizations.
</content>
