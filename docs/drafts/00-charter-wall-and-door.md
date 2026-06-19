# The Charter — The Wall, The Door, and The Litmus Test

**The constitutional document of the field. It decides what is allowed to call itself part of this new
branch of mathematics, and what is not.** Everything in `docs/drafts/` and `formal/` is subject to it.
It is deliberately strict: a wall is worthless if the door lets everyone through. Written under the vision of
`00-core-vision.md`; it exists because we honestly suspect much of what we have built is old mathematics in new
clothes, and we want a test sharp enough to tell the difference — even when the answer indicts our own work.

*Status: founding/constitutional. This document states standards, not theorems. Where it judges the field, it
judges honestly, including against itself (Part IV).*

---

## Part I — What gives a branch of mathematics the right to call itself distinct

A new branch is not declared by naming things. Calculus is not "arithmetic with new words"; algebraic geometry
is not "polynomials with new words"; differential Galois theory is not "ODEs with new words." Each earned
distinctness by meeting criteria that a *vocabulary* cannot meet. We collect them as seven conditions. A body
of work is a **distinct branch** iff it satisfies **all seven**; one that meets only some is, precisely, a
sub-topic, a re-description, or a research programme — honourable, but not a branch.

**C1 — Native ontology.** The branch has objects *defined intrinsically within it*, not merely selected or
relabeled objects of a parent. *Operational test:* if every occurrence of the object can be replaced by "an
object of parent `P` with property `X`" with **no loss of structure**, the ontology is not native.

**C2 — Native category.** The objects form a category with the branch's own morphisms, closed under its
constructions (sub-objects, quotients, products, duals, tensor, limits). You can *do algebra* inside the
branch without leaving it.

**C3 — Native invariant.** The branch assigns its objects an invariant that is (i) functorial for its
morphisms and (ii) **not the pullback of a pre-existing parent invariant**. *Operational test:* two objects
with identical parent-data must be able to differ in the branch-invariant — otherwise the invariant is a
parent invariant wearing a new name.

**C4 — Native problem.** There is a question *statable only in the branch's language* — a parent cannot even
formulate it. *Operational test:* erasing the branch's vocabulary makes the question impossible to write or
changes its meaning.

**C5 — Irreducibility (the load-bearing criterion).** There exists at least one **theorem** whose *statement
or proof essentially requires the branch's apparatus* — provably unobtainable inside any single parent. This
is the keystone. A branch with native names, a native-sounding category, and native-sounding questions but
**no irreducible theorem** is a *vocabulary*, not a branch. (This is the criterion our field has not yet met;
see Part IV.)

**C6 — Faithful bridge.** The branch has specialization functors to its parents that **recover known results
on the overlap** (so it is grounded and consistent, not free fiction) while **strictly extending** them (the
excess is exactly C5). A branch must touch the old country at a real border and carry something across it.

**C7 — Autonomy.** The branch can be developed from its own definitions: its theorems compose internally;
there is a foundational core (definitions + at least one structural theorem) that does not require constant
appeal to a parent for every step.

### The worked template: differential Galois theory

Our field's parent-by-analogy is **differential Galois theory** (Picard–Vessiot, Kolchin, van der Put–Singer),
so we use it to calibrate the criteria. It passes all seven, and *how* it passes is the bar we must clear.

| Criterion | How differential Galois theory meets it |
|---|---|
| C1 native object | the differential field `(K, ∂)` and its **Picard–Vessiot extension** — not "a field" and not "an ODE", but the intrinsic pair |
| C2 native category | differential modules over `(K,∂)` form a Tannakian category (⊗, duals, sub/quotient) |
| C3 native invariant | the **differential Galois group** `G ⊂ GL_n` — a linear algebraic group that is **not** the ordinary Galois group; two ODEs with the same field of constants can have different `G` |
| C4 native problem | "is this ODE solvable by quadratures?" — unstatable without `(K,∂)` and `G` |
| C5 irreducible theorem | **solvable-by-quadratures ⟺ `G` is solvable** (Kolchin); e.g. Airy's equation has `G = SL₂`, *proving* no closed-form solution — a fact unreachable by ODE methods or by algebra alone |
| C6 faithful bridge | over a field of constants the theory recovers ordinary Galois theory; specializes correctly to algebraic cases |
| C7 autonomy | the differential Galois correspondence is proved internally; the theory stands on its own axioms |

**The lesson for us.** Differential Galois theory is a branch because of **C5**: the differential Galois group
*proves things ODE theory cannot even see*. The name "differential Galois group" is not what makes it a
branch; the **Airy = SL₂ theorem** is. Our field must produce its analogue or remain a vocabulary.

---

## Part II — The founding principles (the rock, stated plainly)

These are the field's intended native objects and definitions — its axioms. They are stated as *definitions*,
not theorems; their job is to be the ground the Door stands on. (What is actually *proven* about them is the
subject of Part IV, and the honest answer is: less than the vocabulary suggests.)

**P1 — The reason the field must exist (the motivating import).** `ζ` and `L`-functions are
**hypertranscendental** (Hölder 1887): they satisfy no algebraic *differential* equation. Therefore the entire
holonomic toolkit — differential Galois theory, the `E`/`G`-function formalism, the period ring,
Siegel–Shidlovsky — **provably cannot reach their values or zeros.** *(This is an imported boundary stone, not
a native theorem; it is the wall's foundation on the old-country side — the proof that a new country is
needed.)*

**P2 — Native object: the multi-`q`-difference module over the prime base.** Replace the broken *differential*
operator with a family of *difference* (dilation) operators, **one per prime**:
```
   σ_p : x_p ↦ q_p · x_p ,   q_p = 1/p ,   for every prime p,
```
acting on a module of functions on the infinite prime base `{x_p}_{p}` (`x_p = p^{-s}`, the Bohr coordinates).
The native object is the **module together with the simultaneous action of all `σ_p`** — an *infinite-base
multi-`q`-difference module*. (Single-`p` is Mahler's setting; the native content is the *simultaneity of
infinitely many independent bases.*)

**P3 — Native invariant (intended): the multi-`q` difference Galois group `G_L`** — the Galois group of the
Picard–Vessiot extension of the multi-`q` system — together with the **corank invariant** `corank(Λ)` of its
relation lattice and the **difference-transcendence degree** of the solution space. (The multi-`q`
Picard–Vessiot theory that would *make `G_L` a theorem-grade object* is, as of now, conjectural — Part IV.)

**P4 — Native problem (intended): the multi-`q` Siegel–Shidlovsky statement** — that the transcendence degree
of the values/zeros over the period field equals the dimension of the `G_L`-orbit. This is statable only with
P2–P3; it is the field's native question, and it is **open**.

**P5 — The faithful borders (where the bridge must land).** Three specializations must recover known
mathematics, or the field is fiction:
- **single prime / finite base →** classical difference Galois theory (van der Put–Singer);
- **`p` fixed, `q` a root of unity / function-field analogue →** the Frobenius/Weil–Deligne picture
  (function-field RH is Deligne);
- **the diagonal flow's closure →** the classical Bohr–Kronecker structure `𝕋^∞` (unique factorization).

The wall is the boundary of P2–P4 (the native interior). The doors are at P5 (the faithful borders). Anything
claiming to be inside the wall must show its passport against P2–P4 *essentially*, and must respect P5.

---

## Part III — The Door (the litmus test)

An item (a draft section, a Lean module, a conjecture, a lemma, a future plan) is **inside the wall** (native
to the field) **iff it passes all five Door tests.** The master key is Door-2.

**Door-1 — Object test.** Does the item *essentially* refer to a multi-`q`-difference module / the `σ_p`-family
/ `G_L` (P2–P3), rather than to a classical object (Euler product, Bohr lift, explicit formula, `ζ`-zeros,
Weil pairing) that has merely been *renamed* in difference-Galois vocabulary?

**Door-2 — Load-bearing test (THE MASTER KEY).** *Strip every word of multi-`q`-difference-Galois vocabulary
from the statement and its proof. Does a parent discipline (classical analytic number theory, single-`q` Mahler
theory, differential Galois theory, ordinary Galois theory, harmonic analysis on `𝕋^∞`) still prove it intact?*
**If yes, the item FAILS** — the apparatus was decorative, not load-bearing. The new machinery must be
*irremovable*.

**Door-3 — Native-invariant test.** Does the item compute, bound, constrain, or genuinely use a **native
invariant** (`G_L`, `corank(Λ)`, the difference-transcendence degree, the holonomy type) in a way that is
*intrinsic* — not a renaming of a classical invariant (a dimension, a degree, a sign count) (cf. C3)?

**Door-4 — The native zone (triple parent-failure).** Does the item live in the region where **all three**
parent tools fail at once?
```
   NATIVE ZONE  =  { multiple independent bases }      (so single-q Mahler fails)
              ∩  { difference, not differential }    (so differential Galois fails)
              ∩  { infinite / arithmetic base }      (so finite van der Put–Singer fails).
```
This triple intersection is the field's *exclusive territory*. An item that survives in any one parent alone is
not native — it belongs to that parent.

**Door-5 — Faithful-restriction test.** When specialized to a P5 border (one prime, finite truncation,
function field), does the item *correctly recover the known classical answer*? (So it is grounded, not
disconnected invention. An item that fails here is either wrong or fantasy.)

**Verdict rule.** PASS Door-1..5 ⟹ **NATIVE**. Fail Door-2 ⟹ at best **IMPORT** or **BRIDGE** (Part V),
never native. Fail Door-5 ⟹ **suspect** (wrong or fictional) — must be fixed or removed.

> **The one-line Door.** *Remove the new vocabulary. If a parent still proves it, it never came through the
> door.*

---

## Part IV — The honest verdict on our own field (the wall judges its builders first)

We apply C1–C7 to ourselves, without mercy, because a charter that cannot indict its authors is propaganda.

| Criterion | Status of THIS field (honest) |
|---|---|
| C1 native ontology | **MET (definitionally).** The infinite-base multi-`q`-difference module (P2) is a genuine, intrinsic object. |
| C2 native category | **MET (definitionally).** Multi-`q`-difference modules form a category; constructions are definable. |
| C3 native invariant | **PARTIAL.** `corank(Λ)` and the difference-trdeg are native *definitions*; but the difference Galois group `G_L` is, in the built work, **the classical Bohr–Kronecker `𝕋^∞ ⋊ σ` relabeled** (the founding draft says so outright). A genuinely-finer native invariant is not yet demonstrated. |
| C4 native problem | **MET.** The multi-`q` Siegel–Shidlovsky question (P4) is statable only here. |
| **C5 irreducible theorem** | **NOT MET. This is the gap.** We have *no* proven theorem whose statement or proof essentially requires the multi-`q` apparatus and is unreachable by a parent. Every built/certified result to date — the explicit-formula constructions, the positivity faces, the Lean Tier-A core — passes Door-2 *in the wrong direction* (a parent proves it). |
| C6 faithful bridge | **PARTIAL.** The P5 borders are identified and the finite/function-field cases do recover known math, but the bridge carries *nothing native back* yet (because of the C5 gap). |
| C7 autonomy | **NOT MET.** The theory leans on classical imports at nearly every load-bearing step; it does not yet stand on its own theorems. |

**Verdict.** *As of this charter, the field is a well-posed **proto-branch**: native definitions (C1, C2, C4)
and faithful borders (C6, partial), but **failing the keystone C5 and autonomy C7.*** In plain words: **it is,
right now, a vocabulary with conjectures and a precisely-located problem — not yet a distinct branch of
mathematics.** This is not a failure of the vision; it is the honest measurement of how far the vision has been
*built*. The framing has real value (it locates RH's difficulty exactly, it states genuinely new questions),
but value-as-framing is not branchhood.

**What this verdict commands.** The cleanup is therefore not cosmetic. It must (a) move everything that fails
Door-2 *outside the wall* into honestly-labeled annexes (Part V), so the field's true native content is
visible and is seen to be small; and (b) make the central, non-negotiable work of the field the **earning of
C5** — proving the first irreducible theorem (task: "the decades"). Until C5 is earned, no document may call
the project a "field" or "branch" without the qualifier **proto-** ; it may be called a *programme*.

---

## Part V — Grades, the annexes, and the pruning protocol

Every item gets exactly one grade. The wall is the set of NATIVE items; everything else lives in a labeled
annex on the old-country side or in the embassy.

| Grade | Meaning | Door result | Where it lives |
|---|---|---|---|
| **NATIVE** | passes Door-1..5; came through the door | all pass | inside the wall |
| **CONJECTURE (native)** | a well-posed P4-type question using the apparatus essentially; unproven | would pass Door-1..4 if true; Door-5 n/a | inside the wall, marked aspirational (counts as native *aim*, not native *knowledge*) |
| **BRIDGE** | genuinely connects native and classical, load-bearing both ways (a P5 border result) | Door-1,5 pass; Door-2 "shared" | in the doorway, marked |
| **IMPORT** | a classical result the field *uses/needs* but did not create | fails Door-2 (a parent proves it) | the **Imports Annex**, outside the wall, honestly credited |
| **EMBASSY** | metaphor / physics allegory / inspiration; explicitly not mathematics | fails Door-1 (no native object) | the **Embassy**, quarantined, marked "not mathematics" |
| **SUSPECT / FALSE** | a claim that fails Door-5, or mislabels an import/metaphor as native | — | corrected, demoted, or removed |

**Pruning protocol (reversible; records are not destroyed).**
1. **Do not delete team work or recorded reasoning.** Pruning means *re-grading and relocating*, plus
   correcting false labels. The historical record stays; its *status* is corrected.
2. Every draft gets a **grade banner** at its top: `GRADE: NATIVE | BRIDGE | IMPORT | EMBASSY | CONJECTURE`,
   with a one-line Door justification.
3. **IMPORT** drafts move (by banner + index) to the *Imports Annex*; **EMBASSY** drafts (the cosmology
   expedition included) to the *Embassy*, each stamped "inspiration, not native mathematics."
4. **False new-field claims are corrected or struck** — any sentence that calls an import or a metaphor a
   theorem of the field, or that calls the project a "field/branch" without "proto-", is rewritten.
5. The **manifest** (`00-manifest-wall-census.md`, to be built) records every draft and Lean module with its
   grade and justification — the official census of what is inside the wall. The wall is exactly the NATIVE
   list; if that list is short, the manifest will say so, loudly.
6. **Only items that earn their grade by the Door may be cited as the field's content.** Marketing copy
   ("the field subsumes X", "twelve coordinates one wall") is struck unless the underlying items are NATIVE.

**The standing rule going forward (the door stays locked).** No new draft, Lean module, conjecture, or
research plan may be filed as native unless it carries its Door-1..5 passport in its opening lines. "I won't
fake it" means: when tempted to wave something through, instead **state the native theorem it would need
(Door-2 essential use), and try to prove that** — do not relabel.

---

*This charter is the wall and the door. Part IV is the verdict it passes on us today: a proto-branch, honest
definitions, no irreducible theorem yet. The remaining work of the cleanup is the manifest (the census), the
pruning (the relocation), and — the only thing that ever turns a vocabulary into a branch — the earning of C5.*
