# The Wall, the Door, and the Litmus Test

This document sets the rules. It states three things:
1. a **test for when a body of work is a distinct branch of mathematics** (the criteria, §1);
2. the **boundary of the field's own territory** — the wall and its borders (§2);
3. the **test each item must pass** to be called native — the door (§3).

It is a specification for what we are building. Conjectural throughout; nothing here is claimed as
proven, and no proof of RH is claimed.

---

## 1. What makes a branch a branch

A name is not enough. Calculus, algebraic geometry, and differential Galois theory are branches because
they meet conditions a vocabulary cannot. We use seven. A body of work is a **distinct branch** when it
meets **all seven**; meeting only some makes it a sub-topic, a re-description, or a research programme.

| | Criterion | Test |
|---|---|---|
| **C1** | Native objects | Objects defined inside the field, not parent objects relabelled. If every occurrence can be replaced by "a parent object with property X" with no loss of structure, the ontology is not native. |
| **C2** | Native category | The objects form a category with the field's own morphisms, closed under its constructions (sub, quotient, product, dual, tensor, limit). |
| **C3** | Native invariant | An invariant functorial for the field's morphisms and not a pullback of a parent invariant. Two objects with identical parent-data must be able to differ in it. |
| **C4** | Native problem | A question statable only in the field's language. Erasing the field's vocabulary makes it impossible to write. |
| **C5** | Irreducible theorem (the keystone) | At least one theorem whose statement or proof needs the field's apparatus and is unobtainable inside any single parent. |
| **C6** | Faithful bridge | Specialization functors that recover known results on the overlap and strictly extend them. |
| **C7** | Autonomy | The field develops from its own definitions; a foundational core (definitions + one structural theorem) stands without constant appeal to a parent. |

**The bar, calibrated.** Differential Galois theory meets all seven, and C5 is why it is a branch: the
differential Galois group proves what ODE methods cannot see (Airy's equation has group `SL₂`, so it has
no closed-form solution). C5 is the goal we build toward — see §5.

---

## 2. The wall and its borders

**The native interior (the wall).** The field's territory is the **completed** multi-`q`-difference
structure — the **two hypertranscendence sources** held together (the founding fact: Hölder 1887 is about
the archimedean `Γ`, not the primes):
- **Source B — the prime difference lanes:** one dilation per prime, `σ_p : x_p ↦ q_p·x_p` with `q_p = 1/p`
  (**constant** multipliers), acting on the Bohr coordinates `x_p = p^{-s}`;
- **Source A — the archimedean differential generator:** the scaling derivation
  `∂_s = −Σ_p (log p) θ_p` (the `s`-flow; the **polynomial**-multiplier place `Γ(z+1)=z·Γ(z)`, whose
  `ζ`-regularized determinant is `Γ`) — carried **as a generator inside the wall, not as an obstruction
  outside it**;
- the module carrying the **simultaneous** action of all `σ_p` **and** `∂_s` — the completed
  `(σ_p, ∂_s)`-module `𝓜⁺` — with its difference Galois group `G_L⁺`, the corank of its relation lattice,
  and the difference-transcendence degree.

The natural diagonal object is the **completed `Λ = Γ·ζ`**; the functional equation `Λ(s)=Λ(1−s)` welds the
two sources. The objects and invariants are defined in `00-foundations-native-objects-and-gatekeepers.md`;
the conjectures are developed in `door/` (the archimedean generator in `door/bucket-archimedean-generator.md`).

**The borders.** Four specializations must recover known mathematics — each strips one source or collapses
the base:
- single prime / finite base → classical difference Galois theory (van der Put–Singer);
- root of unity / function field → the Frobenius / Weil–Deligne picture (function-field RH is Deligne);
- diagonal-flow closure → the Bohr–Kronecker structure `𝕋^∞`;
- **the archimedean factor alone** (Source A stripped of the primes) → **differential Galois theory /
  Hölder 1887** (`Γ` hypertranscendental).

The wall is the boundary of the native interior; the doors stand at the borders. **Native = the weld:** a
theorem using the prime `σ_p` and the archimedean `∂_s` *jointly and irreducibly*, reachable from no single
border parent.

---

## 3. The door (the litmus test)

An item — a draft section, a Lean module, a conjecture, a lemma, a plan — is **native** when it passes
all five tests. Door-2 is the master key.

- **Door-1 — object.** Does it refer essentially to the multi-`q` module / the `σ_p` family / `G_L`,
  rather than to a classical object (Euler product, Bohr lift, explicit formula, `ζ`-zeros, Weil pairing)
  that has merely been renamed?
- **Door-2 — load-bearing (the master key).** Strip every word of multi-`q`-difference-Galois vocabulary
  from the statement and its proof. If a parent discipline (analytic number theory, single-`q` Mahler
  theory, differential Galois theory, harmonic analysis on `𝕋^∞`) still proves it, the item is **not
  native** — the apparatus was decoration.
- **Door-3 — native invariant.** Does it compute, bound, or genuinely use a native invariant (`G_L`,
  `corank(Λ)`, the difference-trdeg, the holonomy type), not a renamed classical one (a dimension,
  degree, sign count)?
- **Door-4 — native zone.** Does it live where all parents fail at once — the **archimedean–prime weld**:
  `{ multiple independent prime bases } ∩ { the archimedean differential generator coupled to the prime
  difference generators — neither alone } ∩ { infinite / arithmetic base }`? (Source A alone is
  differential Galois / Hölder; Source B alone decouples and is BRIDGE; the native zone is their
  interaction.)
- **Door-5 — faithful restriction.** Specialized to a border (one prime, finite truncation, function
  field), does it recover the known classical answer?

> **The one-line test.** Remove the new vocabulary. If a parent still proves it, it never came through
> the door.

---

## 4. Grades

Every item carries exactly one grade.

| Grade | Meaning | Where it lives |
|---|---|---|
| **NATIVE** | passes Door-1..5 | inside the wall |
| **CONJECTURE (native)** | a native question, unproven | inside the wall, marked as an aim |
| **BRIDGE** | connects native and classical at a border | the doorway |
| **IMPORT** | a classical result the field uses but did not create | outside the wall, credited |
| **EMBASSY** | metaphor or physical analogy, not mathematics | quarantined, marked as such |
| **META** | index, vision, or this charter | — |

**One rule going forward.** Every new draft, Lean module, conjecture, or plan states its Door-1..5 grade
in its opening lines, or it stays outside the wall. When an item is tempting to wave through, state
instead the native theorem it would need (Door-2 essential use) and prove that.

---

## 5. The keystone

C5 is the target: the first theorem whose statement or proof needs the field's apparatus and that no single
parent can reach. The earliest candidates — the difference-Hölder statement (G1) and the corank dichotomy
(G3) — were Door-2 re-tested and came back **BRIDGE**: each lives on **Source B alone**, which decouples
prime-by-prime, so a parent reproves it. The lesson redirects the keystone to the **archimedean–prime
weld** — a theorem using the prime `σ_p` and the archimedean `∂_s` *jointly and irreducibly*
(`door/bucket-archimedean-generator.md`, `door/door-C5-irreducibility-and-door-2-retest.md`; the live
status of each candidate is in `door/00-status.md`). Proving one is what makes the work a branch **on the
C-axis (a peak)**. But the BRIDGE monoculture has raised a second possibility — that the field is not a peak
but a **substrate** — which the C-axis cannot test; see **§6**.

---

## 6. Two axes of novelty — peaks (the C-axis) and substrates (the D-axis)

§§1–5 test **one** mode of mathematical novelty: a **specialization** that rises *above* its parents and
proves what none of them can (differential Galois over ODE theory; C5 is its keystone). Call this the
**C-axis** — its signature of success is **"unobtainable in any single parent."**

There is a second mode the C-axis cannot see: a **substrate** that sits *beneath* the parents — the common
root each already contains as a shadow. A substrate has the **inverse** signature: under Door-2 it strips to
*some* parent **every time**, because it is present in all of them. So **universal reducibility (the BRIDGE
monoculture) is the signature of bedrock, not only of failure** — but it is *also* the signature of a trivial
re-description, and the D-axis exists to tell the two apart.

**The D-axis — the substrate test.** A body of work is a **candidate substrate** when:
- **D1 — Universal reducibility.** Every individual theorem Door-2-strips to a parent (the BRIDGE
  monoculture). *Necessary, not sufficient — a relabel has this too; D2 separates them.*
- **D2 — Unifying revelation (predictions, not relabelings).** The framework reveals distinct parents as
  faces of one structure, yielding **constraints/predictions a single parent cannot state**. Test: erase the
  framework and the parents look unrelated again. *(Met: `corank` unifies `F_q ⟷ ℚ` at 1 vs ∞; the
  orthogonality meta-theorem forbids prime-side RH-positivity — predictions, not renamings.)*
- **D3 — Constraint, not flow.** The central object is fixed by a binding **relation**, not generated by an
  **operation**. Substrates constrain; peaks operate. *(Met: the FE-constraint — "fixed by a constraint, not
  propagated by a flow.")*
- **D4 — The irreducible obstruction (the substrate's C5-dual).** A class **visible in every parent and
  computable by none** — the obstruction to the constraint factoring (the weld, `ω`). Not "a theorem no
  parent reaches" but "an obstruction every parent sees and none resolves." *(OPEN — this is exactly
  `door/door-C5-irreducibility-and-door-2-retest.md` #134; it decides substrate-with-content vs a gorgeous
  but empty atlas.)*
- **D5 — The foundation.** An actual definition of the substrate base — the **F_1 / absolute** object — from
  which D2's unifications become **theorems instead of observations**. *(OPEN — the F_1 frontier;
  `door/bucket-the-seam-archimedean-obstruction.md`, the missing single Frobenius.)*

**This is not a lower bar.** D4 **is** #134 and D5 **is** F_1 — each as hard as C5. The D-axis does not
*excuse* a C-axis failure; it **relocates and dualizes** the bar. A body of work may be tested on both axes:
this framework **fails the C-axis** (no C5; the BRIDGE monoculture) and is a **candidate on the D-axis**
(D1–D3 met; D4–D5 open). **"Not a peak; candidate bedrock"** is a coherent verdict, not a contradiction —
and is the project's current honest status.

**Grade refinement (extends §4).** A **BRIDGE** result that yields a D2-unification (a prediction across
parents) is **substrate-load-bearing** even though it fails the C-axis — mark it `BRIDGE (substrate)`. A
BRIDGE result that yields no unification is a plain re-description. The distinguishing test is **D2**, and it
is the discipline against mistaking romance for bedrock.

> **The litmus test, restated for both axes.** Remove the new vocabulary. If a parent still proves it, it did
> not come through the **peak**-door (C-axis). But ask also: does *erasing the framework* make the parents
> **forget they are related**? If so, it came through the **substrate**-door (D-axis). The first is a theorem
> no parent has; the second is a kinship no parent sees. This field has, so far, found kinships, not peaks —
> which is why it reduces to everything and is contained by nothing.
