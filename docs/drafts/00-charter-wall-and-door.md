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

**The native interior (the wall).** The field's territory is the multi-`q`-difference structure on the
prime base:
- one dilation per prime, `σ_p : x_p ↦ q_p·x_p` with `q_p = 1/p`, acting on functions on `{x_p}_p`
  (`x_p = p^{-s}`, the Bohr coordinates);
- the module carrying the **simultaneous** action of all `σ_p` — an infinite-base multi-`q`-difference
  module;
- its difference Galois group `G_L`, the corank of its relation lattice, and the difference-transcendence
  degree.

The objects and invariants are defined in `00-foundations-native-objects-and-gatekeepers.md`; the
conjectures about them are developed in `door/`.

**The borders.** Three specializations must recover known mathematics:
- single prime / finite base → classical difference Galois theory (van der Put–Singer);
- root of unity / function field → the Frobenius / Weil–Deligne picture (function-field RH is Deligne);
- diagonal-flow closure → the Bohr–Kronecker structure `𝕋^∞`.

The wall is the boundary of the native interior; the doors stand at the borders.

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
- **Door-4 — native zone.** Does it live where all three parents fail at once:
  `{ multiple independent bases } ∩ { difference, not differential } ∩ { infinite / arithmetic base }`?
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

C5 is the target: the first theorem whose statement or proof needs the multi-`q` apparatus and that no
single parent can reach. The gatekeeper conjectures (`00-foundations-native-objects-and-gatekeepers.md`,
developed in `door/`) are the candidates; the live status of each is in `door/00-status.md`. The nearest
candidates are the difference-Hölder statement (G1) and the corank dichotomy (G3); the Door-2 re-test
(`door/door-C5-irreducibility-and-door-2-retest.md`) decides their grade. Proving one is what makes the
work a branch.
