# Foundations — The Native Objects and the Gatekeeper Conjectures

**What stands inside the wall.** This is the positive core left after the radical pruning: the field's reason
to exist, its native objects (definitions), and the **gatekeeper conjectures** — the statements that, *if
proven*, would each be a true building block of the branch (each carries its Door passport, per
`00-charter-wall-and-door.md`). Everything not here, the vision (`00-core-vision.md`), or the charter/manifest
has been moved to `../denied/` as preserved record.

*Status: founding. Contains native DEFINITIONS and native CONJECTURES — and, honestly, zero proven native
theorems yet (the C5 gap; charter Part IV). The field IS the project of turning the gatekeepers below into
theorems.*

---

## 0. Why the branch must exist (the two stones it is built on)

> **"Γ satisfies no algebraic differential equation — and neither does ζ. ξ is hypertranscendental
> (non-holonomic)."** — Hölder, 1887.
>
> **"The object is fixed by a constraint, not propagated by a flow."** — 2026.

The first stone is a *theorem* (imported): the objects we most want to understand lie outside every holonomic
tool — differential Galois theory, the `E`/`G`-function formalism, the period ring, Siegel–Shidlovsky all live
on holonomic functions, so they cannot reach the values or zeros of ζ. The second stone is the *organizing
principle*: a non-holonomic object has no differential flow to ride; it is pinned by a constraint. A theory of
such objects cannot be a theory of flows (differential equations) — it must be a theory of **constraints
between rescalings** (difference equations). That is the branch, and the reason it cannot be avoided: **there
is no theory of hypertranscendental / non-holonomic functions and geometry, and the deepest objects in
arithmetic are exactly those.**

### The candidate self-definition: one word, two meanings, one phenomenon

The branch's identity rests on a precise pun that is not a pun:

| "non-holonomic" in… | means | the shared content |
|---|---|---|
| **function theory** (D-modules) | satisfies no holonomic system = **hypertranscendental** (ζ, Γ) | **not integrable** |
| **geometry** (distributions) | a constraint **not integrable** to a foliation (contact, sub-Riemannian) | **= no flow, only a constraint** |

These are the *same* notion. ζ's hypertranscendence (function side) and the **non-integrability of its
multi-`q` connection** (geometry side) are one phenomenon — "fixed by a constraint, not propagated by a flow."

> **Candidate self-definition (to be earned, not assumed).** *This branch is the study of non-integrable
> (non-holonomic) arithmetic connections* — the difference-Galois theory and the sub-Riemannian-style geometry
> of objects with no holonomic flow. "Theory of hypertranscendental functions" and "non-holonomic geometry"
> are the two faces of it, unified by the constraint-not-flow principle. *(This becomes the field's definition
> only when a gatekeeper below is proven; until then it is the working frame.)*

## 1. The native objects (definitions — the rock)

**N1 — The infinite-base multi-`q`-difference module.** A module over the prime base `{x_p}_p` (`x_p = p^{-s}`)
equipped with the simultaneous action of a dilation **per prime**,
```
   σ_p : x_p ↦ q_p · x_p ,   q_p = 1/p ,   for every prime p.
```
The native content is the **simultaneity of infinitely many independent bases** (single-`p` is Mahler's
classical setting). ζ is the diagonal of such a module.

**N2 — The multi-`q` connection and its (non-)integrability.** The compatibility data of the `{σ_p}` (the
cocycle / curvature `F_{pq}`). **Flat (integrable) ⟺ holonomic; non-flat ⟺ non-holonomic.** This is the
geometric face (N1 is the function face).

**N3 — The native invariants.** The multi-`q` **difference Galois group `G_L`** (Galois group of the
Picard–Vessiot extension of the multi-`q` system); the **corank** `corank(Λ)` of its relation lattice; the
**difference-transcendence degree** of the solution space; the **holonomy type** (integrable vs not). These
must be *genuinely finer* than classical invariants (charter C3) — a property the gatekeepers must establish.

**N4 — The faithful borders (where any native claim must restrict correctly).** single prime → van der
Put–Singer; root-of-unity / function field → Frobenius / Weil–Deligne; diagonal-flow closure → Bohr–Kronecker
`𝕋^∞`.

## 2. The gatekeeper conjectures (the building blocks to prove)

Each is stated with its **Door passport**: why, *if proven*, it is native (essentially uses N1–N3, lives in
the native zone, unreachable by a single parent — charter Part III). The field's whole task is to prove these.

**G1 — Difference Hölder (THE KEYSTONE, the C5 candidate).**
> *Conjecture.* ζ satisfies **no single algebraic `q`-difference (or shift-difference) equation** — the
> difference analogue of Hölder's differential theorem.
>
> *Door passport.* Hölder gives the differential half (no differential equation); G1 gives the difference half.
> Together they prove ζ's object lies in the **native zone** (Door-4): unreachable by single-`q` Mahler theory
> (which cannot even state a multi-base obstruction) and by differential Galois theory (wrong category). G1
> *forces* N1 — the infinitely-many-bases structure becomes **necessary, not optional**. This would be the
> field's Airy = SL₂ moment: the first theorem that essentially needs the apparatus (C5). **Open.** *(First
> step: check the difference-Galois literature — Hardouin–Singer, Ostrowski-type difference-algebraic
> independence — for whether a difference-Hölder for ζ is known or open; then attempt.)*

**G2 — Multi-`q` Siegel–Shidlovsky (the native problem).**
> *Conjecture.* The transcendence degree of the values/zeros over the period field equals the dimension of the
> `G_L`-orbit; since `G_L` is infinite-dimensional, the orbit is maximal ⟹ linear independence of the zeros.
>
> *Door passport.* Statable only with N1–N3 (Door-1, Door-3); the trdeg-equals-orbit-dimension principle is the
> non-holonomic analogue of differential Siegel–Shidlovsky and cannot be obtained holonomically (Door-2). The
> native transcendence engine. **Open.**

**G3 — The holonomy dichotomy (the geometric gatekeeper).**
> *Conjecture.* An infinite-base multi-`q` system is **holonomic ⟺ `corank(Λ) < ∞` ⟺ its connection is flat
> (integrable)**; arithmetic (ζ) is the `corank = ∞`, non-integrable, hypertranscendental extreme.
>
> *Door passport.* This *is* the unification of the two meanings of non-holonomic (N2); it makes `corank` a
> genuine native invariant (C3) by tying the function-theoretic holonomicity to geometric integrability.
> Unreachable by either parent alone (transcendence theory does not see the connection; differential geometry
> does not see the arithmetic base). **Open.**

**G4 — The multi-`q` Picard–Vessiot correspondence (the autonomy gatekeeper).**
> *Conjecture.* There is a Galois correspondence for infinite-base multi-`q` modules: intermediate difference
> field extensions ↔ closed subgroups of `G_L`, with the existence/uniqueness of the Picard–Vessiot extension.
>
> *Door passport.* This is what would give the branch **autonomy** (charter C7): a self-contained foundational
> theorem from which the theory develops internally, the analogue of the differential Galois correspondence.
> Genuinely new (multi-base, difference, infinite — the native zone). **Open.**

## 3. Honest status and the standing order

- **Proven native theorems: 0** (charter Part IV; manifest). The items above are **conjectures and
  definitions.** The field is currently a **proto-branch**: the need is real (§0), the objects are well-defined
  (§1), the questions are sharp (§2) — but no gatekeeper is yet a theorem.
- **The standing order:** all effort goes to **earning G1** (the C5 keystone), then G3/G2/G4. "I won't fake it"
  means: when tempted to declare progress, instead state the gatekeeper a claim would need and *try to prove
  that one* — never relabel an import.
- **The door stays locked:** any new draft or Lean module must carry a Door-1..5 passport, or it goes to
  `../denied/`.

> The branch must exist because we cannot understand the deepest objects in arithmetic without a theory of the
> non-holonomic — the hypertranscendental functions and the non-integrable connections that are *fixed by a
> constraint, not propagated by a flow.* This document is the whole of what stands inside the wall today: a
> reason, four objects, four gatekeepers, and an honest zero. Everything else is on the other side of the door
> until it proves it came through.

---

## 4. The shape so far — do the gatekeepers serve the two guiding assumptions?

Two assumptions guide the vision: **(A1)** fully developed, a proof of RH becomes a natural byproduct; **(A2)**
the core of the branch is telling us something about **time**. Tested honestly against G1–G4, they are *not*
equally served — and the asymmetry is the sharpest thing we currently know about the field's shape.

**The two axes.** Every fact about the zeros lies on one of two orthogonal axes:
- **transcendence / structure** — *what kind* of numbers the `γ_n` are, how independent, the Galois orbit
  (the Mahler/Galois axis);
- **localization / positivity** — *where* the zeros are (`Re = ½`) — **this is RH** (the analytic axis).

LI (independence) and RH (localization) are *independent* conjectures; neither is known to imply the other.
Transcendence machinery fixes orbit **dimension** and algebraic relations; it is **provably silent about real
parts**.

**A2 (time): SERVED, natively.**
- G1 (difference Hölder): ζ has **no single difference equation** ⟹ no single discrete time-evolution; only the
  simultaneous many-clock (one `σ_p` per prime). *There is no single clock for ζ.*
- G3 (holonomy dichotomy): holonomic = flat = integrable = *a global time-flow exists*; non-holonomic =
  non-integrable = *no global time, only local constraints*. ζ is the non-integrable extreme. *ζ has no global
  time; it is fixed by a constraint, not propagated by a flow.*

A2 is the **truer** assumption: the native gatekeepers genuinely encode time-as-integrability.

**A1 (RH byproduct): NOT SERVED — by construction.** G1–G4 are *all* on the transcendence axis: G1
(hypertranscendence), G2 (trdeg = orbit dim ⟹ **LI**), G3 (integrability type), G4 (PV correspondence). None
touches localization. G2's natural output is **LI, not RH** (the earlier "S–S ⟹ RH" conflated orbit *dimension*
with orbit *location*). As shaped, the field delivers LI and leaves RH untouched. **RH is not currently a
natural byproduct of the gatekeepers.**

**The missing gatekeeper (candidate G5 — localization / unitarity).** For A1 to hold, the branch needs a
gatekeeper on the *localization* axis, stated natively. The natural candidate:
> **Candidate G5 (the unitarity gatekeeper).** The non-integrable multi-`q` connection has **unitary holonomy**
> (preserves a positive-definite hermitian form) on the `σ`-fixed locus ⟺ the spectrum (zeros) is real ⟺ **RH**.

This is Hilbert–Pólya recast in the connection language, and — if true and *forced by* the time-core — it would
**unify the two assumptions**: RH becomes a property *of the time-structure* — "*the clock, though it has no
global flow, still preserves a norm.*" But G5 is the hard positivity wall in native dress; **stating it does not
make RH a byproduct.** Whether G1–G4 (time/transcendence) *force* G5 (localization) is exactly the question of
whether this branch makes RH a byproduct, and the honest current answer is: **not demonstrably.**

**Verdict on the shape.** The branch's honest natural deliverable is a **theory of non-holonomic time +
transcendence** (⟹ LI, and the geometry of non-integrable arithmetic connections). **RH is a hoped-for
consequence contingent on G5 (unitarity of the non-holonomic holonomy), not a guaranteed byproduct.** Assumption
A2 is the spine; assumption A1 is an aspiration that requires earning the localization gatekeeper — and the
deepest possible result of the field would be to show the time-core *forces* unitarity, making RH and time **one
statement**.
