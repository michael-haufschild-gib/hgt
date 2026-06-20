# Native Objects and the Gatekeeper Conjectures

The field's reason to exist, its native objects, and the **gatekeeper conjectures** — the statements
that, once proven, are the building blocks of the branch. Each conjecture is developed in `door/`; the
live status of all of them is in `door/00-status.md`. Read alongside `00-charter-wall-and-door.md` (the
branchhood test and the Door).

Conjectural throughout; no conjecture here is claimed as proven, and no proof of RH is claimed.

---

## 0. Why this theory

`ζ` and the L-functions are **hypertranscendental**: they satisfy no algebraic differential equation. The
founding fact is Hölder's 1887 theorem that the **archimedean factor `Γ`** is hypertranscendental; `ζ` and
the L-functions inherit it through the completion `Λ = Γ·ζ` and the functional equation. So the holonomic
toolkit — differential Galois theory, the `E`/`G`-function formalism, the period ring, Siegel–Shidlovsky —
cannot reach their values or zeros. These are among the deepest objects in arithmetic, and no theory is
built for them.

A non-holonomic object has no differential flow to ride; it is fixed by a **constraint between
rescalings**, not propagated by a flow. The right setting combines **both** rescaling lanes — the
infinitely many prime dilations `σ_p` (difference, **constant** multipliers) **and** the archimedean
scaling generator `∂_s` (the differential lane, **polynomial** multiplier `Γ(z+1)=z·Γ(z)` — the place
Hölder's theorem is actually about). The native content is their **weld** on the completed `Λ = Γ·ζ`
(`00-charter-wall-and-door.md` §2; the two sources of hypertranscendence).

**Working definition.** The field is the study of **non-integrable (non-holonomic) arithmetic
connections**: the difference-Galois theory and the sub-Riemannian-style geometry of objects with no
holonomic flow. "Theory of hypertranscendental functions" and "non-holonomic geometry" are two faces of
one notion — *not integrable*. This becomes the field's settled definition once a gatekeeper below is
proven.

**Operational criterion (the two axes, computationally — confirms §0, does not weaken it).** Each
hypertranscendence axis is a concrete test on a function's jet, via the smallest singular value of a
jet-monomial matrix (nonlinear: jet-degree `>1` allowed; the linear/spectral tests are *blind* to
hypertranscendence, since Hölder is a nonlinear statement). (i) *Differential axis (Hölder / "flow"):*
does `f` satisfy an algebraic differential equation `P(x,f,…,f^{(w)})=0`? — Hölder-HT objects (`Γ, ζ, Λ`)
**resist at every order**; an object with a finite ADE is **caught** at its order. (ii) *Difference axis
("constraint"):* the same test on shifts `{f(x),f(x+1),…}` — `Γ` is **caught** at first order
(`Γ(z+1)=z·Γ(z)`), the FE/constraint the objects *do* possess. So the native cell is
**differential-resist × difference-caught = "constraint, not flow,"** i.e. exactly the weld
`𝓜⁺ = (σ_p, ∂_s)`: `∂_s` the absent differential flow, `{σ_p}` the present difference constraint.

This makes one boundary precise: *differentially-algebraic but classically-irreducible* objects —
**Painlevé transcendents** (satisfy the Painlevé ADE) and **modular forms** (`E₂, η`, partitions: satisfy
the Chazy–Ramanujan ADE) — are **caught** by the differential test, hence are **not** hypertranscendental
in Hölder's sense and lie **outside** this field's class, despite being "transcendental." The charter's
class is the strictly smaller `{f : resists every ADE}` = `{Γ, ζ, L, Λ}`. (All classical: Hölder 1887,
the Painlevé/Chazy equations; the singular-value test is the numerical witness, verified at dps 80 in
`computations/2026-06-20-wheeler-nonlinear-ade-probe.py`.)

## 1. The native objects

- **N1 — The infinite-base multi-`q`-difference module.** A module over the prime base `{x_p}_p`
  (`x_p = p^{-s}`) with a dilation per prime, `σ_p : x_p ↦ q_p·x_p`, `q_p = 1/p`. The native content is
  the **simultaneity of infinitely many independent bases** (single-`p` is Mahler's classical setting).
  `ζ` is the diagonal of such a module. **(This is Source B — the prime / difference lane.)**
- **N1⁺ — The archimedean generator and the completed module (Source A + the weld).** The scaling
  derivation `∂_s = −Σ_p (log p) θ_p` (the `s`-flow; **polynomial** multiplier `Γ(z+1)=z·Γ(z)`, whose
  `ζ`-regularized determinant is `Γ`), carried as a native generator **alongside** the `σ_p`, forming the
  completed `(σ_p, ∂_s)`-module `𝓜⁺` with Galois group `G_L⁺`. The diagonal object is the **completed
  `Λ = Γ·ζ`**; the functional equation `Λ(s)=Λ(1−s)` welds the two sources. The native zone is the
  **weld** (archimedean×prime), not either lane alone. (Hölder 1887 = Source A alone = the differential
  Galois border; `door/bucket-archimedean-generator.md`.)
- **N2 — The multi-`q` connection.** The compatibility data of the `{σ_p}` (the cocycle / curvature
  `F_{pq}`). The prime dilations are **curvature-flat** (`F_{pq}=0`, commuting `σ_p`); holonomicity is
  instead the finite-rank / finite-corank condition. Arithmetic is curvature-flat but infinite-rank
  (`corank=∞`), hence non-holonomic by rank, not by nonzero curvature. In finite dimensions the two notions
  coincide; in the infinite base they split. Keep three axes distinct: curvature (`F_{pq}=0`), rank/order
  (`corank=∞`, `G_L` infinite-dimensional, Hölder-style function hypertranscendence), and
  value-transcendence/DSS (`γ_n` beyond the regular base, the open F₁/GROUP→VALUES lift); flatness controls
  neither rank nor values by itself.
- **N3 — The native invariants.** The difference Galois group `G_L` (of the Picard–Vessiot extension),
  the corank `corank(Λ)` of its relation lattice, the difference-transcendence degree, and the holonomy
  type.
- **N4 — The borders.** single prime → van der Put–Singer; root of unity / function field → Frobenius /
  Weil–Deligne; diagonal-flow closure → Bohr–Kronecker `𝕋^∞`.

## 2. The gatekeeper conjectures

Each is one line, with why it would be native and where it is developed.

- **G1 — Difference Hölder (the keystone, C5 candidate).** `ζ` satisfies **no single algebraic
  `q`-difference equation**. *Native:* with Hölder's differential half, this places `ζ` in the native
  zone — out of reach of single-`q` Mahler theory and of differential Galois theory; it turns N1 from
  optional into necessary. → `door/G1-difference-holder.md`.
- **G2 — Multi-`q` Siegel–Shidlovsky (the native problem).** The transcendence degree of the zeros over
  the period field equals the dimension of the `G_L`-orbit; `G_L` is infinite-dimensional, so the zeros
  are independent (DSS). The native transcendence engine. → `door/G2-multi-q-siegel-shidlovsky.md`.
- **G3 — The holonomy dichotomy.** An infinite-base system is **holonomic ⟺ `corank(Λ) < ∞` ⟺
  integrable to finite rank**; arithmetic is the curvature-flat but `corank = ∞` non-integrable extreme.
  This is the rank/order layer only; DSS value-transcendence remains separate in G2. Makes `corank` a native
  invariant. → `door/G3-holonomy-dichotomy.md`.
- **G4 — The multi-`q` Picard–Vessiot correspondence (autonomy).** A Galois correspondence for
  infinite-base multi-`q` modules: intermediate extensions ↔ closed subgroups of `G_L`, with existence
  and uniqueness of the Picard–Vessiot extension. → `door/G4-multi-q-picard-vessiot-and-langlands-group.md`.
- **G5 — The unitarity gatekeeper (candidate).** The non-integrable multi-`q` connection has **unitary
  holonomy on the `σ`-fixed locus ⟺ the spectrum (zeros) is real ⟺ RH**. →
  `door/G5-unitarity-gatekeeper.md`.

## 3. The two axes and the aim

Facts about the zeros lie on two axes:
- **transcendence / structure** — *what kind* of numbers the `γ_n` are, how independent (the Galois
  orbit);
- **localization** — *where* the zeros are (`Re = ½`). This is RH.

The two are independent: independence (LI) and localization (RH) do not imply each other, and
transcendence machinery fixes orbit dimension and algebraic relations while saying nothing about real
parts.

G1–G4 sit on the **transcendence axis**; their natural output is independence of the zeros. G5 sits on
the **localization axis**; it is RH in the connection's language (Hilbert–Pólya recast: a constraint
with no global flow that still preserves a norm).

Two assumptions guide the work:
- **A1** — fully developed, a proof of RH is a natural byproduct (the localization axis, G5);
- **A2** — the core is about time: non-holonomic means no global clock, only the simultaneous many-clock
  of the `σ_p` (the transcendence/constraint axis, G1–G4).

**The aim that joins them:** show that the constraint-structure (G1–G4) **forces** G5 — that unitarity
follows from the non-holonomic core. If it does, RH and the time-structure are one statement. The
unification, and the single object on which both faces live (the carrier germ `m_ξ` / the boundary
representation of `G_L`), are developed in `door/bucket-A1-A2-unification-the-carrier.md`.
