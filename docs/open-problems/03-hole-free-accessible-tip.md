# Open Problem 3: A hole-free accessible boundary point for a pair of filled Julia sets

> **STATUS (2026-07-02): ANSWERED for the stated acceptance criterion — see
> [03-amswer.md](03-amswer.md); proof audited and correct.** The answer proves the Statement
> for the subclass `(c₁, c₂) = (c, −2)`, `−2 < c ≤ 1/4` real: `K₋₂ = [−2, 2]`,
> `K_c ∩ K₋₂ = [−β, β]` is connected, so by **Janiszewski's theorem** `K₁ ∪ K₂` does not
> separate the plane — there are **no holes at all** — and the explicit tip
> `z₀ = i√(β+c)` ∈ `J₁ ∖ K₂` works with `r = ½√(β+c)`.
>
> **Audit caveat (our specification error, not the answer's):** the partner `c₂ = −2` is an
> *exceptional* parameter — `φ₋₂` is algebraic over `ℂ(z)` (Chebyshev/Zhukovsky), so no pair
> `(c, −2)` is in the scope of the independence theorem, and the single-coordinate consequence
> (transcendence of `φ_c` over `ℂ(z)`) is already a machine-checked unconditional theorem
> in-tree (`phiMero_transcendental_of_mem_mandelbrot`) needing no tip. Two ingredients of the
> answer are load-bearing and reusable: (i) the **Janiszewski reduction** — connected
> `K₁ ∩ K₂` ⟹ no holes; (ii) the **explicit imaginary-axis tip** with its elementary escape
> proof. The genuinely load-bearing case (both parameters nonexceptional) is restated, with
> the acceptance criterion tightened to exclude vacuous classes, as
> **[Problem 4](04-nonexceptional-hole-free-tip.md)**.

**Field:** plane topology / complex dynamics / potential theory.
**Self-contained:** no knowledge of the surrounding project is needed. A proof of the
Statement below (for any nonempty class of parameter pairs) is a complete solution.

## Setting

Let `c₁ ≠ c₂ ∈ ℂ` and let `K_i = { z : the orbit of z under f_i(z) = z² + c_i stays bounded }`
be the filled Julia sets, `J_i = ∂K_i`. Each `K_i` is a **full** compact set: `ℂ ∖ K_i` is
connected (machine-verified in this project; classical). No connectivity assumption on `K_i`
itself is needed, but the main case of interest is both `c_i ∈ M` (both `K_i` connected).

Write
- `X = K₁ ∪ K₂`,
- `W` = the unbounded connected component of `ℂ ∖ X`,
- **holes** = the bounded connected components of `ℂ ∖ X`.

Elementary facts (may be assumed; the first two are machine-verified in this project):

1. If `K₁ ∩ K₂ = ∅` there are **no holes** (complement of two disjoint full compacta is
   connected), and `W = ℂ ∖ X`.
2. `∂W ∖ K₂` is nonempty and consists of points of `J₁` whenever `J₁ ⊄ K₂` — which, after
   possibly swapping the indices, holds for every distinct pair (the swap dichotomy:
   `K₁ = K₂ ⟹ c₁ = c₂`).
3. Every hole `H` has `∂H ∩ K₁ ≠ ∅` **and** `∂H ∩ K₂ ≠ ∅` (a hole bounded by one full `K_i`
   alone would be a bounded complementary component of that `K_i`).
4. Consequently, if a sequence of **distinct** holes accumulates at a point
   `z₀ ∈ ∂W ∖ K₂`, then each of those holes has diameter at least
   `dist(z₀, K₂) − o(1) > 0`: near `z₀` they form infinitely many disjoint "channels" of
   definite size, all crossing every small circle around `z₀` on their way to `K₂`
   (a comb-like interlocking of `K₁` and `K₂`).

## Statement (the problem)

> **Prove:** there exist a point `z₀ ∈ ∂W ∩ J₁` with `z₀ ∉ K₂` and a radius `r > 0` such that
>
> `B(z₀, r) ∩ K₂ = ∅`  and  `B(z₀, r) ∩ H = ∅` for **every** hole `H`.
>
> Equivalently: some point of `J₁ ∖ K₂` on the boundary of the unbounded component is **not**
> in the closure of the union of the holes. If this fails in general, characterize the
> exceptional pairs `(c₁, c₂)`.

In words: one boundary point of the first Julia set, escaping the second filled set and
visible from infinity, all of whose nearby basin points belong to the *unbounded* component
of `ℂ ∖ (K₁ ∪ K₂)`.

By fact 1 the Statement is **automatic when `K₁ ∩ K₂ = ∅`**. The open case is
`K₁ ∩ K₂ ≠ ∅` — and this is the *main* case, not an edge case: e.g. for both `c_i` real,
`K_i ∩ ℝ` are intervals around `0`, so the two filled sets always overlap.

## Why this is the whole problem (context, no proof needed by you)

Downstream (machine-checked or in verified preparation), the point `z₀` feeds this chain:
an assumed algebraic relation between the two Böttcher coordinates propagates, by the
identity theorem, from the far field to **all of `W`** — but to no other component of
`ℂ ∖ X`. At a hole-free `z₀`, *every* basin point near `z₀` lies in `W`, so every point of
`J₁` near `z₀` is a limit of relation-carrying points; a root-limit argument (no branch
coherence needed) plus a Baire pigeonhole over the finitely many algebraic branches then
places a relatively open piece of `J₁` on a smooth real-analytic curve, which forces
`c₁ ∈ {0, −2}` (Julia-set rigidity) — a contradiction closing the algebraic-independence
theorem for the pair. Holes are the sole obstruction: a `J₁`-point approached by hole
components carries no relation data there.

## What is known / likely attack routes

1. **Prime ends / accessibility.** `Ŵ = W ∪ {∞}` is a simply connected domain on the sphere
   (its complement `X ∪ holes` is connected when `K₁ ∩ K₂ ≠ ∅`). Uniformize by the Riemann
   map from the disk. Accessible boundary points are dense among prime ends; the question is
   whether hole-accumulation can happen at *every* accessible point of `∂W ∖ K₂`. F. & M.
   Riesz-type theorems and the fact that `∂W ∖ K₂ ⊆ J₁` carries positive harmonic measure
   in natural situations look directly relevant.
2. **Extremal length / modulus.** Fact 4 gives, at a hole-accumulation point `z₀`, infinitely
   many disjoint channels of diameter `≥ δ₀` crossing every circle `∂B(z₀, ρ)`, `ρ < δ₀`.
   Each channel needs conformal modulus to reach from scale `ρ` to scale `δ₀`; summing moduli
   of disjoint families against the annulus bound may already be contradictory for small `ρ`
   — this looks like the most elementary kill and should be tried **first**.
3. **Potential theory.** Both `K_i` have logarithmic capacity 1 and Green functions with
   known behaviour; holes are regions where both Green functions are positive but which are
   screened from `∞`. A quantitative screening estimate could bound the total "shadow" of
   the holes on `∂W`.
4. **Vary the point.** It suffices that hole-accumulation points are not all of
   `∂W ∖ K₂` minus a countable set (the downstream argument may also discard a countable
   bad set). Showing the hole-accumulation set is nowhere dense or of zero harmonic measure
   in `∂W ∖ K₂` is enough.

## Relation to the other problems in this folder

- Problem 01 (fixed-scale sector connector) is **refuted** (see `01-answer.md` and the
  status banner in `01-…md`); its surviving weakened form (factor-2 basis family at a
  movable tip) is the **fallback** route if the present Statement fails.
- Problem 02 Statement A is **proved** (see `02-answer.md`); it removes the disconnected
  lane from the blocker list entirely. The present problem is what remains for the
  connected and mixed lanes.

## Acceptance criterion

A rigorous proof (paper mathematics is fine; formalization is our job) of the Statement for
all pairs with `K₁ ∩ K₂ ≠ ∅` — or for an explicitly-described nonempty subclass (e.g. both
`c_i` real in `(−2, 0)`), with constants effective or effectivizable — or a counterexample
pair together with a characterization of when a hole-free accessible tip exists.
