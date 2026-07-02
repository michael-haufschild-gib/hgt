# Open Problem 2: Steering an analytic curve family past a Cantor Julia set

> **STATUS (2026-07-02): ANSWERED — see `02-answer.md`.**
> **Statement A is TRUE for every disconnected pair, with no exceptional pairs.** The proof
> is elementary and verified by reading: fix any single admissible `r₀`; the tower piece is
> finitely many injective analytic arcs; each bad angular set `η_ν⁻¹(K₂)` is a compact
> totally disconnected subset of an interval, hence nowhere dense; a finite union of such
> sets still omits a whole angular subwindow `W`, and the tower piece over `W` avoids `K₂`.
> The angular (second) parameter alone suffices — no radius steering needed.
> **Statement B is FALSE** (a slanted linear projection of a perturbed Chebyshev Cantor
> Julia set fills an interval, so every leaf of a straight-line foliation meets `K`). This
> costs nothing downstream: only Statement A was consumed.
>
> Consequence: the disconnected lane has **no remaining open mathematics** — what is left is
> formalization (tracked as tasks B1a–B1d in the project). The open problems for the
> connected and mixed lanes moved to `03-hole-free-accessible-tip.md`.
>
> The original statement is kept below unchanged, for the record.

**Field:** complex dynamics / plane topology / geometric measure theory.
**Self-contained:** no knowledge of the surrounding project is needed. A proof of either
Statement below is a complete solution.

## Setting

Let `c₁, c₂ ∈ ℂ` be two parameters for which the filled Julia sets
`K_i = { z : the orbit of z under f_i(z) = z² + c_i stays bounded }`
are **totally disconnected** (Cantor sets; equivalently `0 ∉ K_i`), with `c₁ ≠ c₂`.

Write `G₁` for the Green's function of `K₁` (harmonic on `ℂ ∖ K₁`, `G₁ = 0` on `K₁`,
`G₁(z) = log|z| + o(1)` at ∞) and `h₁ = G₁(0) > 0` for its critical value.

A machine-verified construction produces, for the parameter `c₁`, families of compact
"tower pieces" in the plane, with free parameters:

- **arcs**: for each radius `r` in an open interval `(a, b)` and each angular window,
  a real-analytic arc lying on the Green level curve `{ G₁ = ℓ(r) }` where `ℓ(r)` is an
  explicit strictly monotone function of `r` (with `0 < ℓ(r) < 2h₁`, below the critical
  level, plus their dyadic root-lifts at levels `ℓ(r)/2^j`);
- **loops**: circles `{ |φ₁(z)| = r }` in the far field (these avoid every bounded set
  for `r` large, so they are harmless).

The pieces are curves (finite unions of real-analytic arcs); as `r` sweeps its interval,
the arcs at a fixed level-index sweep an open region (the level-annulus between two Green
levels), and arcs for different `r` are **pairwise disjoint** (they live on different
level curves).

## Statement A (the steering problem, as needed)

> **Prove or disprove:** for every such pair `(c₁, c₂)` there exists a parameter choice
> `r ∈ (a, b)` (and angular windows) such that the full tower piece for `r` — finitely
> many arcs on the levels `ℓ(r)/2^j`, `j = 0, …, J`, with `J` fixed by the construction —
> is **disjoint from `K₂`**.
>
> If false in general, characterize the exceptional pairs.

## Statement B (a clean model question implying the needed cases)

> Let `K ⊂ ℂ` be a compact, totally disconnected set which is the Julia set of `z² + c₂`
> (so it carries the standard self-similar structure), and let
> `Φ : (a,b) × [0,1] → ℂ` be a real-analytic injective map whose images
> `γ_r = Φ({r} × [0,1])` are pairwise disjoint arcs foliating an open region `Ω`.
> The **bad set** is `B = { r ∈ (a,b) : γ_r ∩ K ≠ ∅ }`.
> **Question:** is `B ≠ (a,b)` — i.e. does some leaf avoid `K`?

Note `B` is the projection to the `r`-coordinate of the compact set
`Φ⁻¹(K ∩ Ω)`; projections of totally disconnected compacta can be full intervals in
general (Cantor-function graphs), so pure point-set topology does **not** suffice.
The question is whether the *conformal/self-similar* structure of a Cantor Julia set
rules this out for *analytic level-curve* foliations.

## What is known (may be assumed; partially machine-verified)

1. **Dimension counting solves the thin case.** If `dim_H(K_{c₂}) < 1` (true for `|c₂|`
   large), then `B` has Hausdorff dimension < 1 (projections under the locally Lipschitz
   level map do not raise dimension), hence `B ≠ (a,b)`. **The open case is
   `1 ≤ dim_H(K_{c₂}) < 2`.**
2. **Zero area is not enough.** `K₂` has zero area, so by Fubini almost every leaf meets
   `K₂` in a set of zero length — but zero length is not empty, and the downstream
   application needs *empty*.
3. **Level-window hypotheses are provably useless.** No condition of the form
   "`K₂` avoids a `G₁`-level window `{0 < G₁ ≤ M}`" can hold for genuinely distinct
   parameters: the `G₁`-values on `K₂ ∖ K₁` are trapped below an explicit constant, and
   such windows always catch them. (This vacuity is machine-verified; the avoidance must
   be set-level, i.e. genuinely about *positions*, not potential levels.)
4. The arcs can additionally be perturbed in the *angular* direction — the family is
   really two-parameter; Statement A may exploit this while Statement B (one-parameter)
   is the harder, cleaner question.

## Likely attack routes

- **Harmonic measure / capacity:** `B`'s "size" is controlled by the harmonic measure of
  `K₂ ∩ Ω` seen through the foliation; Makarov-type dimension bounds for harmonic measure
  on Cantor Julia sets (dimension of harmonic measure ≤ 1, strictly < 1 + ε…) could beat
  the projection.
- **Self-similarity:** `K₂ ∩ Ω` is covered by boundedly many conformal copies of a fixed
  Cantor template; a leaf avoiding the template's gaps at every scale exists by a direct
  shrinking-target / Baire argument if gap-density is uniform (it is, for hyperbolic
  Cantor Julia sets — all disconnected quadratic Julia sets are hyperbolic on their Julia
  set? — the postcritically-infinite escape case is uniformly expanding on `J`: yes,
  `J = K` is a hyperbolic set when the critical orbit escapes). This route looks the most
  promising: **uniform expansion ⟹ K₂ is porous**, and porous sets have dimension < 2
  with *uniform gap structure*; a positive-density gap family along every leaf-transversal
  might force some leaf into gaps at all scales.
- **Transversality technology** from parametrized fractal geometry (Peres–Schlag):
  the family `γ_r` vs. the self-similar measure on `K₂`; transversality of the level-curve
  family would give `dim B ≤ dim K₂ − (transversality exponent)`… applicable if the
  foliation satisfies their axioms (real-analytic, non-degenerate — plausible).

## Acceptance criterion

A rigorous proof of Statement A for all disconnected pairs, **or** of Statement B for all
Cantor quadratic Julia sets `K` (equivalently: with `dim_H K ≥ 1`), **or** a
counterexample pair together with a characterization of when steering is possible.
Partial results for explicit parameter classes (e.g. both `c_i` real, or porosity-based
sufficient conditions) are directly usable.
