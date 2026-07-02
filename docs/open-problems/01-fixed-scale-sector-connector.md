# Open Problem 1: The fixed-scale sector connector at a repelling boundary fixed point

> **STATUS (2026-07-02): REFUTED as stated — see `01-answer.md`.** The Statement below is
> **false** for the suggested parameter `c = −1.5436…` (and, by the same mechanism, for
> essentially every real dendrite parameter): the vertical Julia arc through the critical
> point pulls back along the β-fixed inverse branch to hairs whose Koenigs radius profile
> bulges *outward* (`|Φ(it)|² = A² + (B²−AC)t² + …` with `B²−AC ≈ 1.186 > 0`, verified here
> to 500 digits), producing crosscuts at radii `r ∈ (aₙ, μaₙ)`, `μ ≈ 1.031`, that trap shell
> points away from the sector at every scale. The λ-descent then defeats every `ρ₀`.
>
> **What survives.** The downstream consumer never needed the sector connector itself — only
> a shrinking preconnected family `T(t) ⊆ B(z₀,t) ∖ K` containing `B(z₀,t/2) ∖ K`, for all
> small `t`, at **some** tip `z₀` (factor-2 slack). The counterexample's own bulge factor
> `1.031 ≪ 2` does not refute that weaker form. The weakened problem — now a **fallback**,
> since the primary route moved to Problem 03 — is: *prove the factor-2 basis-family
> statement at some point of `J₁ ∖ K₂` off a countable exceptional set* (endpoint tips of
> the dendrite are the natural candidates; the full critical-subtree pullback extent is the
> quantity to control, measurable by the same `Φ`-recurrence used in the refutation).
>
> The original statement is kept below unchanged, for the record.

**Field:** one-dimensional complex dynamics (quadratic Julia sets, local structure).
**Self-contained:** no knowledge of the surrounding project is needed. A proof of the
Statement below (for any nonempty class of parameters `c`) is a complete solution.

## Setting

Fix a real parameter `c ∈ (−2, 0)` for which the filled Julia set
`K = K_c = { z ∈ ℂ : the orbit of z under f(z) = z² + c stays bounded }`
is **connected with empty interior** (a *dendrite*; e.g. any real Misiurewicz parameter such
as `c = −1.5436…`, where the critical orbit is strictly preperiodic).

Let `β = (1 + √(1 − 4c))/2` be the *repelling* fixed point of `f` with multiplier
`λ = f′(β) = 2β > 2`. Elementary facts (machine-verified already, may be assumed):

- `K ⊆ { |z| ≤ β }`, and `β ∈ J = ∂K`: `β` is the norm-extreme point of `K`
  (the landing point of the external ray of angle 0; the rightmost point of `K`).
- Consequently every `z ∈ K` has `Re(z − β) ≤ 0`, so the sector
  `S = { z : Re(z − β) > |z − β|/2 }` is disjoint from `K`.
- Let `ψ` be the Koenigs linearizer at `β`: the unique analytic map on a disk
  `{ |w| < ρ_ψ }` with `ψ(0) = β`, `ψ′(0) = 1`, and `ψ(λw) = f(ψ(w))`.
  Set `P = ψ⁻¹(K)` (defined near 0). Then `P` is **λ-invariant** (`v ∈ P ⇔ λv ∈ P`
  where both sides are defined), `0 ∈ P`, and `P ⊆ { Re v ≤ |v|² }` — so the sector
  `Σ = { v : Re v > |v|/2 }` is disjoint from `P` at every scale.

## Statement (the problem)

> **Prove:** there exists `ρ₀ ∈ (0, ρ_ψ)` such that for every scale `r ∈ [ρ₀/λ, ρ₀]`
> and every point `v ∉ P` with `r/λ² ≤ |v| < r`, there exists a **connected** set
> `C ⊆ { u : |u| < r } ∖ P`
> with `v ∈ C` and `C ∩ Σ ≠ ∅`.

In words: at **one fixed scale** near the fixed point, every basin point in the annular
shell can be joined, within the basin and without leaving the disk of that scale, to the
sector on the external-ray side.

An equivalent `z`-plane formulation (up to the bi-Lipschitz change of variable `ψ`, which
is tangent to the identity): every point of `(annulus around β of one fixed scale) ∖ K`
can be connected to the ray-side sector inside `(disk of that scale) ∖ K`.

## Why this is the whole problem (context, no proof needed by you)

A machine-checked *scale-collapse theorem* already reduces the a-priori-infinite family of
conditions "`B(β,ρ) ∖ K` is connected for **all** small `ρ`" to exactly the single-scale
Statement above: λ-invariance of `P` transports connectors across scales, and the sector
`Σ` (scale-invariant, `P`-free, convex) glues them. All the reduction machinery — the
linearizer, its tangency and open-mapping properties, the invariance, the sector location,
the collapse — is formally proven (Lean 4 / mathlib, axiom-clean). The Statement is the
only missing input. Downstream (also machine-checked), it yields an unconditional
algebraic-independence theorem for Böttcher coordinates of pairs of quadratic polynomials.

## What is known / likely attack routes

1. **Local connectivity route.** For real Misiurewicz (more generally finitely-renormalizable)
   parameters, `J_c` is locally connected (Yoccoz). Tree-like (dendrite) + locally connected
   should give: within the fixed-scale annulus, `K` decomposes into the real spine
   `[β − δ, β] ⊆ ℝ` plus countably many "decorations" attached at real points, with
   diameters → 0. If at the chosen scale all decorations that meet the annulus have diameter
   smaller than the annulus width times a constant, connectors exist by going around them.
   Needs a *quantitative* small-decoration statement at one scale — self-similarity under
   `z ↦ λz` (in ψ-coordinates) means one scale suffices.
2. **Distortion route.** Decorations near `β` are preimages under the (expanding) dynamics of
   decorations in a fundamental annulus far from `β`; Koebe distortion of the inverse
   branches bounds their diameter/position ratio. No local connectivity needed, only
   bounded distortion of univalent inverse branches along the ray.
3. **Harmonic-measure / external-ray route.** The sector contains the landing segment of
   the 0-ray. Connectors could follow level/gradient lines of the Green's function; the
   obstruction is precisely sub-continua of `K` separating a shell point from the ray
   within the disk — rule them out at one scale.

**Traps we already closed (do not spend time here):** the statement *cannot* be obtained
from any per-component or sector-only maximum-principle argument (single-branch coherence
across components of `B ∖ K` is exactly what it encodes); and no coordinate transfer
avoids it — the reduction to one scale is optimal in that sense.

## Acceptance criterion

A rigorous proof (paper mathematics is fine; formalization is our job) of the Statement
for **any** explicitly-described nonempty set of real dendrite parameters `c` — e.g. just
`c = −1.5436…` (the real Misiurewicz point with orbit −α → α), or all real Misiurewicz
parameters — with all constants effective or effectivizable.
