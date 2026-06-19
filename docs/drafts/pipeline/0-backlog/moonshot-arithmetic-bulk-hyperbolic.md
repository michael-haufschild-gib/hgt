# MOONSHOT — the arithmetic bulk: ζ is the Selberg zeta of a hidden hyperbolic 3-orbifold; RH = its hyperbolicity

- **ID:** moonshot-arithmetic-bulk-hyperbolic
- **Stage:** 0-backlog
- **Type:** MOONSHOT CONJECTURE (wild; ~10% true; far beyond SOTA)
- **Priority:** FIELDS MEDAL (+)
- **Source:** user directive 2026-06-19 (wild moonshots; "Think Holographic theory", CLAUDE.md); the explicit
  formula as a trace formula (#139), constraint-not-flow (#138), Connes' adele class space.
- **The wild claim.** The primes are a **boundary**; the zeros are a **bulk**; the explicit formula is a
  **holographic (Selberg-type) dictionary** between them — and there is an actual **geometric bulk** realizing it.

## The conjecture
> **Conjecture (arithmetic bulk).** There exists a 3-dimensional **hyperbolic orbifold (or a noncommutative
> 3-geometry)** `M` — a "bulk" dual to the prime "boundary" — such that the Weil explicit formula **is** the
> Selberg trace formula of `M`:
> - the **closed-geodesic length spectrum** of `M` is `{k·\log p}` (primes = boundary data);
> - the **Laplacian spectrum** of `M` is `{¼+γ_n²}` (zeros = bulk excitations).
> Then **RH ⟺ `M` is genuinely hyperbolic**: `spec(Δ_M)⊆[¼,∞)` (no exceptional small eigenvalues) ⟺ the bulk
> has uniform negative curvature. **Off-line zeros = small Laplacian eigenvalues = a "cusp"/degeneration of the
> bulk geometry** (the geometry develops a thin part). The critical line `Re=½` is the bulk's **conformal
> boundary** (the holographic screen); `Fix(ι)` (#127) is its boundary-at-infinity.

## Why ~10% plausible (not random)
- The explicit formula and the Selberg trace formula are **already structurally identical** (length spectrum
  ↔ primes, Laplacian ↔ zeros); the open part is whether a *single geometric `M`* realizes ζ (the Selberg zeta
  of a *fixed* surface is not ζ — that's the SOTA obstruction this leaps past).
- Connes' adele class space is a noncommutative "space" whose trace formula gives the explicit formula —
  candidate `M` (the moonshot: it has a genuine 3-geometry, not just a spectral triple).
- `spec(Δ)≥¼` ⟺ RH is exactly the **Selberg-eigenvalue / Ramanujan** form — `¼` is the same `¼` as `½(1−½)`.
- Ties RH to **3-manifold topology / hyperbolic geometry / the volume conjecture** — far from analytic NT.

## Attack / what would confirm or refute
1. Identify the candidate `M`: test whether Connes' adele class space carries a 3-dimensional hyperbolic
   structure (or whether the "arithmetic bulk" is the `BC`-system's modular flow geometry).
2. Check the dictionary on a **toy model** (a Beurling system with a *known* geometric dual) — does the
   length-spectrum↔Laplacian-spectrum match force `spec≥¼`?
3. **Refuted if** the trace-formula match provably cannot come from a 3-geometry (a no-go on the volume/curvature).
- Door: NATIVE if the bulk geometry is irreducibly the joint `(σ_p,∂_s)` (`∂_s`=the radial/holographic
  direction, `σ_p`=the boundary).

## Weyl-law test — PARTIAL REFUTATION + refinement (2026-06-19, Professor) `[showed teeth]`
A decisive near-term test was run. If `{¼+γ_n²}` were the Laplacian spectrum of a `d`-dimensional manifold,
the counting must obey `N(λ<Λ)~C·Λ^{d/2}`. The actual zero counting `N(γ<T)~(T/2π)\log(T/2π)` gives, in
`λ=¼+γ²`, `N(λ)~(√λ/2π)\log√λ`. Measured effective `d/2=\log N/\log λ`:
```
   T:     50     200    1000    5000    50000
   d/2:  0.287  0.413  0.469   0.494   0.511    →  1/2   (so d → 1)
```
**`d → 1`, not 2 or 3.** The zeros are far too **sparse** (sub-linear `√λ\,\logλ`) to be a finite **2D
surface** (`N~λ`) or **3D manifold** (`N~λ^{3/2}`) Laplacian spectrum — a full power off.
- **REFUTED:** the "finite hyperbolic **3-manifold** (or surface) bulk" form. ζ is **not** the Selberg zeta of
  a finite-volume hyperbolic manifold (the classical obstruction, here made quantitative).
- **REFINED (the surviving form):** the counting `N~γ\logγ` is exactly the **Berry–Keating `H=xp` (1D)** law
  (the `log` = the dilation/`xp` density) — so the "bulk" is **1-dimensional** (a quantum graph / the `xp`
  line), **or** the **non-compact, infinite-volume adelic space** (Connes' adele class space, type III), whose
  divergent volume *evades* the finite Weyl law and *produces* the extra `\log`. Both keep the moonshot's core
  (zeros = bulk spectrum, primes = boundary length spectrum, RH = `spec≥¼`) but the geometry is **1D-`xp` /
  adelic, not a 3-manifold**.
- **Net:** the holographic/Selberg core survives; the "3-manifold + curvature-hyperbolicity" specifics are
  refuted and replaced by "1D Berry–Keating / non-compact adelic bulk." `spec(Δ)≥¼ ⟺ RH` is unchanged (it is
  `γ` real). Verified: `computations/2026-06-19-arithmetic-bulk-weyl-law.py`.

## Cross-references
- `explicit-formula-as-constraint.md` (#139), `constraint-not-flow-theorem.md` (#138),
  `bucket-time-and-non-holonomic-time.md` (the WDW/holographic ingredients M2 RT/holography);
  `completed-connection-category.md` (#127, `D=∂_s`=`xp`/Berry–Keating, the 1D bulk this test points to).

## Log
- 2026-06-19 — Professor: filed as a moonshot (user directive). ζ as the Selberg zeta of an arithmetic
  hyperbolic 3-bulk; RH = `spec(Δ)≥¼` = hyperbolicity; off-line = cusp degeneration. Holographic steer made
  geometric.
- 2026-06-19 — Professor: **ran the Weyl-law test (showed teeth).** Measured effective dimension `d → 1`
  (d/2: 0.29→0.51 as T:50→50000). The zeros are too sparse for a 2D/3D manifold Laplacian — **the finite
  hyperbolic-3-manifold form is REFUTED**; refined to a **1D Berry–Keating `xp` / non-compact adelic** bulk
  (the `log` in `N~γ\logγ` = the `xp` density / the infinite adelic volume). Core (zeros=bulk spectrum,
  RH=`spec≥¼`) survives; the 3-manifold geometry does not. Computation archived. Genuine partial-refutation
  of my own moonshot via a clean test — the intended "figure out true/false."
- 2026-06-19 — Professor: **second teeth-test — GUE spacing statistics.** Parameter-free spacing ratio
  ⟨r⟩=0.614 for the first 160 zeros — squarely **GUE (0.603), far from Poisson (0.386)**. So the 1D bulk is
  **quantum-CHAOTIC, NOT integrable/lattice.** Together with the Weyl law (d→1), the bulk is pinned: a **1D
  quantum-chaotic system = the Hilbert–Pólya operator D=∂_s** (#127), RH = its PT-unbrokenness. "Chaotic, not
  integrable" is also the spectral-statistics echo of B18 (`hp-not-too-algebraic`: an algebraic/integrable HP
  operator would give Poisson). Computation: `computations/2026-06-19-zero-spacing-gue.py`.
