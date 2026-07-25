# The Cusp–Spectrum Radius Law for the Selberg class

- **ID:** cusp-spectrum-radius-law
- **Stage:** 2-fully-proven (paper proof complete; independent of Selberg's conjectures)
- **Type:** THEOREM (paper)
- **Source:** `../1-in-progress/selberg-orthogonality-working-log.md` §§13.1, 14.1, 23.1, 24.2, 25
- **Statement:** the shift-lattice expansion of the degree-`d` theta function of `F ∈ S^♯` at any
  base point has radius of convergence exactly the distance from that point to the rest of the
  standard-twist spectrum; at the cusp this reads `d q^{−1/d}`.

## Statement

Let `F ∈ S^♯` have degree `d ≥ 1` and conductor `q`. Put
```
Φ_F(s,z) := Σ_{n≥1} a_F(n) n^{−s} e(z n^{1/d})        (z ∈ H),
F_α(w)   := Σ_{n≥1} a_F(n) n^{−w} e(−α n^{1/d})       (the K–P standard twist; F_0 = F),
Δ(α₀)    := dist( α₀ , Spec(F) \ {α₀} ) ,             Spec(F) = { d(m/q)^{1/d} : a_F(m) ≠ 0 }.
```

> **Theorem.** For every `s ∈ C` off the exceptional lattice `{s*_ℓ + k/d}` and every `α₀ ≥ 0`,
> ```
> limsup_{k→∞} | F_{α₀}(s − k/d) / k! |^{1/k}  =  1 / ( 2π Δ(α₀) ) .
> ```
> Equivalently, `Φ_F(s, −α₀+ζ) − (explicit singular part at α₀) = Σ_{k≥0} ((2πiζ)^k/k!) F_{α₀}(s−k/d)`
> with radius of convergence exactly `Δ(α₀)`.
>
> **Cusp case.** Since `a_F(1) = 1`, `Δ(0) = min Spec(F) = d q^{−1/d}`, so
> `limsup_k |F(s−k/d)/k!|^{1/k} = q^{1/d}/(2πd)`.

## Proof

1. **The expansion.** Mellin–Barnes: `e^{−x} = (2πi)^{−1}∫_{(c)}Γ(u)x^{−u}du` with
   `x = −2πiζ·n^{1/d}` (legitimate, `Re(−2πiζ) = 2π Im ζ > 0`) gives, for `c` large,
   `Φ_F(s,−α₀+ζ) = (2πi)^{−1}∫_{(c)} Γ(u)(−2πiζ)^{−u} F_{α₀}(s+u/d) du`.
   Shifting to `Re u = −M` crosses `u = 0,−1,−2,…` (poles of `Γ`, giving the displayed power series)
   and the poles of `F_{α₀}` — at `u = d(1−s)` when `α₀ = 0` (the pole of `F` at `1`, giving `P_F`),
   at `u = d(s*_ℓ − s)` when `α₀ ∈ Spec(F)` (giving the `ℓ`-sum with exponents `d(s−s*_ℓ)`).
   The singular part is singular only at `ζ = 0`.
2. **Radius = distance to the nearest other singularity.** `Φ_F(s,·)` is holomorphic on `H`;
   by K–P it continues across every boundary point `−α` with `α ∉ Spec(F)` (there `F_α` is entire in
   `s`), and by the jump lemma it is genuinely singular at `−α` for `α ∈ Spec(F)`:
   `sup_{|s−s*_0|=r}|F_{α}(s) − F_{α'}(s)| ≥ |ρ_0(α)|/r > 0` for all `α' ∉ Spec(F)`, because
   `∮ F_{α'} = 0` while `∮ F_α = 2πi ρ_0(α) ≠ 0` (K–P: `ρ_0(α) ≠ 0` on the spectrum).
   Hadamard's formula for the radius then gives the stated `limsup`.
3. **Cusp constant, independently.** By the functional equation and uniform Stirling, for `σ → −∞`
   with `t` fixed, `|X(σ+it)| ≍ C[q/(2π)^d]^{|σ|}|σ|^{d|σ|}e^{−d|σ|}` and `|F(1−s)| → 1`; with
   `|σ| = k/d + O(1)` and `k! ≍ (k/e)^k` this yields `|F(s−k/d)/k!|^{1/k} → q^{1/d}/(2πd)`,
   matching `1/(2πΔ(0)) = q^{1/d}/(2πd)`. The two computations use **disjoint data** — the first only
   the archimedean invariants, the second only `a_F(1)=1` and the location of the first prime-side
   singularity — so their agreement is a local–global identity.

## Verifications (all exact, with constants)

| `F` | `d` | `q` | predicted radius | independent check |
|---|---|---|---|---|
| `ζ` | 1 | 1 | 1 | Lerch `Σ n^{−s}e(nz)` singular exactly on `Z` ✓ |
| `L(·,χ)`, `χ` mod `q` | 1 | `q` | `1/q` | singularities on `(1/q)Z` ✓ |
| `L(·,Δ)` level 1 | 2 | 1 | 2 | `Γ`-computation gives `limsup = 1/(4π)` ✓ |
| level-1 Maass, any `r` | 2 | 1 | 2 | `Γ_R Γ_R` computation gives `1/(4π)`, independent of `r` ✓ |

## Consequences

- **Lower bound on the far-left growth of the standard twist.** `Δ(α_m) ≍ q^{−1}(α_m/d)^{1−d} → 0`
  for `d ≥ 2`, so `limsup_k |F_{α_m}(s−k/d)/k!|^{1/k} ≍ q(α_m/d)^{d−1}/2π → ∞`. K–P's upper bounds on
  `F(s,α)` **must** degrade in `α`, at the reciprocal of the local spectral spacing.
- **Radius 0 for the degree-1 shift lattice when `d ≥ 2`.** The same computation with spacing `1`
  gives `k`-th term `≍ (d^d k^{d−1}|2πz|)^k`. This is the quantitative reason Dirichlet-character
  twists (built from additive characters in `n`) are available in degree 1 and open beyond: the
  standard twist supplies additive characters in `n^{1/d}`, and matching them would need
  `α ∝ n^{1−1/d}`, not a constant.

## Novelty

Searched (2026-07): K–P's twist papers (arXiv:1911.10497, 1304.4734, 1507.07177, 2303.02417/20),
the degree-2 conductor-1 classification (arXiv:2009.12329, 2503.02492), the Annals `1<d<2` paper,
and the surveys (Dixit, Zheng, Perelli, Kaczorowski). No statement of this shape found. Both
ingredients are standard; the combination and the sharp two-sided radius are the new item.
Recorded as **plausibly new, not certainly new**.

## Relation to Selberg's conjectures

Independent of them. It does not advance Conjecture B — the three structural obstructions recorded
in the working log (§9.1, §10.1, §20.4) are untouched — but it supplies the exact `α`-dependence any
spike-type analysis of the standard twist needs.

## Log
- 2026-07-25 — proved (cusp case), sharpened to two-sided, unified over base points, verified on all
  four families with explicit constants.
