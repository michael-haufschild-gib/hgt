# LA — first Laguerre inequality of Ξ from the theta source: producer ladder

- **ID:** laguerre-anchor-producer-ladder
- **Stage:** 1-in-progress
- **Type:** hgtl7 conjecture loop (prove-or-kill per producer)
- **Source:** frontier LA; F0240, F382r; route-1/3 residuals
- **Target (open, strictly weaker than RH):** `L(t) = Ξ'(t)² − Ξ(t)Ξ''(t) ≥ 0` for every real `t`.

## Exact reformulation (P)
`Ξ(t) = ∫ Φ₀(u) cos(tu) du` with the even, positive theta kernel `Φ₀(u) = e^{u/2} Σ_n h(n² e^{2u})`,
`h(x) = (2π²x² − 3πx) e^{−πx}`. Symmetrising `u ↔ v` and using the evenness `v ↦ −v`:

`L(t) = ½ ∫∫ Φ₀(u) Φ₀(v) (u − v)² cos(t(u + v)) du dv = ∫ G(s) cos(ts) ds`,
`G(s) = ¼ ∫ Φ₀((s+d)/2) Φ₀((s−d)/2) d² dd`.

So Laguerre for all `t` ⟺ `G` is positive definite (Bochner). Also `L = −Ξ² (log|Ξ|)''`: Laguerre ⟺ `log|Ξ|` concave
between consecutive real zeros.

## Kill standard
A producer `P` (a property of the kernel) is killed only by a kernel with `P` whose `L` is negative somewhere,
or by proving an intermediate claim of the `P`-derivation false. When `P` pins `Ξ` down, only a proof remains.

## Ladder
| P | content | verdict |
|-|-|-|
| P₀ | positive, even, log-concave | KILLED (corpus countermodel) |
| P₁ | … | … |

## Log
- 2026-09-26 — created.
