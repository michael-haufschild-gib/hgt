# Galois theory of the zeros — programme card (review-1211 §2.19)

- **ID:** gtz-programme
- **Stage:** 1-in-progress
- **Type:** programme
- **Source:** `docs/reports/review-1211/obstacles-summary.md` §2.19
- **Lean:** `formal/GaloisForLFunctions/GaloisTheoryOfZeros/` (umbrella `GaloisTheoryOfZeros.lean`)
- **README:** `formal/GaloisForLFunctions/GaloisTheoryOfZeros/README.md`

## Questions and status

| # | Question | Status |
|---|---|---|
| Q1 | orbit of a zero with irrational real part over `B`; an automorphism besides conjugation | open; orbit lies in the quartet; rational real part settled |
| Q2 | `[L:K] ∈ {1,∞}` | open; contains B13 |
| Q3 | square-class relations among the radicands `−δ_q²` | open |
| Q4 | group of one Jensen polynomial over its coefficient field | open; generic centred group is `S_d` (HTGeometry) |
| Q5 | monodromy of the heat family at a collision, group generated, relation to conjugation | in progress (below) |
| Q6 | a restriction from the prime traces forcing `H = B` | open; equivalent to RH |

## Q5: local monodromy of the heat cover (in progress)

Objects. `H_τ(z) = ∫ Φ(x) e^{τx²} e^{izx} dx` for complex `τ` (`complexHeat`); for real `τ` this is
`riemannHeat`. A collision is `(τ₀, z₀)` with `z₀` a zero of exact order `m ≥ 1` of `H_{τ₀}`;
`a = H_{τ₀}^{(m)}(z₀) ≠ 0`. `Q_m = heatModelFwd m = e^{−D²}σ^m`, with `m` simple real roots
(`√2 ·` roots of the Hermite polynomial), symmetric under `σ ↦ −σ`.

Paper proof.

1. *Blow-up without division.* With `X = ix`, `W(x) = Φ(x)e^{τ₀x²}e^{iz₀x}`,
   `H_{τ₀+s²}(z₀+sy) = ∫ W e^{u}`, `u = sX(y − sX)`. Write `e^u = Σ_{n<m} u^n/n! + u^m e_m(u)`,
   `e_m` entire, `|e_m(u)| ≤ e^{|u|}`. Expand `u^n = Σ_j C(n,j)(−1)^j y^{n−j} s^{n+j} X^{n+j}`. The
   moments `∫ W X^k = H_{τ₀}^{(k)}(z₀) = a_k` vanish for `k < m`. Hence
   `H_{τ₀+s²}(z₀+sy) = s^m G(y,s)`,
   `G = Σ_{n<m} Σ_{j≤n, n+j≥m} C(n,j)(−1)^j/n! · y^{n−j} s^{n+j−m} a_{n+j}
        + ∫ W X^m (y − sX)^m e_m(sX(y − sX)) dx`.
2. *`G` is entire in `(y,s)`.* The polynomial part is. The integral is continuous and holomorphic
   on every complex line: the integrand is entire and locally bounded by
   `Φ(x)e^{(|τ₀|+R²)x²}|x|^m(R+R|x|)^m e^{(|z₀|+R²)|x|}`, which is integrable. Continuous +
   line-entire ⇒ analytic (`HTGeometry.analyticOnNhd_of_continuous_affineLineEntire`).
3. *`G(y,0) = (a/m!) Q_m(y)`.* At `s = 0` only `n + j = m` survives: `j = k`, `n = m − k`,
   coefficient `(−1)^k/(k!(m−2k)!)`, `1 ≤ k ≤ m/2`; the integral gives `a y^m/m!`.
4. *Branches.* `∂_y G(ρ,0) = (a/m!) Q_m′(ρ) ≠ 0` at each root `ρ`. The analytic implicit function
   theorem gives `y_ρ` analytic at `0`, `y_ρ(0) = ρ`, `G(y_ρ(s), s) = 0`, unique among continuous
   branches. Hence `H_{τ₀+s²}(z₀ + s y_ρ(s)) = 0`.
5. *Monodromy.* `G(−y,−s) = (−1)^m G(y,s)` (both sides analytic; equal for `s ≠ 0` since
   `H_{τ₀+s²}(z₀+sy)` is invariant under `(y,s) ↦ (−y,−s)`). So `s ↦ −y_ρ(−s)` is a branch
   through `−ρ`: `y_{−ρ}(s) = −y_ρ(−s)`. One turn of `τ` around `τ₀` is `s ↦ −s`; it sends the
   zero `z₀ + s y_ρ(s)` to `z₀ + s y_{−ρ}(s)`. The local monodromy is the reflection `ρ ↦ −ρ` of
   the Hermite roots: `⌊m/2⌋` transpositions, order two for `m ≥ 2`.
6. *Conjugation.* For real `τ₀`, `z₀`: `G(ȳ, s̄) = conj G(y,s)`, so `y_ρ(s̄) = conj y_ρ(s)`. Real
   `s` (after the collision): all `m` zeros real. `s = iσ` (before): `conj(z₀ + iσ y_ρ(iσ)) =
   z₀ + iσ y_{−ρ}(iσ)`. Conjugation before the collision is the local monodromy.
7. *Exhaustion.* For `0 < |s| < r` the zeros of `H_{τ₀+s²}` in a fixed disc around `z₀` are
   exactly the `m` distinct points `z₀ + s y_ρ(s)`.

Lean plan: `TheHeatCoverOfTheZeros` (1–3), `TheHermiteMonodromyOfACollision` (4–6),
exhaustion (7) after.

## Conjecture log

(none failed yet)

## Log
- 2026-11-12 — card created; README restructured to the §2.19 frame; Q5 paper proof written.
