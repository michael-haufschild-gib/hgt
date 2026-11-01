# Lattice Section Theory of the scaling surface (LST)

- **ID:** lst-programme
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-0111/obstacles-summary.md §2.7, Q1–Q3, B25, B39, B40
- **Statement:** sections of the scaling surface as Gaussian lattice counts; Serre duality as
  Poisson summation; `h¹ = Künneth part + ½ Weil defect`; definite counts are fakes; the split
  surface selects through boosts; the even Hodge defect is the primitive `h¹` index.

## Goal
Answer the 2.7 questions with Lean theorems; isolate the primitive `h¹` as the single missing count.
Lean folder `formal/GaloisForLFunctions/LatticeSectionTheory/`, umbrella `LatticeSectionTheory.lean`.

## Gates
- [x] 0 → 1  in-progress: README first draft, pillar list
- [ ] 1 → 2  paper proofs of the pillars (below)
- [ ] 2 → 3  Lean modules for each pillar, checked with `lake --old env lean`

## Pillars and paper proofs

1. **Lattice Riemann–Roch + slope law.** HTGeometry `latticeTheta_inversion` gives
   `θ_L(t) = c t^{−r/2} θ_{L*}(1/t)`. Monotonicity of `θ_{L*}` gives `θ_L(t) ≤ (t'/t)^{r/2} θ_L(t')`
   for `t ≤ t'`, i.e. `h⁰(L,d) − h⁰(L,d') ≤ r(d − d')`.
2. **Künneth RR.** `u = h⁰(−a)`, `v = h⁰(−b)`, `h⁰(a) = a + u`, `h⁰(b) = b + v`:
   `h⁰(a)h⁰(b) + uv − ab = v·h⁰(a) + u·h⁰(b) > 0`. With `x² = 2ab − δ(x,x)` (`a = x·H`, `b = x·V`):
   `h(x) + h(−x) − ½x² = h¹_K + ½δ`. RI ⇔ HI (scale primitive `x` by `n`). Degree levels: base
   count `≤ 3 exp(−π e^{−2d})` for `d ≤ 0`.
3. **Epstein fake.** `θ_y(t) = θ(t)θ(y²t)`, `θ_y(1/t) = (t/y) θ_{1/y}(t)`.
   `Λ_y(s) = ∫_1^∞(θ_y−1)t^{s−1} + y^{−1}∫_1^∞(θ_{1/y}−1)t^{−s} + 1/(y(s−1)) − 1/s`.
   At `s = ½`: `θ_{1/y}(t) − 1 ≥ θ(t/y²) − 1 ≥ y t^{−1/2} − 1` on `[1, y²]`, so the dual term
   `≥ 2 log y − 2 + 2/y`; total `> 0` for `y > e²`. As `s → 1⁻`, `1/(y(s−1)) → −∞`, other terms
   bounded. IVT ⇒ zero in `(½, 1)`.
4. **Siegel majorant.** `A = H + V`: `(x·A)² − x² = a² + b² + δ(x,x)`. Convergence of
   `Σ e^{−πtQ(n)}` on `ℤ^k` ⇔ `Q` positive definite (negative or null rational direction ⇒
   infinitely many terms bounded below).
5. **Boost selection.** `∫(Ae^{2u} + Be^{−2u})^{−s}e^{2wu}du = ½(AB)^{−s/2}(B/A)^{w/2} c₀(s,w)`,
   `c₀ = ∫_0^∞ (y + 1/y)^{−s} y^{w−1} dy`; Tonelli over `m, n ≥ 1`.
6. **Primitive index** = negative index of `δ` on primitive part = Hodge defect (ACS Pontryagin).

## Log
- 2026-11-01 — created in 1-in-progress with README first draft
