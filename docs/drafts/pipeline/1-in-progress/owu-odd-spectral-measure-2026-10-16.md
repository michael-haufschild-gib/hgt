# OWU: the odd Weil functional is the spectral integral of its Nevanlinna measure

- **ID:** owu-odd-spectral-measure
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) → THEOREM (Lean) in progress
- **Source:** docs/reports/rh-current-frontier-map.md, route OWU; successor of
  `3-formalized/owu-square-root-herglotz-transfer-2026-10-16.md`
- **Statement:** For odd Weil-positive `lam` with Nevanlinna data `(Ψ, ν, c)` of the squared-variable
  Weil function, every odd `C²` compactly supported `f` satisfies
  `Re W_lam(f ⋆ f̃) = ∫ Θ_f(ζ) dν(ζ)` with `Θ_f ≥ 0` continuous,
  `Θ_f(ζ) = (1 + γ²)|f̂(√γ)|²/γ` on the critical ordinates `γ > 0`,
  `Θ_f(ζ) = (1 + γ²)|f̂(i√|γ|)|²/|γ|` on the cut `−¼ ≤ γ < 0`, `Θ_f(1) = 0`.
  Consequences: the odd cone is exactly the set of weights whose Weil function has a slit
  continuation with the squared-variable sign law (odd Herglotz bridge), and the Nevanlinna
  measure is integrable against `1/|γ|` near the centre (central regularity).

## Goal

The full-cone uniqueness theorem rests on the Bochner boundary measure of the full functional.
The odd cone had no spectral measure; the Pick continuation was a surrogate. This card supplies the
odd spectral measure: the Nevanlinna measure of `g(z) = aΨ(½ + a)`, `z = a²`, represents the odd
functional on every compactly supported odd test, not only on the exponential family. The cut
enters with the positive weight `|f̂(ic)|²`, so no odd test can see it; the constant `c` of the
representation and the point `ζ = 1` are invisible to odd tests. This makes exact which data the
odd cone controls.

## Paper proof

1. (Representation on the whole line.) For `a` in the first quadrant
   `a Ψ(½ + a) = ∫ k(a², ζ) dν − c`, `k(z, ζ) = i K(½ − iz, ζ)`. The kernel has real coefficients:
   `K(½ + iā², ζ̄) = −K(½ − iā², ζ)` for `|ζ| = 1`, so `conj k(z, ζ) = k(z̄, ζ)`; with
   `Ψ(s̄) = conj Ψ(s)` (identity theorem on the quadrants) the same formula holds on the fourth
   quadrant. Hence on the line `w = 5/4 + it`, `t ≠ 0`:
   `Ψ(w) = ∫ K_ζ(w) dν(ζ) − c/(w − ½)`, `K_ζ(w) := k((w − ½)², ζ)/(w − ½)`.
2. (Kernel bound.) On the support `{ζ = 1} ∪ {−¼ ≤ γ}` and the line `w = 5/4 + it`:
   `K_ζ(w) = (γa² − 1)/(a(a² + γ))`, `a = ¾ + it`, with `|a² + γ| ≥ max(3|t|/2, 1/16 for |t| ≤ ½)`,
   so `|K_ζ(w)| ≤ C₀(1 + t²)` uniformly; `K_1(w) = a`.
3. (Fubini.) `W_lam(f ⋆ f̃) = (1/2π)∫ F(t) Ψ(5/4 + it) dt` (`weilFullFunctional_eq_line_integral`),
   `F(t) = H(5/4 + it) + H(1 − 5/4 − it)`, `|F| ≤ 2D/(1 + t²)²`. The product is integrable on
   `volume × ν|_support`, and the `c`-term is `c · (1/2π)∫ F(t)/(w − ½) dt = c · H(½) = c|f̂(0)|² = 0`
   for odd `f` (`two_line_pair` at `z₀ = ½`).
4. (Per-point evaluation.) Put `Θ_f(ζ) = Re[(1/2π)∫ F(t) K_ζ(5/4 + it) dt]`. For `ζ ≠ ±1`,
   partial fractions `K_ζ(w) = −1/(γ(w − ½)) + ((1 + γ²)/(2γ)) g_{z_γ}(w)`, `z_γ = ½ + √(−γ)`
   (principal branch: `½ + i√γ` for `γ > 0`, `½ + √|γ|` for `γ < 0`), and `two_line_pair` give
   `Θ_f(ζ) = ((1 + γ²)/(2γ)) Re[H(z_γ) + H(1 − z_γ)]`; on the critical ordinates
   `H(½ ± i√γ) = |f̂(±√γ)|²`, on the cut `H(½ ± c) = f̂(∓ic) conj f̂(±ic) = −|f̂(ic)|²` for odd `f`.
   At `ζ = 1`, `Re` of the linear term vanishes (`re_integral_line_weilTest_linear`).
   `Θ_f` is continuous on the circle (dominated convergence with the bound of step 2), nonnegative
   off `{±1}`, hence nonnegative at `−1`.
5. (Conclusions.) `Re W_lam(f ⋆ f̃) = ∫ Θ_f dν ≥ 0`. Conversely, every holomorphic slit
   continuation with the sign law yields such a `ν` and hence odd positivity (bridge). Taking `f`
   odd with `f̂′(0) ≠ 0`, `Θ_f(ζ) → |f̂′(0)|²` as `γ → 0`, so `∫_{0<|γ|<δ} dν/|γ| < ∞`.

## Gates
- [x] 0 → 1  well-posed, source-pure, attack idea fixed
- [ ] 1 → 2  paper proof above
- [ ] 2 → 3  Lean module `OddWeilSpectralMeasure`

## Log
- 2026-10-16 — created; paper proof; Lean formalization started
