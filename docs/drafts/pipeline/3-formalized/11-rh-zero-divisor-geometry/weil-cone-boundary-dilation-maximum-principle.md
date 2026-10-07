# Boundary-class dilation rigidity by archimedean dominance and the maximum principle

- **ID:** weil-cone-boundary-dilation-maximum-principle
- **Stage:** 3-formalized (MUST-804)
- **Type:** THEOREM
- **Source:** loop rows 535–536; extends MUST-801 (`WeilConeInfiniteDilationRigidity`)
- **Statement:** Let `a, v : ℕ → ℝ` with `Σ |a(n)| n^{−1/2}(1 + log n) < ∞`, `Σ |v(n)| n^{−1/2} < ∞` and `v(0) = v(1) = 0`. Put `A(s) = Σ a(n) n^{−s}` and `V(s) = Σ v(n) n^{−s}`, both absolutely convergent on `Re s ≥ ½`. If `Λ ⋆ a + v` is full-cone Weil-positive, then `a = δ₁` and `v = 0`. Hence `Λ` is Weil-positive and RH holds. Within this class, a Weil-positive system exists iff RH.

## Lean
- `RHTower/WeilConeBoundaryDilationInequality.lean`: master identity on `Re s > ½`, `A(1) = 1`, the boundary inequality `0 ≤ (1 − Re A)θ' + Im A·Z'/Z` off zeros, the squared form `(Re A − 1)θ'Z² ≤ Im A·ZZ'` at every height, and the derivative of `t ↦ A(½+it)`.
- `RHTower/WeilConeBoundaryDilationLogAveraging.lean`: softened logarithm `L_η = ½log(Z²+η²)`, the integrated inequality after integration by parts, concavity bound from the mean square, Littlewood floor for `∫ L_η`, zero-free heights.
- `RHTower/WeilConeBoundaryDilationRigidity.lean`: almost-period excess windows, block lower bound, smooth-transition weight, numerical comparison, `re_lineSeries_le_one`, Phragmén–Lindelöf (`re_dilSeries_le_one`), maximum principle (`dilSeries_eq_one`), `eq_delta_of_weilPositiveFull_boundary`, `eq_vonMangoldt_of_weilPositiveFull_boundary` (`v = 0` from abscissa rigidity, `WeilAbscissa.eq_vonMangoldt_of_weilPositiveFull_of_rpow_summable`), `riemannHypothesis_of_weilPositiveFull_boundary`, `exists_boundaryDilation_weilPositive_iff`.
- Namespace `RHTower.WeilBoundaryDilation`; standard axioms only; wired after `WeilConeInfiniteDilationRigidity`.

## Why it is new
- MUST-801 needs absolute convergence on `Re s ≥ ½ − δ`: its proof uses analyticity across the line and zero counting. Here `A` may have a natural boundary at the line.
- No zero counting and no realness step. The archimedean phase velocity `θ' ~ ½ log t` dominates, in mean, the fluctuation of `log|ζ(½+it)|` (`O(T log log T)`), which forces `Re A ≤ 1` pointwise on the line.

## Paper proof (as formalized)
1. **Boundary inequality.** The master identity gives `Φ = G + 1/(s−1) + Aζ'/ζ − V` on `Re s > ½`, continuous up to every line point with `ζ ≠ 0`. With `ζ'/ζ(½+it) = −θ'(t) − iZ'/Z(t)` and the cancellation of the real parts of `1/s` and `1/(s−1)`, `Re Φ ≥ 0` gives `(Re A − 1)θ'Z² ≤ Im A·ZZ' − Re V·Z²` at every height.
2. **Softening.** For `η > 0` multiply by `w/(Z²+η²)`, with `w ≥ 0` a `C¹` weight, and integrate by parts against `L_η`, using `L_η' = ZZ'/(Z²+η²)`. Pointwise, `log η ≤ L_η ≤ ½log(1+Z²)`, `|L_η| ≤ log(1+Z²) − L_η`, and `η²/(Z²+η²) ≤ η + 2(½log(1+Z²) − L_η)/log(1/(2η))`. Averages: `∫ log(1+Z²) ≤ |I| log(1+M)` by tangent-line concavity with the mean square `M ≪ log² T`, and `∫ L_η ≥ ∫ log|ζ| ≥ −C − K log T₂` by Littlewood's floor, since `L_η ≥ log|Z|` off finitely many zeros.
3. **Excess forces mass.** If `Re A(½+it₁) > 1 + δ`, then by Bohr almost periodicity (an absolutely convergent exponential series) `Re A ≥ 1 + δ/2` on windows of fixed width in every block of length `L`. With `w = S((Re A − 1)/ε)` (`S` the smooth transition, `ε = δ/2`), `(Re A − 1)w ≥ 0` everywhere and `≥ ε` on the windows. So `∫_{T₁}^{T₂}(Re A − 1)θ'w ≥ κ T log T`, using `θ' ≥ ¼ log T`.
4. **Comparison.** Take `η = 1/T₂` with `T₁ ∈ [T, T+1]`, `T₂ ∈ [2T, 2T+1]`, zero-free horizontal segments. Every other term is `O(T log log T + log T)`; the regular part costs only `‖V‖_∞ T`. For large `T` this contradicts `κ T log T`, so `Re A ≤ 1` on the line.
5. **Interior.** Phragmén–Lindelöf for the bounded function `exp A(½ + z)` on the right half-plane gives `Re A ≤ 1` on `Re s ≥ ½`. `A(1) = 1` is an interior maximum of `|exp A|`, so `exp A` is constant, `A' = 0`, and `A ≡ 1`. Uniqueness of Dirichlet coefficients gives `a = δ₁`. Then `λ − Λ = v` has absolute abscissa `≤ ½ < 1`, and abscissa rigidity gives `v = 0`.

## Scope and limits
- Like MUST-801, this is a uniqueness theorem (U): it does not produce a Weil-positive element. Existence in the class is equivalent to RH.
- Not covered: Möbius parts `μ ⋆ f` with `f` infinite (parallel card `weil-cone-zeta-square-boundary-rigidity`, δ > 0), dilation series without the log moment, and non-multiplicative full-scale deviations.

## Log
- 2026-10-06: card created (Opus loop row 535). Paper proof complete.
- 2026-10-07: formalized (loop row 536). The formal route replaces realness plus product-Poisson weights by η-softening plus almost-period windows (pointwise `Re A ≤ 1` on the line) and Phragmén–Lindelöf. Moved to 3-formalized.
- 2026-10-07: extended to `Λ ⋆ a + v` with a boundary-regular part `v` (loop row 537). The extra term `−Re V·Z²` costs `O(T)` in the comparison; `v = 0` follows from abscissa rigidity once `a = δ₁`.
