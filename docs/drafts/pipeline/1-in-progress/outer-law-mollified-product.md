# Outer law for the mollified product `ζΨ` (OUTER-001)

**Label:** conjecture-in-progress. **Started:** 2026-09-05. **Parent:** MOLL-DEV-001 (MUST-207).

## 1. Statement found

Let `Ψ_M(s) = ∑_{h≤M} μ(h) (log(M/h)/log M) h^{-s}` (linear mollifier) and, for any Dirichlet
polynomial `D` with `D(∞) = 1`, `ℓ_D(T) := (1/T)∫_T^{2T} log|D(1/2+it)|² dt`.

**Outer decomposition law.** `ℓ_{ζΨ_M}(T) = ℓ_ζ(T) + ℓ_{Ψ_M}(T)` with
- `ℓ_ζ(T) = (4π/T)∑_{β>1/2, T<γ<2T}(β−1/2) + O(log T/T) ≥ −o(1)` (Littlewood; the `(L)` mass),
- `ℓ_{Ψ_M}(T) = (4π/T)∑_{Ψ_M(ρ)=0, β>1/2}(β−1/2) + O(1/T) ≥ −o(1)` (Littlewood for the polynomial),
- `ℓ_{Ψ_M}(T) → J_M := E_χ log|∑_{h≤M} μ(h)P(h)χ(h)h^{-1/2}|²` (Steinhaus/torus Jensen mass of the
  multilinear polynomial `F_M(z) = ∑ μ(h)P(h)z^{v(h)}h^{-1/2}` on the polydisc; Bohr–Jessen–Tornehave
  for fixed `M`), and `J_M ≥ 0` with equality iff `F_M` has no zeros on the polydisc skeleton.

Hence `(L) ⟺ ℓ_{ζΨ_M}(T) − ℓ_{Ψ_M}(T) → 0`, and for every `M` with `J_M = 0`:
`(L) ⟺ ℓ_{ζΨ_M}(T) → 0` (the outer law proper). The previous card's "outer law" `ℓ_{ζΨ} → 0`
therefore holds iff `(L)` and `J_M → 0`.

## 2. The mollifier part is a computable deterministic quantity

Torus Monte Carlo (pod, `scratchpad/moll/torus_jensen.py`, exact last coordinate via
`E_z log|A+zB|² = log max(|A|,|B|)²`):

| M | linear `J_M(1/2)` | sharp Möbius sum `J_M(1/2)` |
|---|---|---|
| 10² | −0.001 ± 0.002 | 0.343 ± 0.003 |
| 10³ | −0.004 ± 0.003 | 0.432 ± 0.003 |
| 10⁴ | −0.005 ± 0.005 | 0.497 ± 0.006 |

The flow means agree (`psi_zeros.py`, `T = 10⁵, 10⁶`): linear `ℓ_Ψ(1/2) = 0.001–0.004`, sharp
`0.28–0.43`; the profile `ℓ_Ψ(σ)` shows the linear mollifier's zeros sit at `σ ≲ 0.4`, the sharp
sum's spread across `σ ≤ 0.7`.

Reading: the smoothing `P(h) = log(M/h)/log M` is what makes the mollifier (nearly) outer. Peeling
a prime `p` (`F` is multilinear since `μ` is supported on squarefree `h`):
`J(F) = J(F|_{z_p=0}) + E log⁺(|∂_pF|/|F|_{z_p=0}|)` exactly, and `∂_pF/F|_{z_p=0} ≈ p^{-1/2}(1 +
O(log p/log M))` for the linear weights, so the excess is charged only on the small-ball event
`|F|_{z_p=0}| ≲ log p/log M`, of log-normal probability `≈ 1/log M`; for the sharp weights the
ratio is `p^{-1/2}·|S_{M/p}|/|S_M|` with an `O(1)` increment, giving `∑_p O(1/p) ≍ log log M`
(observed slope `≈ 0.5` per unit of `log log M`).

Strict positivity: `F_M(r·𝟙)` is real with `F_M(0) = 1` and `F_M(𝟙) = ∑_{h≤M}μ(h)P(h)/√h →
1/ζ(1/2) < 0` (Riesz mean of `1/ζ` at `1/2`, conditional), so `F_M` has a real zero on the diagonal
at `r* ≈ log M/(2√M)`; `J_M > 0` but the diagonal has exponentially small weight. Small `M` is
exact: `M ≤ 7` linear gives `J_M = 0` (each peeled ratio `< 1` pointwise), while the sharp sum has
`J > 0` already at `M = 3` (corpus `torusAverage_log_norm_three_pos`).

## 3. Sharpened `(L)`

`(L) ⟺ ∀a>0: N(1/2 + a/log T, T) = o(T log T)` — zeros at a fixed multiple of the mean spacing
off the line are a vanishing proportion. Selberg gives `≪ e^{−a/4} T log T` (a bounded proportion
at fixed `a`), which is `∑(β−1/2)⁺ = O(T)`. So the outer law is exactly the fixed-scale zero
density at the mean spacing; the mollified log-mean `ℓ_{ζΨ}` is its analytic avatar.

## 4. Plan (Lean)

1. `MollifierLittlewoodFloor`: `ℓ_{Ψ}(T) ≥ −C/T` for a bounded Dirichlet polynomial with `b 1 = 1`
   (corpus entire weighted Littlewood rectangle, right edge `σ₀` with `|Ψ − 1| ≤ 1/2`).
2. `TorusJensenPeeling`: peeling identity and `J ≥ 0` for multilinear torus polynomials; `J = 0`
   for the linear mollifier at small `M`.
3. `DirichletPolynomialTorusLaw`: `limsup_T ℓ_D(T) ≤ J_D` (truncation `log max(|D|,ε)` +
   Kronecker–Weyl equidistribution of `(t log p)_p` + monotone convergence), and the lower bound via
   the area-averaged law and Littlewood monotonicity in `σ`.
4. Assemble: `ℓ_{ζΨ} − J_M − o(1) ≤ ℓ_ζ ≤ ℓ_{ζΨ} + o(1)`.

## 5. Open core

`[OPEN CORE]` `(L)` itself (`ℓ_ζ → 0`); and `J_M → 0` for the linear mollifier (small-ball
estimates for the random mollifier sum; Carbery–Wright-type anti-concentration is far too weak,
log-normal small-ball tails are needed).

## 6. Lean (2026-09-05, all axiom-clean, wired after `MollifiedDeviationHeadFourthMoment`)

* `MollifierLineLogMeanFloor`: `exists_edPoly_line_logMean_floor` — for a real unit-head bounded
  Dirichlet polynomial, `−(C + K log Mb) ≤ ∫_{T₁}^{T₂} log|Ψ(1/2+it)| dt`, **uniformly in the
  heights** (Littlewood rectangle for `Ψ` alone; generic far-right `O(1)` lemmas; the edPoly
  horizontal-edge bound with the trace `‖Ψ(4±iT)‖ ≥ 5/16`).
* `DirichletPolynomialTorusLogUpperLaw`: `tendsto_contMoment_average_steinhaus` /
  `tendsto_contMoment_window_steinhaus` — for every continuous `φ`, the time average of
  `φ(|F|²)` (Cesàro or on `[T,2T]`) converges to the Steinhaus expectation (Weierstrass on top of
  the corpus even-moment Bohr tower); `eventually_window_logMean_dpoly_le` — the torus upper law
  `(1/T)∫_T^{2T} log|F| ≤ ½E_χ log max(|F_χ|², ε²) + η` eventually (zeros of `F` on the window
  are finite, so the continuous majorant works a.e.).
* `OuterDecompositionLawMollifiedProduct`: `integral_log_norm_zeta_mul_edPoly_line`
  (`ℓ_{ζΨ} = ℓ_ζ + ℓ_Ψ` on any segment, heights `≥ 20`);
  `exists_zetaLine_logMean_le_mollifiedProduct_logMean` (**producer direction**:
  `ℓ_ζ ≤ ℓ_{ζΨ} + C + K log Mb` — any outer law `ℓ_{ζΨ} = o(T)` forces `(L)`);
  `eventually_window_logMean_zeta_mul_linearMollifier_le` (**receiver direction**, linear
  mollifier: `ℓ_{ζΨ_M}(T,2T) ≤ ℓ_ζ(T,2T) + T(J_M(ε) + η)` eventually, with
  `J_M(ε) = linearMollifierTorusLogMean M ε` the truncated torus Jensen mass).

So the outer law is proven as the exact **decomposition law** with both one-sided torus/Littlewood
bounds; the vanishing statement `ℓ_{ζΨ} → 0` is equivalent to `(L)` (given `J_M → 0`) and stays
open, and `J_M → 0` for the linear mollifier is supported numerically (`≤ 0.005` up to `M = 10⁴`)
and heuristically (small-ball events of probability `≈ 1/log M`).

## 7. Open core (after the Lean pass)

`[OPEN CORE]` (i) `(L)` itself; (ii) `J_M → 0` for the linear mollifier (small-ball law of the
random mollifier sum at scale `log p/log M`; negative-moment/Carbery–Wright routes are far too
weak); (iii) the **lower** torus law `liminf ℓ_Ψ(T,2T)/T ≥ J_M` (needs uniform integrability of
`log⁻|Ψ|` on the line: Poisson–Jensen on discs with the `≪_M T` zeros of the strip gives
`∫(log⁻|Ψ|)² ≪_M T`; not formalized), which would upgrade the receiver direction to the exact
equivalence `(L) ⟺ lim ℓ_{ζΨ_M}(T,2T)/T = J_M` for each fixed `M`.
