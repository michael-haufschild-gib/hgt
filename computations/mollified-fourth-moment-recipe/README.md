# Mollified fourth moment `c₄(θ)` via the CFZ ratios recipe (symbolic multiple residues)

Setting: `Ψ_M(s) = ∑_{h ≤ y} μ(h) (log(y/h)/log y) h^{-s}`, `y = T^θ`, and
`c₄(θ) := lim (1/T)∫_T^{2T} |ζΨ_M(1/2+it)|⁴ dt`.

`engine.py` — the residue engine: integrand kept as `∑_key exp(key)·rational(w)` with `key` a linear
form; each term is closed on the side where its exponential decays (sign of `∂key/∂w` in the
regime `θ = 0.3`); residues at poles of any order by explicit Laurent coefficients; validated on
- `(K,L,Q,R) = (1,1,0,0)` → `1` (`∫|ζ|² ~ L`),
- `(2,2,0,0)` → `1/12` (fourth moment `L⁴/12` before the arithmetic factor `1/ζ(2)`),
- `(1,1,1,1)` → `1 + 1/θ` (Conrey's mollified second moment),
- the head `H_M = (1/log M)∑_{n≤M}Λ(n)n^{-s}` (sharp and smooth cutoffs): `E|H|² = 1/2, 1/12`,
  `E|H|⁴ = 1/2, 1/72` — the rigorous values (Lean `MollifiedDeviationHeadVariance`,
  `MollifiedDeviationHeadFourthMoment`; the smooth variant by the same proof), obtained only when the
  closure sides are decided in the regime `θ < 1/2` (deciding at `θ = 1/2` leaves the spurious term
  `−(1−2θ)⁴/(12θ⁴)`, the analytic continuation of the `θ > 1/2` off-diagonal phase).

`recipe2.py`, `adjudicate.py` — the mollified moments; `adjudicate.py` recomputes `(2,2,2,2)` with
the shift limit before and after the residues, three integration orders, two shift directions:
all twelve agree (`adj_out.txt`).

Result:
```text
c₄(θ) = 1 + 8/(3θ) + 2/θ² + 2/(3θ³)      (recipe; rigorous main terms in Hughes–Young's range θ < 1/11)
```
Gaussian `CN(0,1/θ)` would give `1 + 4/θ + 2/θ²`; the two agree only at `θ = 1/√2`.

`c4_out.txt` is the FIRST (buggy, `sympy.residue`-based) engine's output giving `(1+1/θ)²`; it is
kept as a record of the bug: that value is excluded by the Littlewood/outer identity (see the card).

`moll_test.py`, `moll_scaling.py`, `scaling_out.txt` — Riemann–Siegel numerics at `T = 10⁵, 10⁶, 10⁷`:
`E|ζΨ|⁴/(E|ζΨ|²)²` = `1.997, 2.060, 2.110` (θ = 1/2) and `2.265, 2.346, 2.417` (θ = 0.4),
rising toward the recipe's `2.185` and `2.498`; `E log|ζΨ|² ≈ 0` throughout; `P(|ζΨ|² < 0.1) ≈ 0.12`
stable.
