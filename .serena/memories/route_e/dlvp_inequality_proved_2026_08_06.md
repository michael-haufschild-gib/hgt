# The de la Vallée Poussin inequality is proved

`RHTower/Sieve/DeLaValleePoussinInequality.lean` — `dlvp_inequality`, unconditional
(`[propext, Classical.choice, Quot.sound]`). Card:
`docs/drafts/pipeline/1-in-progress/landau-lemma-log-derivative.md`.

```
zeta(beta + i gamma) = 0,  |gamma| >= 3,  0 < delta <= 1/16,  1 - beta <= 1/16,  beta <= 1
==>  4/(1 + delta - beta)  <=  3/delta + 3A
         + 320 * ( (5/4) log(7 + 8|gamma|) + (3/4) log(1 + 1/delta) )
```
`A` = the pole constant from `RHTower/Sieve/ZetaPoleLogDeriv.lean : exists_pole_bound`.

## The three inputs

| input | module | statement |
|---|---|---|
| pole | `ZetaPoleLogDeriv.lean` | `-Re zeta'/zeta(sigma) <= 1/(sigma-1) + A` on `(1,2]` |
| Landau at `sigma+i gamma` | `ZetaLandauInput.lean : zeta_landau_at` | `<= 64 log M - sum_S m_rho Re(...)^{-1}` |
| three-four-one | `ZetaLogDerivThreeFourOne.lean` | `0 <= 3X0 + 4X1 + X2` |

`zeta_landau_at` uses `R = 1/4`, `R0 = 3/8`: the disc keeps `Re w >= 5/8` and `|Im w| >= 2`, so
`ZetaCrudeGrowth.norm_riemannZeta_le_crude` applies and `M = (7+2|gamma|)/||zeta(sigma+i gamma)||`.
The `||zeta||` lower bound comes from the **vendored** `PNTPlus.ZetaInvBound1` (root namespace,
importable — `PNTPlus` does not import the corpus, so no cycle; precedent:
`RHTower/XiMassPrimeSquareBoundaryResidue.lean`) plus the corpus's
`ZetaRealBound.norm_riemannZeta_real_le`.

## What remains for `kappa = 1`

Only the parameter optimisation. `delta = c0/log|gamma|`; a contradiction with
`1 - beta < c/log|gamma|` needs `4/(c0+c) > 3/c0 + 401`, so `c0 < 1/401`; `c0 = 1/500`,
`c = 1/10000` works once `log log|gamma|` is small against `log|gamma|`. That "eventually" is the
last Lean step.

## Lean traps found here

- **`linarith` does not identify `3 / d` with `3 * (1 / d)`.** They are distinct atoms to its
  preprocessing. If a goal has `3 / d` and the hypotheses have `1 / d`, insert
  `have : (3:ℝ)/d = 3 * (1/d) := by ring; rw [this]` before calling it. This silently cost several
  build cycles — the linear combination was otherwise completely standard.
- `set x := e with h` leaves `x` a *let*-binding; `clear_value x` makes it opaque. Worth doing
  before any `linarith` that mixes the abbreviation with its body (though it was not the culprit
  above).
- `Σ` cannot appear in a Lean identifier.
