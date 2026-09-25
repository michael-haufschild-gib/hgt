# Theta Gibbs Stein certificate discovery

## Question

Can the exact first-atom Gibbs score produce sufficiently sharp global integral inequalities to close the first nonconstant completed prime--Gamma Hankel minor?

The density is `rho(x)=exp(5x/2-pi exp(2x))` on `x>=0`. For
`Bq=(2pi exp(2x)-5/2)q-q'`, integration by parts gives
`integral (Bq)rho = q(0)exp(-pi)` when the endpoint at infinity vanishes.

## Method

Runpod: `157.157.221.29:27094`, 32 logical CPUs. `search.py` uses 16 processes, one native numerical thread per process; `rationalize.py` uses four processes. No integral quadrature or zero computations were performed.

Search `q=sum_{j=1}^J r_j(4x)exp(-2jx)`. Rewrite `P-Bq` in powers of `4x` and Bernstein polynomials in `t=exp(-2x)`. Nonnegative coefficients certify the entire rectangle `x>=0, 0<=t<=1`. Impose the sign at both `pi=314159/100000` and `pi=3927/1250`; affine interpolation then covers actual pi. Both pi bounds have analytic proofs in the local mathlib.

Degrees `J=4,8,12,20` were tried for mass and the three Ward polynomials. Floating-point optima contained constraint violations down to approximately `-8.3e-10`; those optima are not certificates. A second solve fixed simple rational boundary values and maximized strict residual slack. Coefficients were rounded to rational numbers, their boundary sum corrected exactly, and every Bernstein residual recomputed with rational arithmetic.

## Outcome

All four rational candidates have strictly positive residual coefficients at both pi endpoints:

| Integral divided by `exp(-pi)` | Direction | Rational target | Exponential degree |
|---|---|---|---|
| `integral rho / exp(-pi)` | lower | `1697/10000` | 4 |
| `integral (4x-x²)rho / exp(-pi)` | lower | `423/5000` | 8 |
| `integral (8x³-x⁴)rho / exp(-pi)` | upper | `5457/500000` | 8 |
| `integral (12x⁵-x⁶)rho / exp(-pi)` | lower | `441/200000` | 8 |

For `c=3005/2997`, the exact resulting ratio margins are

```
9(423/5000)(441/200000) - 14c²(5457/500000)²
  = 2940012677/1247501250000000 > 0

45(423/5000)² - 16c²(18303/10000)(5457/500000)
  = 18695040767/24950025000000 > 0.
```

The common `exp(-pi)` factor cancels. Thus these certificates are strong enough for both first-atom Ward ratio inequalities and the corpus's full-source first-minor consumer, including its all-order higher-atom loss `c`.

## Proof status and use

`rational-certificates.json` contains the complete rational witnesses and residual decompositions. `emit_lean.py` renders the witness identities and nonnegativity proofs. The resulting analytic integral bounds and full-source first-minor theorem are independently proved in `ThetaGibbsSteinIntegral.lean` and `ThetaGibbsSteinSourceMinor.lean`; both named-module audits pass. Scratch axiom checks report only `propext`, `Classical.choice`, and `Quot.sound`. The proof card is `docs/drafts/pipeline/3-formalized/theta-gibbs-stein-source-minor.md`.

Neither the optimizer, Python's rational checks, nor this report is a Lean premise. Lean checks symbolic polynomial identities, coefficient signs, and improper-integral arguments. No numerical integral estimate is used.

This is a finite source block. It supplies no all-rank positivity theorem and no proof of RH. The useful new method is a signed exponential-polynomial Stein primitive with a globally nonnegative Bernstein remainder, retaining the exact theta-source score.
