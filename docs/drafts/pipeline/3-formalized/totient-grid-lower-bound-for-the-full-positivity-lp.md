# Totient grids bound every positivity test

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Closure tasks](fable-route-closures.md).

## Theorem

For a continuous integrable real function `g≥0`, with integrable real Fourier
transform `h=𝓕g`, `g(0)>0`, and `h(α)≤0` for `|α|≥1`,

```
[h(0)+∫_[-1,1] |α|h(α)dα]/g(0) ≥ 1+3/π² > 13/10.
```

This closes the standard positivity LP for arbitrary admissible tests, not
only the Frobenius family. The class is the Fourier-dual formulation of
[Chirre–Gonçalves–de Laat, §3.1](https://arxiv.org/html/1810.08843#S3.SS1).
No extra lower bound on the form factor beyond the unit band is imposed.

## Proof

Use the exact form factors `F_L` of the
[totient grid construction](../3-formalized/totient-grids-obstruct-seventy-percent-at-every-bandwidth.md).
Their positive grid expansions and Fourier inversion give

```
∫h P_m = Σ_r (L/m)sinc²(πr/m) g(rL/m) ≥ (L/m)g(0).
```

Fourier pairing with the removed central triangle gives

```
∫h(α)LΛ_1(Lα)dα = ∫g(x)sinc²(πx/L)dx ≤ ∫g = h(0).
```

Hence `A_L g(0)≤h(0)+∫h F_L`. Since `F_L≥0`, equals `|α|` on the
unit band, and `h≤0` outside it, the last integral is at most
`∫_[-1,1]|α|h(α)dα`. Taking `L→∞` gives the target because
`A_L→1+3/π²`. All integral and series interchanges follow from
`g,h∈L¹`, boundedness of `F_L`, and the summable positive grid coefficients.

## Lean

`TransThresholdPairCorrelation/TotientGridBoundsEveryPositivityTest.lean`:

- `grid_constant_mode_le_positive_test`: each grid retains its origin mode.
- `central_triangle_test_le_mass`: Fourier pairing bounds the removed triangle.
- `positivity_test_cost_ge_totient_limit`: the exact bound `1+3/π²`.
- `positivity_test_cost_gt_thirteen_tenths`: exclusion of the seventy-percent target.

The module passes `lake --old env lean` and is imported by its umbrella.
The positive survivor is the exact totient family with origin mass tending to
`1+3/π²`; the resulting positivity-method census ceiling is `1−3/π²`.
This is an obstruction bound, not a claim that the LP optimum is attained there.
