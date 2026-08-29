# CLG atom-tangent likelihood reserve

Date: 2026-08-29  
Status: computation complete; diagnostic only; forbidden as input to Lean proofs

## Route question

Let `M(lambda)` be the exact C5 compensation margin along the literal first-atom-to-full-theta
likelihood homotopy.  If `M` is convex, then

```text
M(1) >= M(0) + M'(0).
```

The first-atom margin `M(0)>0` is already formalized.  This run tried to kill the only additional
first-order reserve needed by this convex tangent bridge:

```text
M(0) + M'(0) > 0.                              (CLG-LT)
```

## Outcome

`(CLG-LT)` survived all 335,780 tests at 140 decimal digits:

- 135,780 deterministic points on a `292 x 465` boundary-enriched grid;
- 200,000 randomized points biased toward `t=0`, `t=u`, and `A=6`;
- `6 <= A <= pi*exp(40)` and `0<t<=u`;
- no nonpositive atom margin, tangent reserve, or full margin;
- no robust violation of the corresponding convex tangent inequality.

The worst sampled likelihood tax occurred at the exact lower-scale/full-displacement corner
`A=6`, `t=u`:

```text
-M'(0) / M(0) = 0.1954230520036294...
(M(0)+M'(0)) / M(0) = 0.8045769479963705...
```

Thus computation selects the clean rational strengthening

```text
[CONJECTURE] -M'(0) <= M(0)/5.
```

This is not parameter optimization: it is a proposed exact source inequality which, together
with interpolation convexity, would prove positivity of the literal full-theta far-tail C5
margin and discharge the current CLG likelihood-interference gate.

## Research consequence

The former task “control arbitrary theta-mixture cross terms” is now sharpened to two explicit
source theorems:

1. `M''(lambda) >= 0` for `0<=lambda<=1`;
2. `M'(0) >= -M(0)/5` on `A>=6`, `0<t<=u`.

The second theorem should be attacked first: at `lambda=0`, every nonlinear denominator is the
already-factorized first-atom Bose weight, while the new terms are linear in the exact likelihood
jets.  The hostile test is a proof-derived analytic bound evaluated at the corner `A=6,t=u`, not
another point scan.

## Precision boundary

Raw subtraction of two values as large as `10^105` produced convexity gaps around `10^-34` with
either sign.  These are roughly `10^-139` relative and were classified below the 70-digit relative
resolution of the 140-digit run.  No robust negative gap occurred.  Margin and tangent-reserve
signs themselves had no such ambiguity.

## Reproduction

RunPod used 128 workers with one BLAS thread each.  Wall time was 79.4 seconds.
`verify_results.py` checks the two margin signs, the `1` tax-ratio boundary, and absence of a robust
convexity-gap violation.  `SHA256SUMS` authenticates all downloaded artifacts.

```bash
python3 run_experiments.py --workers 128 --dps 140 \
  --u-points 160 --tau-points 280 --random-points 200000 \
  --max-u 20 --output results.json
python3 verify_results.py .
```
