# CLG likelihood-interpolation hostile test

Date: 2026-08-29  
Status: computation complete; diagnostic only; forbidden as input to Lean proofs

## Route question

The physical first-atom C5 compensation margin is already closed in Lean.  The current CLG tail
gate is addition of the literal higher-theta-atom likelihood interference.  This run tested the
exact homotopy

```text
q_lambda = q_first_atom + lambda * (q_full - q_first_atom),  0 <= lambda <= 1,
```

through all seven action and displacement jets entering the nonlinear C5 margin `M(lambda)`.
It asked whether the formal positive likelihood centre-flow jets imply monotone improvement of
`M`, and whether a more useful curvature law survives.

## Killed shortcut

Monotone improvement is false.  The robust sign counts for `M'(lambda)` were:

| campaign | negative | positive |
|---|---:|---:|
| deterministic | 811,886 | 209,457 |
| randomized | 50,334 | 14,310 |

There were also 34 deterministic and two randomized interior samples with margin below both
sampled endpoint margins.  Therefore the already-formalized positivity of the three likelihood
centre-flow jets does **not** transport through the nonlinear C5 compensation formula as a
pointwise monotonicity theorem.

## Survivor and new route candidate

No nonpositive margin occurred in 1,545,765 samples on

```text
A = pi*exp(2u) >= 6,  0 < t <= u,  0 <= lambda <= 1.
```

More importantly, no robust negative value of `M''(lambda)` occurred.  There were 871,573 robust
positive deterministic values and 52,094 robust positive randomized values.  Tiny raw negative
values disappeared under 180--320 digit reevaluation and were below the relative precision of
the subtracted theta tails.

This opens, but does not prove, the exact candidate

```text
[CONJECTURE] M''(lambda) >= 0 on the physical first-atom tail chamber.
```

Convexity converts the full-mixture problem into a first-atom tangent-reserve problem.  That
consequence is tested separately in
`../2026-08-29-c5-likelihood-tangent-reserve/REPORT.md`.

## Reproduction

RunPod used 128 workers, one BLAS thread per worker, and 120 decimal digits.  Wall time was 62.7
seconds.  `verify_results.py` checks margin survival, both robust derivative signs, absence of a
robust negative second derivative, and existence of an interior dip.  `SHA256SUMS` authenticates
all downloaded artifacts.

```bash
python3 run_experiments.py --workers 128 --dps 120 \
  --u-points 128 --tau-points 220 --lambda-points 17 \
  --random-points 100000 --max-u 20 --output results.json
python3 verify_results.py .
```
