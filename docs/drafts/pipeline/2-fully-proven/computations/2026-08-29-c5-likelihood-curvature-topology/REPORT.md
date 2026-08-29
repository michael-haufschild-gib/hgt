# CLG likelihood-homotopy curvature topology

Date: 2026-08-29  
Status: route-selection computation; forbidden as Lean input

## Frontier question

The surviving CLG likelihood lift asked for convexity of exact first-atom-to-full compensation
`M(lambda)`. A direct proof of `M''>=0` is a three-variable burden. This campaign asked two more
decisive questions:

1. Is `M'''` one-signed in `lambda`, reducing convexity to an endpoint theorem?
2. After removing exponentially small higher-atom amplitude, does far-tail `M''` or `M'''` have
   the wrong leading sign?

All derivatives are analytic formulas; no finite differences are used.

## Validated outcome

On the compact structural tail `6<=A<=100`, a 400-decimal run tested 48,138 deterministic and
10,000 randomized physical packets, with 33 lambda values per packet:

- no negative `M''`;
- `M'''>0` at every lambda value;
- no `M'''` sign-change bracket;
- hence every sampled `M''` minimum was at `lambda=0`.

The far-tail calculation avoids subtraction of nearly equal full/atom jets. It factors out the
dominant second-atom likelihood amplitude

```text
R_2(A)=4*(8A-3)/(2A-3)*exp(-3A)
```

and evaluates the exact homogeneous leading coefficients. Across 248,815 states, covering
`6<=A<=10^10`, macroscopic displacement and seam boundary layers `A*t=O(1)`:

- leading coefficient of `M''` was positive everywhere;
- leading coefficient of `M'''` was positive everywhere.

## Route consequence

This opens a materially smaller producer:

```text
M'''(lambda)>0  and  M''(0)>=0
  -> M''(lambda)>=0
  -> convex likelihood lift.
```

The old global `M''(lambda)>=0` target is therefore sharpened to two endpoint/source inequalities.
Dominant second-atom positivity suggests the cofinal tail can be handled analytically after
factoring `R_2(A)^2` and `R_2(A)^3`; remaining difficult region is finite transition scale. Together
with the independent atom-tangent reserve, these endpoint laws would close literal far-tail C5
compensation.

This is actionable in the existing corpus rather than a new numerical surrogate: Lean already
contains exact second-to-first likelihood-ratio and dominant-atom `exp(-3A)` identities (including
`thetaCuspSecondAtomLikelihoodRatio_seam_eq_exp_neg_three_pi`). Those source identities are the
intended starting point for a remainder bound; no sampled value is needed or admissible there.

No sampled sign proves either theorem. Next paper task is to derive exact formulas for `M''(0)` and
`M'''(lambda)`, factor their dominant second-atom terms, and bound remaining atom ratios.

## Precision correction

An initial 140-digit relative-sign scan reported apparent negative `M''` only where higher-atom
signal lay below working precision. Re-evaluation at 200, 400, and 600 digits made the same
witnesses stably positive and matched the original independent `M''` formula. Those false signs
are discarded. This is why the far-tail run uses amplitude removal rather than larger raw grids.

## Reproduction

RunPod used 128 worker processes with one numerical thread each.

```bash
python3 run_experiments.py --workers 128 --dps 400 --u-points 96 \
  --tau-points 200 --lambda-points 33 --random-pairs 10000 \
  --max-u 1.7302201500693455 --output stable-results.json
python3 run_asymptotic.py --workers 128 --dps 120 --a-points 500 \
  --t-points 500 --max-a 1e10 --output asymptotic-results.json
python3 verify_witnesses.py
```

Scripts, raw results, logs, environment metadata, and checksums are included.
