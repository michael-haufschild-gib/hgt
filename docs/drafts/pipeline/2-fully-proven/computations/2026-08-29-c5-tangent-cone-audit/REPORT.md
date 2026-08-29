# CLG fixed-action C5 tangent-cone audit

Date: 2026-08-29  
Status: route diagnostic; no numerical output is admissible in Lean

## Frontier question

Can the already-formal pointwise likelihood-jet signs and pairwise bounds prove the atom-tangent
reserve needed by the CLG convex-homotopy route?

The test minimized the exact first variation of the C5 compensation over the formal coarse cone

```text
y=-db, x=-da,
0<=y<=13/5, 0<=x<=t*y, 0<=dm<=y,
0<=ds<=x, 0<=ds<=t*dm,
```

while separately evaluating the literal theta likelihood tangent. This attacks a named proof
mechanism, not a fitted constant.

## Outcome

- 514,803 physical states were tested at 120 decimal digits.
- The coarse cone failed the required tangent reserve at 171,237 states.
- Every cone minimum used the same vertex: `db=-y`, `dm=y`, with other adverse channels zero.
- The literal theta tangent had no failure in this run.
- Exact paper algebra, reconstructed without numerical input, proves the saturated second-channel
  coefficient is strictly negative throughout the physical tail.

Thus pointwise signs plus the current pairwise cone are structurally insufficient. Increasing
sample density cannot repair this producer.

## Route consequence

Killed:

```text
positive likelihood jet signs + current pairwise bounds
  -> atom-tangent reserve
  -> convex likelihood lift
```

Survivor: the literal theta tangent does not saturate the adverse vertex. A viable proof must retain
at least one of:

1. strict non-saturation coupling between second displacement and first mixed-centre channels;
2. exact favorable third likelihood channel;
3. an exact residual identity in the full compensation margin.

Two computation-free survivors were extracted and formalized independently:

- the saturated second-channel coefficient is everywhere negative;
- convexity of `-F'''` gives the mixed trapezoid law `dm <= t*dn`.

## Reproduction

RunPod used 128 worker processes, one numerical thread each. Runtime was 98.21 seconds.

```bash
python3 run_experiments.py --workers 128 --dps 120 --output results.json
python3 verify_results.py .
```

`results.json`, scripts, log, environment metadata, and `SHA256SUMS` are included.
