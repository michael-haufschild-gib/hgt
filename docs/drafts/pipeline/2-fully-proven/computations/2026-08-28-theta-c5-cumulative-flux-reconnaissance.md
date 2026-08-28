# Completed-theta cumulative C5 reconnaissance — 2026-08-28

## Status and scope

`[COMPUTATIONAL EVIDENCE — NOT A PROOF]`

Purpose: kill insufficient CLG/TTF proof mechanisms and identify a sharper analytic target for the
global completed-source C5 burden. No result here is, or may become, an input to a Lean proof.
`rh-current-frontier-map.md` was not edited.

Exact balance tested:

`B(u,t) = 6 - 2m - 4m^2 + 5me`,

where `m = tD/(2A)`, `e = (tJ-D)/(2D)`, and the corpus proves

`C5(u,t) >= 0  <->  B(u,t) >= 0` for `t > 0`.

Corpus declarations used:

- `thetaCuspFullSource`, `thetaCuspSourceTerm`, and `thetaCuspSeed`;
- `thetaCuspFullSource_neg` (evenness);
- `thetaCuspReflectedSourceCumulativeEndpointFluxRatio_mem_Ioc`;
- `thetaCuspReflectedSourceFifthRootCurvatureNumerator_nonneg_iff_cumulativeFluxLossBudget`;
- `thetaCuspCompletedReflectedCumulantRiccatiMargin_nonneg`.

## Run

- Host: Runpod `216.81.151.68`, 2 × AMD EPYC 9335, 64 physical / 128 logical cores.
- Parallelism: 64 Python worker processes, one BLAS thread each.
- Actual source: 24,000,000 scale-adapted samples; 8,059,037 passed numerical admissibility and
  `q >= 10^-3`.
- Small action: 2,177 independent 100-decimal evaluations in `t exp(u)` coordinates.
- Dominant-atom boundary: 200,001 100-decimal samples for `10^-10 <= q <= 10^6`.
- Finite mixtures: 6,000,000 samples each for 2, 3, and 4 positive theta-shaped atoms.
- Runtime of final run: 21.65 seconds, excluding transfer and smoke audits.

Four actual-source sampling families covered rectangular `(u,t)`, large-center
`t exp(u)` boundary layers, the same-half-line ratio `t/u`, and neighborhoods of `t=u`. Source
evenness reduces to `u >= 0`. Twelve positive atoms were retained at nonnegative arguments; every
reported extremum was independently reevaluated at 100 decimal digits. Large-center subtraction
used an exact stable one-atom second-difference identity after a smoke run exposed false float64
negatives.

## Results

### Actual completed theta source

- Negative `B`: **0 / 8,059,037** admissible sampled points.
- Negative elasticity `e`: **8,059,037 / 8,059,037**.
- Smallest float64 balance for `q >= 10^-3`:
  `B = 4.518508921506... × 10^-7` after 100-decimal reevaluation, at
  `u = 0.008042346431...`, `t = 0.007306496403...`, `q = 0.001000014600...`.
- Small-action scan: 0 / 2,177 negatives. Smallest sampled normalized coefficient was
  `B/q^2 = 0.451595557716...` at the modular seam `u=0`.
- Every action bin had its smallest sampled balance at, or very near, `u=0`:
  `u = 0.0080, 0.0125, 0.00137, 0.0161, 0.0516` for successive bins
  `[10^-3,10^-2], ..., [10,100]`.

This does **not** prove C5. It does show that the already-formalized nonnegative-elasticity safe
chamber is not the operative actual-source mechanism: all sampled actual points lie in the hard
negative-elasticity chamber, and cumulative reserve pays the loss.

### Finite positive theta-shaped mixtures

Filters were imposed pointwise at the sampled center/endpoints: positive action and first action
jet, `m in (0,1]`, negative log curvature at center and both endpoints, positive second action jet,
and nonnegative reflected Riccati margin.

- 2 atoms: 1,293,061 passed; **101,306 had `B < 0`**.
- 3 atoms: 665,502 passed; **223,278 had `B < 0`**.
- 4 atoms: 391,451 passed; **224,324 had `B < 0`**.

A moderate two-atom witness, confirmed at 100 decimals, has center probabilities
`(0.1023516100..., 0.8976483900...)`, `u = 0.0115606281...`, `t = 0.0106537969...`,
`m = 0.9838406493...`, `e = -0.0327827468...`, positive Riccati margin
`319.2876056...`, and `B = -0.000715986779853...`.

Consequence: pointwise positivity of theta-shaped atom mixing, endpoint-ratio confinement, local
log-concavity, and the reflected Riccati inequality do not algebraically imply C5. Any proof using
only those data is dead. This is a pointwise insufficiency result; finite reweighted mixtures were
not certified to satisfy the completed source's global modular law, so the computation does not
refute a theorem that uses that law.

### Asymptotic structure

For `u -> infinity`, `t = w exp(-u)`, and `q -> 4 pi w^2`, the dominant atom gives

`B_dom(q) = 6 - (2+5q) q/(exp(q)-1) - 4 (q/(exp(q)-1))^2`.

Its center expansion is

`B_dom(q) = (2/3)q^2 - q^3/12 - q^4/72 + q^5/720 + ...`.

No negative value appeared in 200,001 high-precision samples. For fixed `u`, the cofinal limit is
`B(u,t) -> 6` as `t -> infinity`.

For a general even action
`q(t)=c2 t^2 + c4 t^4 + c6 t^6 + ...`, the first balance coefficient is

`B(t) = 2(c2^4 - 9c2^2 c4 + 15c2 c6 - 6c4^2)/(3c2^2) * t^4 + O(t^6)`.

## Research consequence

`[CONJECTURE]` **Action-level seam minimization.** For the actual completed theta source, among
points with fixed reflected action `q`, `B(u,t)` is minimized at `u=0`.

This conjecture is absent from the corpus search. It survives the actual-source computation and
fails to be a generic positive-mixture phenomenon, so its only plausible producer is exact modular
theta coefficient coupling. If proved, global two-variable C5 reduces to:

1. one-variable seam positivity at `u=0`;
2. the explicit positive dominant-atom boundary profile;
3. action-level monotonic transport between them.

Equivalent differential target along action levels is the sign of the Jacobian
`B_u q_t - B_t q_u`. This is the recommended next hard analytic problem. Do not spend effort trying
to prove `e >= 0`, generic atom-mixture positivity, or C5 from Riccati and log-concavity alone.

## Artifacts and limitations

- `theta_c5_recon.py`: reproducible multicore workload.
- `theta_c5_results.json`: full compact metadata, top candidates, 100-decimal checks, and symbolic
  expansions.
- `theta_c5_actual_top.csv`: 100 smallest sampled actual-source balances.
- `theta_c5_finite_mixture_top.csv`: smallest sampled 2/3/4-atom balances.
- `theta_c5_symbolic.txt`: center and cofinal formulas.

SHA-256:

- actual CSV: `fc3d9405a7326c62798c098d62964337253dfc7130d3a73d1392ca3de21aa208`
- mixture CSV: `08080a81717f9d36d0dba94e4346649d33706e30462dc0cf04eb3c3f729b8748`
- result JSON: `f4172b19b9ac4fff78ce3805ca1cc2c5a5a27b43be2b133040750259c04aac33`
- symbolic text: `57add291cd4dfa8a9782bb7f1f201b0f2813f4830558ff5e23501c45d38c33d2`

Limits: searches are non-exhaustive; truncation and decimal checks are not interval certificates;
sampled positivity cannot establish a theorem. Negative finite-mixture witnesses are strong route
killers but still require an analytic/interval proof before being promoted to a formal no-go.
