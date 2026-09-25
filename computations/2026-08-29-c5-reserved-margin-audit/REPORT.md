# CLG adaptive-reserved margin hostile audit

Date: 2026-08-29  
Status: route diagnostic; no numerical output is admissible in Lean

## Frontier question

The likelihood-lift reduction proposed three sufficient far-tail endpoints: positivity of the
lower-jet, fixed-master-reserved, or adaptive-reserved compensation margin. This run tried to kill
those endpoints while evaluating the literal full completed compensation in parallel.

Definitions were transcribed directly from
`ThetaCuspFixedActionC5LikelihoodLiftReduction.lean`; no surrogate objective or optimized proxy was
used.

## Outcome

At 516,054 physical states and 160 decimal digits:

| Candidate | Robust negative samples | Robust positive samples |
|---|---:|---:|
| lower-jet margin | 25,954 | 434,328 |
| master-reserved margin | 25,629 | 434,612 |
| adaptive-reserved margin | 25,286 | 434,882 |
| literal full margin | 0 | 447,146 |

The negative adaptive chamber occurs next to the collapsed displacement seam and persists across a
wide scale range. It is not a corner-constant optimization issue.

Independent source algebra then identified the mechanism: after clearing the positive Bose
denominator, the adaptive margin has fifth seam derivative

```text
600*kappa(u)^2 * (F3(u) + 2*A(u)*F2(u)) < 0.
```

The strict sign follows from the already-formal support-gap cooling law
`2*A*F2 < -F3`. Hence the computation exposed a genuine structural no-go, now proved on paper
without numerical input.

## Route consequence

Killed:

```text
adaptive-reserved positivity
  -> literal far-tail fixed-action C5 orientation.
```

The lower bound deletes exactly the third-channel cooling excess required for seam cancellation.
Master and lower-jet variants fail for the same reason. Future work must not retry any globally
positive reserved endpoint of this form.

Survivor: literal full compensation remained positive throughout the attack. The correct target is
therefore cancellation-preserving:

```text
full margin = adaptive margin + exact positive third-channel residual,
```

or equivalently the weaker domination `adaptive margin > -residual`. This is the next
computation-free paper/Lean target; the sampled full-margin signs are not evidence usable in Lean.

## Precision and reproduction

Theta tails were evaluated at 160 digits. Terms beyond the implemented cutoff are below the
working precision on the tested chamber; selected failure points were stable under higher-cutoff
re-evaluation. RunPod used 128 worker processes and one numerical thread per worker. Runtime was
92.49 seconds.

```bash
python3 run_experiments.py --workers 128 --dps 160 --output results.json
python3 verify_results.py .
```

`results.json`, scripts, log, environment metadata, and `SHA256SUMS` are included.
