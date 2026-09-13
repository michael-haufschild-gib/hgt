# A source deformation can lose and recover real zeros

## Question

Earlier local double-root solves did not establish whether they marked entry, return, or a different branch from an independently verified nonreal zero. This experiment follows the actual complex witness in both deformation directions and repeats at half the step. A double root is attached only inside a traversed lambda bracket near the tracked height.

## Observed boundaries

| Witness | Source direction | Product strength | Direction from witness | Boundary height | Boundary lambda | Multiplier bound |
|---:|---|---:|---|---:|---:|---:|
| 0 | -1,1 | 1 | back | 20.28559449889 | 0.02092554470129 | 0.02980747924 |
| 0 | -1,1 | 1 | forward | 20.87047818832 | 0.05898932573142 | 0.08512642933 |

For the conductor-5 completed primitive real character source, direction (-,+)/sqrt(2) with product strength 1, the witness near 20.604335±0.709735i attaches to boundaries at lambda≈0.0209255447013, height20.2855944989, and lambda≈0.0589893257314, height20.8704781883. The sufficient multiplier bound throughout this interval is at most 0.085127<1. Positivity of this multiplier does NOT assert positivity of the underlying character-theta kernel.

## Interpretation

The high-lambda nearby collision was a numerical return boundary of the same witnessed pair. It was not its first entry threshold. This rejects a one-way-loss model for these specific deformations: the count of nonreal roots of the tracked pair is not monotone in deformation amplitude. It does not say that the entire deformed transform returns to an all-real zero set, or that these are the globally first collisions. The observations also show why nearest-height Newton localization cannot establish onset.

The local coefficient `-2*F_lambda/F_tt` in `(t-t_c)^2≈[-2*F_lambda/F_tt]*(lambda-lambda_c)` is negative at the lower boundary and positive at the upper boundary. Both coefficients are finite and nonzero in the high-precision evaluations. This independently checks the local directions of splitting. It does not certify the whole path between them.

## Validation, reproducibility and limits

4 tracks completed without reported errors; 2 distinct boundaries received 100/160-digit solves. Halving the continuation step changes attached boundary coordinates by at most 2.582284617E-39. The maximum 100/160-digit coordinate difference is 1.0516158873305298330036088882860566546902469270439641862941276E-97. Independent190-digit literal source integration checks both F and F_t at every boundary and at height+.125; maximum discrepancy is 6.959337153312462214189761973471049443732916256606648159612905976110262868981715846323272351521684672E-191 in units of `exp(-pi*t/4)*(1+t*t)^0.875`.

The interior complex witness was independently source-validated before this run; its hash and parameters are retained. Every accepted continuation point and failed attempt outcome is saved. These are high-precision numerical trajectories, not interval-certified continuous curves. The source quadrature uses the documented x=4 tail truncation and finite theta/character sums. Neither generic conjugation symmetry nor square-root splitting is claimed as a discovery.

Guarded wall time 281.581s; recorded worker time 460.511s, including screening, finer trajectories, precision and source checks. All interventions share the same ten-minute guard. Up to 14 worker processes, native threads1, isolated environment recorded. Download hashes passed; REMOTE-SHA256SUMS preserves the original manifest. No Lean builds.

## Consequence for HB/RH and next discriminator

Mass preservation, second-moment preservation and a positive deformation multiplier allow a finite interval of nonreal roots in these sources. Source-selection experiments must therefore follow branches and retain interactions, rather than treat each local collision as permanent loss or a global bound. This computation supplies no off-line zero of undeformed zeta or a Dirichlet L-function. Full physical HB identification and source-enforced extinction remain open. The next useful analytic target is a certified local return interval or a source constraint that excludes this behavior; a larger unqualified collision scan would add little.

## Recorded trajectories

![Tracked zero-pair entry and return](figures/returning-zero-pairs.png)

Dots are recorded points from the finer continuation and refined boundary roots. Lines guide the eye; they do not certify intermediate points. Lower curves are the conjugates inferred from the real-source symmetry. The conductor-5 real coordinate reverses direction inside its nonreal interval, whereas the plotted theta coordinate does not. This geometric contrast is exploratory, not a new monotonicity theorem. Rendering recorded data took1.133 seconds under a separate35-second artifact guard; no new numerical solve was performed.
