# Two source-realizable boundaries of the compensation inequality

**Status:** the two bounded boundary scans below are retained as scoped observations. The [escaping-atom experiment](ESCAPE-REPORT.md) rejects B1 numerically, preserving positive curvature and actual mass/mean. No RH proof or zero classification. The frozen protocols are in [EXPERIMENTS.md](EXPERIMENTS.md).

## Question and intervention

The parent experiments found altered positive theta tails with negative complete compensation, but all those witnesses violated the actual source's positive lower-transport curvature `H''`. Random multi-atom sampling also found negative first-two-channel sums rescued by the third channel. The present experiment attacks the two boundaries separately rather than repeating a positivity grid.

Use the complete budget already identified in Lean,

`F = (β²-1)[12(r-β/2)(s-β/2)-1] + 3h[(6+4β)r-2(β²-1)]`.

Here `β=coth(q/2)`, `r=-da/(a A)`, `s=H'/(B A)`, `h=H''/(B A²)`, `A=-dq`, and `B=-H`. The basic admissibility gates are positive action and source jets `a,b,S`, negative `H`, and positive `H'`; B1 additionally requires `H''>0`. This is the parent report's normalized compensation, not a new definition of RH.

Interventions keep the actual theta tail's Laplace mass at the left endpoint. Positive mixtures use the lowest spectral atom 3, the literal tilted theta tail, and remote atoms. They change the tail distribution and therefore are counterfactual sources. No conclusion about zero location follows directly from them.

## Outcomes

| Conditioned surface | Work performed | Result |
|---|---|---|
| `H''=0` | 450 specifications, 270 in the actual left-scale structural chamber, 372 bracketed crossings (all structural); 4,464 side evaluations, 1,840 with all B1 gates | No negative complete compensation in the evaluated sides |
| Same surface, recomputed at 100 digits | 920 center evaluations passing the gates other than curvature | All retained-coordinate zero-curvature base gaps positive; minimum about `5.0465304 × 10^6` |
| `r=β/2` | 270 specifications, 267 bracketed roots, 252 admissible evaluations | All required positive curvature; smallest curvature/critical-curvature ratio about `82,158.4183` |

Repeated endpoint mixtures occur among these specifications; these are evaluation counts, not counts of distinct source measures. The first surface used 75-digit arithmetic and the second 90 digits. Root grids and finite brackets are exploratory and need not find every crossing.

The second surface forces the first-two-channel normalized contribution to be `-(β²-1)`. The exact critical curvature there is `(β²-1)/(3(3β+2))`. Thus positivity in those cases necessarily uses the third channel. This minimum lies outside the actual left-scale structural chamber; that chamber has 162 admissible slope roots and a minimum ratio about `3.12e8`. The weakest extended-domain case is the pure lowest-atom replacement at left scale `π`, homotopy parameter zero, and displacement

`t = 0.4764189778893174436406670677965802786666…`.

Its complete third compensation is `0.001959413731569476964182344693847392…`. Independent differentiation of the Laplace function and of the complete homotopy compensation agrees at 90 and 140 digits; doubling the theta mass cutoff from 40 to 80 leaves the displayed digits unchanged. See [boundary-validation.json](boundary-validation.json).

**Interpretation:** the tested zero-curvature boundary lies deep inside a region where the other channels are favorable. The tested adverse-channel boundary lies deep inside a region with adequate curvature. This explains why more random tests near only one boundary would miss the real question: can a realizable positive source approach both shortages together? These data do not bound the intervening region or exclude other positive measures.

## Exact positive residue

Retain `κ=s-r+h/(2r)` and set

`Q=(6+4β)r²-4(β²-1)r+β(β²-1)`.

For `r≠0`, exact substitution gives

`F=(β²-1)[12(r-β/2)(r+κ-β/2)-1]+3h Q/r`.

The exact identity

`(6+4β)Q = [(6+4β)r-2(β²-1)]²+(β²-1)(6β+4)`

makes the curvature coefficient strictly positive when `β>1,r>0`. The Lean module `ThetaCuspC5BoseHyperbolicReserve` additionally proves the division-free incidence identity, the cleared substitution including `r=0`, and unconditional nonnegativity of `Q(1+x²,r)`. These four new theorems passed a scratch check and a direct source check with `lake env lean`. They contain no numerical input. The formal audit is recorded in the parent report.

This monotonicity fixes `β,r,κ`. Actual source deformation need not fix those coordinates. Treating it as source monotonicity would omit the hard mathematical step.

## Consequences for a proof and for grouping

An explicit source inequality separating the two shortages could support different proofs in different source regimes. Corpus mechanisms inspected for that step include affine-Gamma inward curvature transport and the two-sample cross-Wronskian identity in `SuzukiShiftSpectralMonotoneRatio`. Neither supplies the required inequality for this theta source merely by resemblance.

This is a concrete application of proving different classes by different mechanisms, but the classes here concern contributions to an inequality. Assigning every nontrivial zero to independently defined classes remains a separate problem. A prime partition, a source-regime split, and an exhaustive zero classification must not be conflated.

## Reproduction

Run on the authorized Runpod in `/root/rh-route-surprise-20260906/boundary-followup`, with the parent helpers present: `boundary_search.py`, `interrogate_boundary.py`, `slope_boundary.py`, then `verify_boundary.py`. Each command was wrapped in `timeout 120s`; worker pools use at most eight processes and one BLAS/OMP thread each. The two principal batches reported 3.45 and 2.21 seconds. JSON and JSONL outputs, scripts, and independent validation were downloaded here. Large-action Bose differences use an exponential form to avoid subtracting nearly equal numbers. No experiment uses a zeta-zero list as a premise.
