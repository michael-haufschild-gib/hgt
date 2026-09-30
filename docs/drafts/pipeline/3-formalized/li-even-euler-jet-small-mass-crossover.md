# LI even Euler jets: sharp small-mass crossover

- **ID:** LI-EJ-SMALL
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean); significance/novelty bounded
- **Source:** actual first-current identification in `LiEvenCrossEulerCurrentBridge.lean`, actual shifted reciprocal moments and squared-node gap.
- **Objective:** locate the first mixed-sign Euler jet as mass tends to zero, exposing exact failure of a uniform differential cone.

## Candidate mechanism

For distinct actual squared nodes `b`, put `S_r=Σ m(b)b^(−r)` with intrinsic Cassini multiplicities. The source atom identity gives

`Γ(v exp t)=4 Σ_{r≥1} (−1)^(r−1) r² S_r v^r exp(r t)`

inside a sufficiently small logarithmic-mass neighborhood. Thus the even Euler jet is

`J_k(v)=4 Σ_{r≥1} (−1)^(r−1) r^(2k+2) Re(S_r) v^r`.

With corpus `XiZeroCopy` normalization, write `M_j=normalizedPrimeArchMoment j`; its ±Xi copies give `M_(r−1)=2 Re(S_r)`. The exact real-jet identity is therefore

`J_k(v)=2 Σ_{r≥1} (−1)^(r−1) r^(2k+2) M_(r−1) v^r`.

Both leading moments are unconditionally positive by `PrimeArchValuationSectorCones.lean:91`. Source negative-binomial expansion is `XiShiftedReciprocalHankelTailCriterion.lean:213,244`; actual Γ/current identification is `LiEvenCrossEulerCurrentBridge.lean`. No moment-positivity premise is added.

The first two terms balance at

`k = [log(1/v)+log(Re(S_1)/(4 Re(S_2)))]/(2 log 2)`.

For a bounded offset from this value, all terms `r≥3`, after division by `v`, should tend uniformly to zero. Key exponent is

`(r−1)−log(r)/log(2)>0` for every integer `r≥3`.

The node gap supplies the uniform summability needed beyond each fixed `r`. Integer rounding needs two separated comparison offsets; do not assert an exact rounded root without auditing ties and remainder signs.

## Exact theorem and dependency-closed paper proof

Put `a=2−log(3)/log(2)>0` and `c=1/(2 log(2))`. For each fixed real `C`, uniformly over every natural `k≤c log(1/v)+C`,

`|J_k(v)/(2v)−M_0+4^(k+1) M_1 v| = O_C(v^a)` as `v→0+`.

1. Existing negative-binomial moment identities, inserted into `Γ(v)=2v M_0(v)−6v² M_1(v)+4v³ M_2(v)`, give the centered mass series with coefficient `2(−1)^(r−1)r² M_(r−1)`. Local normal convergence follows from the uniform reciprocal-node gap and absolute summability. Exponential transport multiplies each fixed-order jet by `r^(2k)`, giving the exact displayed jet series. No growing-order differentiation is interchanged uniformly; first derive each fixed jet, then estimate its exact series uniformly in `k`.

2. `PrimeArchCentralMomentGerm.lean:55`, source reality and `XiReciprocalSquareSecondMomentRadius.lean:30` give `|M_(r−1)|≤A·150^(−(r−1))`, where `A=Σ_q‖xiZeroCopyReciprocalSquare q‖<∞` by `XiRelativeResolventTrace.lean:208`.

3. Set `L=log(1/v)>0`. For `k≤cL+C`, `r≥3`,

   `r^(2k+2) v^(r−1) ≤ r^(2C+2) v^[(r−1)−log(r)/log(2)] ≤ r^(2C+2) v^[a(r−1)/2]`.

   For integer `r≥3`, `r²≤3^(r−1)`: equality holds at three, and `(r+1)²≤3r²` closes induction. Taking logarithms proves the final exponent inequality. Since `v≤1`, factor out `v^a`; the remaining geometric series with fixed polynomial weights and ratio `1/150` is summable. This proves uniform remainder bound over all earlier indices, without signs of higher moments.

4. Let `τ=M_1/M_0>0` (the existing exact coalescing theta-source tangent) and `x(v)=[log(1/v)−log(4τ)]/log(4)`. If `k≤x(v)−1`, the leading term is at least `3M_0/4`; uniform remainder is eventually smaller than `M_0/4`, so every such jet is strictly positive. At `k=ceil(x(v)+1)`, the leading term is at most `−3M_0`, while `k≤x(v)+2`; the same uniform estimate gives a strictly negative jet. Thus least negative index exists and lies in a fixed-width interval about `x(v)`.

If `K(v)` is least natural `k` with `J_k(v)<0`, existence for sufficiently small positive mass follows from LI-EJ-OSC (and independently from step four), and

`K(v)/log(1/v) → 1/(2 log 2)` as `v→0+`.

In fact `K(v)=c log(1/v)+O(1)`. If along any sequence `v→0+`, `k→∞` and `4^k v→w>0`, the same uniform estimate gives the exact source-dependent profile

`J_k(v)/(2v) → M_0−4w M_1 = M_0(1−4τw)`.

Integer rounding prevents a general constant-offset limit for `K(v)`. This does not determine signs of full LI current tower, whose transfer polynomials retain structured cancellation.

## Lean realization and validation

- `LiEvenCrossEulerMassSeries.lean`: exact source mass expansion, absolute coefficient summability, canonical actual-current germ at zero and radius at least `1/2`.
- `LiEvenCrossEulerMassJetSeries.lean`: exact fixed-order real derivative and actual Euler-jet series; summability permits complete finite-prefix decompositions.
- `LiEvenCrossEulerSmallMassRemainder.lean`: complete source-tail bound `18A(3^k v/150)²`, positive decay exponent and uniform convergence over all earlier indices in each logarithmic window. The exponent identity is exactly `2−log(3)/log(2)`.
- `LiEvenCrossEulerSmallMassProfile.lean`: actual normalized jet equals its first two source terms plus the complete tail; explicit uniform bound and convergence follow.
- `LiEvenCrossEulerSmallMassLimit.lean`: along arbitrary filters, `v→0+` and `4^k v→w` imply `J_k(v)/(2v)→M_0−4wM_1`. No positivity of later moments or `w>0` premise is needed.
- `LiEvenCrossEulerFirstNegativeOrder.lean`: actual least negative natural index, uniform earlier positivity, ceiling witness, strict eventual interval `x(v)−1<K(v)<x(v)+2`, explicit bounded log error, `O(1)` capstone and `K(v)/log(1/v)→1/log(4)`.

All six leaves passed targeted named `lake build --old` and final exact `lake env lean <leaf>` checks. Public capstone axiom audits return only `propext`, `Classical.choice`, `Quot.sound`. Leaves are wired in `RHTower.lean`; no umbrella build was run. Refreshed whole-tree `scripts/formal_tools.py lint` remains red for eleven unrelated unwired CCM/Möbius/theta/zero-density modules; no completed or current LI Euler leaf appears in its errors. Formal index refreshed; parallel additions can make generated inventory stale again. No numerical experiments or added proof debt.

## Audits and remaining significance limits

1. Exact actual jet series was formalized before any growing-order estimate.
2. Discrete quadratic envelopes, geometric summability and exponent equality passed this Lean toolchain.
3. Capstones retain literal source normalization and audited natural ceiling bounds.
4. Continue novelty/significance audit. Durán's [*Asymptotic for the rightmost zeros of Bell and Eulerian polynomials*](https://arxiv.org/pdf/2404.03249), Theorems 2–3, already gives universal binary scale and weighted coefficient-ratio asymptotics for positive multiplier sequences. Actual higher Xi moments are not assumed positive or multiplier-preserving. No exact actual-LI match located, but source specialization alone does not establish significant new mathematics or universal absence from literature/training data.
5. Main cofinal-sign/current leaves passed integration first. No RH route is retired. Stronger source-dependent boundary-layer corrections are Lean-closed separately in [the source-boundary card](li-even-euler-jet-source-boundary-layer.md), including the exact two-layer floor sandwich and arbitrary-filter variable-drift limit.

## Log

- 2026-09-29 — Conjectured after cofinal-sign proof exposed nonuniformity of finite differential prefixes. No Lean code, numerical experiment, or unproved premise banked.
- 2026-09-29 — Exact source moment positivity and gap verified against inspected corpus. Independent audit closed uniform growing-order remainder and bounded-offset first-crossing paper proof. Universal scale has public overlap; source-dependent residual needs continued novelty/significance audit. Moved to paper-proven stage without claiming Lean completion.
- 2026-09-29 — Exact source series, uniform complete-tail estimate, literal two-term profile, binary-scale filter limit and least-negative-index asymptotics passed final targeted Lean and foundation-only axiom audits. Moved to formalized stage; RH remains open. Third-term complete-tail ingredient also passed in `LiEvenCrossEulerThirdMassRemainder.lean`, while the sharper boundary-layer capstone remains ongoing.
