# EDQ outgoing aggregate versus the strict mean margin

- **ID:** EDQ-OUM
- **Stage:** 3-formalized
- **Type:** THEOREM; paper and Lean audited
- **Source:** [current frontier](../1-in-progress/rh-current-frontier-map.md), [reflected aggregate](edq-stationary-reflected-tail-sum.md), [half-mean reserve](edq-positive-frequency-reserve.md)

## Full chain and objective

Euler deletion → exact arithmetic remainder → cumulative stationary-head comparison → off-line-zero exclusion → RH. Prove that the entire outgoing error is uniformly smaller than the established mean reserve at sufficiently large height. Then transfer a strict, explicit positive lower bound to the actual incoming head required by any closed-right zero. This addresses the outgoing error in the full comparison; an opposing incoming-head bound and RH remain open.

## Symbolic proof

Let `0<sigma<=1`, `t>=4*pi`, `B=t/(2*pi)`, and `K=floor(B)`. Then `B>=2`, `B/2<=K<=B`, so `K>=1`. Existing source bounds use

`Q=28*w_1*B^(-sigma-1)/sqrt(t)` and

`P=K^sigma/norm(s)+K^(sigma-1)/2+norm((1-conj(s))*(2-conj(s)))*K^(sigma-2)/(2-sigma)`.

The exact factorization

`P=K^sigma*(1/norm(s)+1/(2*K)+norm((1-conj(s))*(2-conj(s)))/((2-sigma)*K^2))`

retains every reflected endpoint and remainder term. From `norm(s)>=t`, `norm(1-conj(s))<=t+1`, `norm(2-conj(s))<=t+2`, `t>=4`, and `2-sigma>=1`, the last coefficient is at most `2*t^2`. Therefore

`Q*P <= 28*w_1/(B*sqrt(t))*(1/t+1/B+8*t^2/B^2)`.

With the actual weight `w_1=1/(4*pi^2)` this equals

`(14/pi+28)/(t^2*sqrt(t))+448*pi/(t*sqrt(t)) <= 2000/(t*sqrt(t))`.

The known half-mean is `t/[24*normSq(s+1)]>=1/(120*t)` since `normSq(s+1)<=(t^2+4)<=5*t^2`. Thus if `sqrt(t)>=480000`, the outgoing error is at most `1/(240*t)`, and the established strict half-mean lower budget at a zero forces

`Im(H(s,1,K)) > horizontal_displacement + 1/(240*t)`.

For `sigma>=1/2` the displacement is nonnegative, so the incoming aggregate is strictly positive with the stated reciprocal-height lower bound. This implication includes critical zeros and does not select the critical line. Constants are deliberately loose symbolic bounds, with no finite or numerical verification used.

## Unconditional positive survivor

The corpus's analytic Hardy theorem gives actual critical-line zeros above every prescribed height. Applying the new quantitative lower bound at those zeros proves, with no zero-existence premise,

`for every T, there exists s with Re(s)=1/2, Im(s)>max(T,0), zeta(s)=0, and Im(H(s,1,floor(t/(2*pi))))>1/(240*t)`.

Thus the blanket assertion that all sufficiently high closed-right incoming heads are nonpositive is false. The positive survivor is quantitative and cofinal, not only a negative no-go. This does not rule out comparisons specific to off-line zeros, relative to horizontal displacement, or involving other exact source terms. The whole EDQ route remains live.

The complete uniform incoming bound already retains horizontal displacement and is valid at every strip zero with `t>=4*pi`:

`Im(H) > t*(2*sigma-1)/[2*normSq(conj(s)*(1-conj(s)))]+1/(120*t)-2000/(t*sqrt(t))`.

## Lean inventory

`GaloisForLFunctions.RHTower.ArithmeticStationaryOutgoingMargin`, namespace `RHTower.DeletionMixedRefinement`: 254 lines, 14 new theorems, no new definitions.

- `stationary_floor_half_bounds`, `norm_reflected_boundary_product_le`, `reflectedPrefixZeroEnvelope_factor`, `reflectedPrefixZeroEnvelope_le_moving_scale`.
- `stationaryReflectedTailEnvelope_mul_scale`, `stationaryOutgoing_scale_bound_identity`, `stationaryOutgoingEnvelope_le_uniform`.
- `norm_stationary_outgoing_le_uniform_at_zero`, `stationary_half_mean_ge_reciprocal_height`, `stationaryIncomingSection_im_lowerBound_uniform_at_zero`.
- `stationary_large_sqrt_height`, `stationaryOutgoingEnvelope_le_quarter_mean_floor`, `stationaryIncomingSection_im_gt_reciprocal_height_at_zero`, `exists_critical_stationaryIncoming_positive_above`.

## Final audit

Foreground scratch passed without warnings. `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticStationaryOutgoingMargin` built only the new leaf in 5.4 seconds. The umbrella import is wired; no umbrella or full build ran. All 14 new theorems were audited once, with only `propext`, `Classical.choice`, and `Quot.sound`; no existing declaration was re-audited. No numerical experiment or computational certificate was used.

Global formal lint reports only two unrelated modules not yet reachable from the RHTower umbrella: `ThetaCuspCenterCompensationSign` and `ThetaCuspOddCompensationCoefficient`. These concurrent files are outside EDQ and were preserved. The EDQ leaf has no lint finding. Logs: `/tmp/edq_outgoing_margin_{build,axioms,lint}.log`.

## Verification gates

- [x] Corpus research and exact existing source inspection.
- [x] Kernel verification of algebra, floor estimates, and uniform inequality.
- [x] Transfer to actual outgoing aggregate and incoming zero budget.
- [x] Wire leaf, targeted build, new-only axiom audit.
- [x] Formal lint run; unrelated findings recorded above.
- [x] Current-state docs and corpus index refreshed; three temporary Lean sources removed; every owned Lean process exited.
- [ ] Independent incoming comparison excluding every off-line zero; RH.
