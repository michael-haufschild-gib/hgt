# Log-square observation windows through mixed moment costs

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** B130 scale locality; strengthening the square-root-window criterion.

## Target

There is a fixed `C>0` such that a uniform lower bound for the zeta spline
trace on all primes in arbitrarily late windows

`|log p-T|≤C (log(T+2))²`

implies RH. Centers may be arbitrarily sparse. No attained-top premise.

## Proposed mechanism

The positive deletion multiplier has the sharper one-factor estimate

`Q_(a,h)(s)≤exp(min(s²h²/2, |sh|))`.

For `h=π/γ`, split factors at `|γ|=H`. Their logarithmic moment cost is at
most

`|s| Σ_(|γ|≤H) |h| + (s²/2) Σ_(|γ|>H) h²`.

Existing zeta bounds give head cost `O((log H)²)` and tail square cost
`O(log H/H)`. With `H=T` and Chernoff parameter `q=T`, the total moment
cost is `O(T(log T)²)`. A sufficiently large fixed log-square radius
should dominate this cost and the trace envelope `exp(DT)`. The existing
finite-spectrum comparison and two prime-gap steps can then apply.

## Corpus inputs

- `RHTower.sum_xiCopiesBelow_inv_abs_le` in `VonKochChebyshevBound.lean`.
- `SquareRootThreshold.sum_inv_norm_sq_le` in
  `EffectiveHorizons/TheEGCContourIsExplicit.lean`.
- `RHTower.summable_inv_sq_xiCopyOrdinate` and its ordinate/norm comparison.
- `ScaleLocality` positive deletion, infinite trace passage, and finite-spectrum oscillation.

## Gaps

Formalize the mixed moment bound, uniform prefix estimates, log-square
leakage, and prime-window transfer. The arithmetic lower bound itself and
arbitrarily slowly growing windows remain open. No external novelty claim.
