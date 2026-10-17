# Exact infinite-grid classification by active correlation lags

## Objects and theorem

Fix `S>=2` and a nonzero real coefficient vector `c_0,...,c_m`. For signed integer `k`, set

\[
A_k=\sum_{0\le i,j\le m\atop j-i=k}c_i c_j,
\qquad G_f(u)=\sum_{j=0}^m c_j f(u-jS).
\]

Thus `A_0=Q=sum c_j²>0`, `A_{-k}=A_k`, and `A_k=0` for `|k|>m`.
A positive lag is **active** when `1<=k<=m` and `A_k!=0`.

**Classification.** There exists an actual smooth compact real seed `f` with `h_f(0)>0`,
correlation supported in `[-1/2,1/2]`, and `h_Gf(log n)=0` for every integer `n>=2`,
if and only if every active center `kS` is outside the logarithmic grid.
The resulting train is also smooth, compact, and has positive origin mass.

**Quantitative necessity.** For any compact C² seed with correlation radius `D>=0`, spacing
`S>D+1`, and an active center `kS>=2`, all-grid pinning gives `d(kS)>0` and

\[
E(f),E(G_f)\ge\frac{e^{-1/2}}4\log\frac1{d(kS)}.
\]

This applies to every active lag, so the smallest active nearest-grid distance governs the
strongest lower bound. It need not occur at the full span.

**Polar inheritance.** Define `B_c(S,beta)=sum_j c_j exp(beta*jS)`.
The construction can always be chosen so that `B_c(S,1/2)=0` implies exact polar balance
`integral_0^infinity h_Gf(x) cosh(x/2) dx=0`. This is a proved implication from finite data,
not an assumed analytic existence interface.

## Exact packet decomposition [PROVED HERE]

The certified finite-source expansion is
`h_Gf(x)=sum_{i,j} c_i c_j h_f(x+(i-j)S)`.
Grouping the finite sum by the integer `k=j-i` gives

\[
h_{G_f}(x)=\sum_{k=-m}^{m} A_k h_f(x-kS).
\]

Each pair has a unique integer difference in this range, so grouping neither omits nor
duplicates any term. Swapping `i,j` proves `A_{-k}=A_k`; the diagonal gives `A_0=Q`.
For `|x-kS|<=1`, every other center `lS` is at least `S` away. Hence
`|x-lS|>=S-1>D`, and

\[
h_{G_f}(x)=A_k h_f(x-kS).
\]

This includes `k=0`, so `h_Gf(x)=Qh_f(x)` on `[-1,1]`. ∎

## Necessity and quantitative survivor [PROVED HERE]

If an active center is a grid node, evaluation there gives `0=A_k h_f(0)`, contradicting
both nonzero factors. This proves necessity for the radius-half class because `S>=2>3/2`.

More generally let `d=d(kS)` and take a nearest grid node `log n` with
`|log n-kS|=d<=exp(-kS)<=1`. Packet isolation and `A_k!=0` force
`h_f(log n-kS)=0`. Evenness gives `h_f(d)=0`, and positive origin mass forces `d>0`.
Local diagonal preservation also gives `h_Gf(d)=0` and `h_Gf(0)=Qh_f(0)>0`.
Apply the certified logarithmic increment-energy inequality to each actual compact C² source
and divide by its positive mass. This proves the quantitative statement. ∎

## Actual-source sufficiency [PROVED HERE]

There are finitely many active positive lags. Their centers are at least two, and their
certified nearest-grid distances are all positive by the off-grid condition. Choose
`0<rho<=1/4` strictly below every such distance; the empty active set is allowed.

Take the certified nonzero smooth compact seed `phi`, and a correlation support radius
`D>0` supplied by compactness. Set `L=(D+1)/rho` and `f(u)=phi(Lu)`.
Then `L>0`, `h_f(x)=L^{-1}h_phi(Lx)`, and `h_f(x)=0` whenever `|x|>rho`.
Smoothness, compact support, and positive origin mass follow from this explicit dilation.

Evaluate the grouped correlation at any `x=log n`, `n>=2`. For `k<=0`,
`x-kS>=log 2>=1/2>rho`, so the seed term vanishes. For positive `k` with `A_k=0`,
the whole term vanishes. Otherwise `|x-kS|>=d(kS)>rho`, so again the seed term vanishes.
Every term is zero, giving all-grid pinning. Local preservation gives train origin mass
`Qh_f(0)>0`; the finite-source regularity theorem supplies smoothness and compactness. ∎

## Exponential symbol and polar balance [PROVED HERE]

Compact continuity makes every shifted exponential product integrable. Finite linearity and
the certified translation identity give, for every real `beta`,

\[
\int G_f(u)e^{\beta u}\,du
=B_c(S,\beta)\int f(u)e^{\beta u}\,du.
\]

If `B_c(S,1/2)=0`, the positive half-exponential source moment vanishes. The certified exact
autocorrelation identity expresses the whole-line cosh moment as the product of positive and
negative half-exponential source moments. Its value is therefore zero. The integrand is even,
so its positive-half-line integral is zero as well. All steps apply to the constructed source. ∎

## What the classification changes

Every active packet creates a genuine resonance obstruction and logarithmic energy cost.
Inactive interior packets impose no grid restriction at all: their cancellation is exact,
before choosing the seed. Endpoint noncancellation is one instance of this complete criterion.
This does not classify arbitrary polar sources, nor does it give an optimal energy constant.

## Novelty and certification boundary

Aperiodic coefficient correlations are classical; see
[Kai-Uwe Schmidt, *Sequences with small correlation*](https://arxiv.org/abs/1602.03722).
The corpus paper `quantitative-constant.md`, §3, already uses grouped lag coefficients for
finite-grid moment invariance. The connected infinite-grid classification and actual smooth
source realization are the contribution pursued here. No exhaustive literature novelty is claimed.
Both Lean leaves passed direct `lake --old env lean` checks without diagnostics.
The separate theorem-dependency audit passed for all 12 public theorems, including the private
finite-radius helper transitively: only `propext`, `Classical.choice`, and `Quot.sound` occur.
`FiniteTrainActiveLags.lean` contains 7 public theorems;
`FiniteTrainGridClassification.lean` contains 5 public theorems and the private helper.
Main endpoints: `exists_smooth_copyTrain_grid_source_iff`,
`exists_smooth_copyTrain_grid_source`, and `copyTrain_active_lag_energy`.
Scratch: `/tmp/infinite_grid_active_audit.lean`.
Logs: `/tmp/infinite-grid-active-{algebra,classification,axioms,index,lint}.log`.
This connected result is certified package 5 of the 100-package research objective.

The final global lint run reported eight concurrent modules missing umbrella reachability:
`CappedBlockSupport`, `CappedCosetSphereDuality`, `CenteredHyperbolicGramControl`,
`CompactSourcePairVariance`, `FullGridCappedCollarEnergy`,
`HyperbolicMultiplierIncrementAndOddSignCoercivity`,
`KreinKantorovichMeasureTransportAndPrimePolarPairing`, and
`SignedKreinCollarAndPrimeDeficitTransfer`. Neither new module has a lint error. Both are
wired into the field umbrella, and all 12 public theorem names appear in the generated API.
Repository-wide lint success is not claimed; unrelated modules were left untouched.
