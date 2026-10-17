# Full-span rigidity for finite common-seed copy trains

## Statement

Let `f` be a compact C² real source with `R=h_f(0)>0`. Compactness supplies a correlation
support radius `D>=1`. For any integer `m>=1`, spacing `S>D+1`, and real coefficients
`c_0,...,c_m` with `c_0 c_m!=0`, form the actual source

\[
G(u)=\sum_{j=0}^{m}c_j f(u-jS),\qquad L=mS,\qquad Q=\sum_{j=0}^{m}c_j^2.
\]

If `h_G(log n)=0` for every integer `n>=2`, then `d(L)>0`, where `d` is the certified nearest
logarithmic-grid distance, and

\[
E(f),\ E(G)\ \ge\ \frac{e^{-1/2}}4\log\frac1{d(L)}
\ \ge\ \frac{e^{-1/2}}4 L.
\]

In particular the full span cannot itself be a logarithmic-grid node. Interior coefficients
may have either sign, vanish, and cancel contributions at repeated interior difference lags.
Neither the number of packets nor their coefficient magnitudes enter the normalized lower bound.
The support threshold is derived from the source; no modulus or analytic interface is assumed.
Polar trains, when present, are included without imposing a polar hypothesis.

## Finite translated-source identity [PROVED HERE]

For arbitrary finitely many shifts `t_i` and coefficients `c_i`, put
`F(u)=sum_i c_i f(u-t_i)`. Translation and finite summation preserve compact support and
the differentiability order. Each shifted product is integrable, and finite expansion gives

\[
h_F(x)=\sum_{i,j}c_i c_j h_f(x+t_i-t_j).
\]

Indeed the `(i,j)` term is the integral of
`c_i c_j f(u-t_i)f(u+x-t_j)`; substitute `v=u-t_i`.
This is an exact source identity, not a prescribed positive-definite relaxation. ∎

## Local preservation and extremal isolation [PROVED HERE]

For the equally spaced train, every off-diagonal shift difference has magnitude at least `S`.
If `|x|<=1`, then `|x+(i-j)S|>=S-1>D` for `i!=j`. Thus

\[
h_G(x)=Q h_f(x)\qquad(|x|\le1).
\]

In particular `h_G(0)=QR>0`, since `c_0!=0` implies `Q>0`.

Now let `|x-L|<=1`. Except at `(i,j)=(0,m)`, the integer `m+i-j` is at least one.
Therefore
`x+(i-j)S=(x-L)+(m+i-j)S>=S-1>D` for every other pair. Only the endpoint pair survives:

\[
h_G(x)=c_0 c_m h_f(x-L)\qquad(|x-L|\le1).
\]

No control of interior aperiodic autocorrelations is needed. ∎

## Nearest-grid pinning and energy [PROVED HERE]

Since `D>=1`, `S>D+1` and `m>=1` imply `L>2`. The already certified nearest-node geometry
supplies `n>=2` with `|log n-L|=d(L)<=exp(-L)<=1`. Evaluate the extremal identity at `log n`.
Grid pinning and `c_0 c_m!=0` force `h_f(log n-L)=0`; evenness gives `h_f(d(L))=0`.
If `d(L)=0`, this contradicts `R>0`. Hence `d(L)>0`, and local preservation also gives
`h_G(d(L))=0`.

Apply the certified logarithmic increment bound to `f` and to the actual compact C² source
`G`, then divide by their positive origin masses. This proves the first energy inequality.
Finally `0<d(L)<=exp(-L)` gives `-log d(L)>=L`, proving the full-span lower bound. ∎

## Source-pure division-free endpoint [PROVED HERE]

Positive origin mass can be dropped from the division-free conclusion. For every compact C²
source, compactness supplies `D>=1` such that, for the trains above,

\[
e^{-1/2}Lh_f(0)\le4J_{\rm arch}(f),\qquad
e^{-1/2}Lh_G(0)\le4J_{\rm arch}(G).
\]

In fact only the detecting sample at `n=ceil(exp L)` is needed. Its lag
`delta=log n-L` lies in `[0,exp(-L)]`. Extremal isolation forces `h_f(delta)=0`; local
preservation gives `h_G(delta)=0`. Apply the already certified ceiling-lag energy estimate,
which includes `delta=0` and zero-mass sources. No division or positive-mass hypothesis is used.
This is the final source-derived-threshold endpoint; the positive-mass statement above gives
its normalized and nearest-distance refinements. ∎

## Positive content and limitations

The exact-span obstruction exposes a uniform quantitative law: interior interference cannot
reduce the logarithmic cost forced by the outermost pair. The relevant large parameter is the
total span `mS`, not merely the adjacent separation `S`. A bounded normalized-energy family
cannot escape through longer finite trains satisfying these conditions, even with changing
seeds, coefficients, or packet counts.

Common seed and separation are structural conditions. For unrelated packet shapes the extremal
term is a cross-correlation and need not equal positive origin mass at zero. If packets are too
close, interior difference packets may reach the extremal window. Neither situation is covered.
No universal theorem for arbitrary polar sources or arbitrary superposed shapes is claimed.

## Audit boundary

Finite-sequence aperiodic autocorrelation and its endpoint product are classical; see
[Kai-Uwe Schmidt, *Sequences with small correlation*](https://arxiv.org/abs/1602.03722).
The no-cancellation-at-the-edge principle also has a broader support analogue in the
[Titchmarsh convolution theorem](https://arxiv.org/abs/2011.05420), which this elementary
finite-packet argument does not require.
The corpus contribution is the connected full-span logarithmic-grid energy law for actual
finite common-seed trains. No exhaustive literature-novelty claim is made.

Current corpus search: `/tmp/infinite-grid-train-search.txt`. Existing finite-sum and shifted
integral APIs were inspected. A private six-packet expansion in concurrent work was read as
context; the new general theorem does not depend on that module.

## Lean certification

`FiniteTranslationTrains.lean` certifies 9 theorems covering actual finite-source regularity,
the correlation expansion, local preservation, and extremal isolation.
`FiniteCopyTailRigidity.lean` certifies 6 theorems, ending with
`exists_copyTrain_infinite_grid_energy_barrier`, whose support threshold is derived from the
compact C² source. The normalized distance refinement is
`copyTrain_infinite_grid_distance_energy`; the division-free detecting-sample refinement is
`copyTrain_zero_linear_energy_cost`.

Both leaves passed `lake --old env lean` without diagnostics. The separate scratch audit
checked all 15 theorem dependencies: only `propext`, `Classical.choice`, and `Quot.sound`.
Both modules are wired into the field umbrella; all 15 names occur in the generated API.
`scripts/formal_tools.py lint` passed. Logs:
`/tmp/infinite-grid-train-{algebra,rigidity,axioms,index,lint}.log`;
scratch: `/tmp/infinite_grid_train_audit.lean`.
This is one significant connected package, fourth of the 100-package research objective.
