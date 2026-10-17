# Uniform logarithmic cost of compatible finite trains

## Intrinsic distance and statement

Fix any nonzero real vector `c_0,...,c_m` and `S>=2`. Let
`A_k=sum_{j-i=k} c_i c_j`, and let `K={k:1<=k<=m, A_k!=0}` be its positive active lags.
Define the finite, attained invariant

\[
\delta(c,S)=\min\bigl(\{1\}\cup\{d(kS):k\in K\}\bigr),
\]

where `d` is the certified nearest logarithmic-grid distance. Thus `delta=1` when `K` is empty.
The active-lag criterion says `delta>0` exactly for compatible train patterns.

**Uniform realization.** There is one real constant `C`, independent of `m`, `c`, and `S`,
such that every compatible pattern has an actual smooth compact positive-mass seed `f`,
correlation radius at most `1/2`, whose train `G(u)=sum_j c_j f(u-jS)` is smooth, compact,
positive-mass, and satisfies all logarithmic-grid zeros, with

\[
\frac{e^{-1/2}}4\log\frac1{\delta(c,S)}
\le E(G)\le C+\log\frac1{\delta(c,S)}.
\]

Every admissible positive-mass compact C² radius-half seed obeys the same lower bound,
as does its train. If `sum_j c_j exp(jS/2)=0`, the constructed train also has exact polar balance.
The leading lower and upper constants need not be optimal.

## Local normalized-correlation stability [PROVED HERE]

Let `f,g` be compact C² sources with positive origin masses `R_f,R_g`, and assume
`h_f(x)/R_f=h_g(x)/R_g` for `0<=x<=a`, where `a>0`. The normalized Lévy integrands

\[
F_f(x)=\left(1-\frac{h_f(x)}{R_f}\right)w(x)
\]

are integrable on `(0,infinity)`, nonnegative there, and bounded above by `2w(x)`.
These facts follow from the certified integrability and `|h_f(x)|<=R_f`.
Split both integrals into `(0,a]` and `(a,infinity)`. The first pieces agree. Each second
piece belongs to `[0,2W(a)]`, where `W(a)=integral_a^infinity w(x)dx<infinity`. Therefore

\[
|E(g)-E(f)|\le2W(a).
\]

No assumptions about the sources outside the local window are needed. For separated trains,
`h_G(x)=Qh_f(x)` on `[-1,1]`, `Q=sum c_j²>0`; hence
`|E(G)-E(f)|<=2W(1)`, independently of every coefficient and the number of packets. ∎

## Uniform narrow-source upper bound [PROVED HERE]

Fix once and for all the certified nonzero smooth compact bump `phi`, a correlation support
radius `D>0`, and its certified compression constant `A`, so
`E(phi(L .))<=A+log L` for `L>0` and `L>=D`.
For any `0<rho<=1`, put `L=(D+1)/rho` and `f_rho(u)=phi(Lu)`.
Then `L>=D`, origin mass is positive, and correlation vanishes outside radius `rho` because
`L*rho=D+1>D`. Consequently

\[
E(f_\rho)\le C_0-\log\rho,\qquad C_0=A+\log(D+1).
\]

The same constant works for every radius. Regularity and compactness come from the actual
dilation; no source-realization or modulus premise remains. ∎

## Finite minimum and lower cost [PROVED HERE]

Every active center `kS` is at least two. Hence each `d(kS)` is nonnegative and at most one,
and it is positive exactly when `kS` is off-grid. Since the finite set defining `delta` is
nonempty, `0<=delta<=1` and compatibility is equivalent to `delta>0`.
Moreover either `delta=1` or some active lag attains `delta=d(kS)`.

For an admissible seed, if `delta=1`, the claimed lower bound is zero and follows from energy
nonnegativity. Otherwise apply the certified active-lag energy bound at the attaining lag.
This proves the lower estimate for both seed and train, including the empty-active-set case. ∎

## Uniform actual train [PROVED HERE]

For a compatible pattern take `rho=delta/4` and the actual source `f_rho` above.
Since `0<delta<=1`, this gives `0<rho<=1/4`. At a positive active center,
every grid node is at distance at least `d(kS)>=delta>rho`; its packet therefore vanishes.
Inactive packets have coefficient zero. At nonpositive centers the distance to every positive
grid node is at least `log 2>=1/2>rho`. The exact grouped correlation thus vanishes at every
grid node. Local preservation gives `h_G(0)=Qh_f(0)>0`.

The stability theorem and narrow-source estimate give

\[
E(G)\le E(f_\rho)+2W(1)
\le C_0+\log4+2W(1)-\log\delta.
\]

Choose `C=C_0+log4+2W(1)`. It contains no train data. The finite-symbol moment theorem gives
exact polar balance whenever the half-exponential symbol vanishes. The preceding lower law
applies to this constructed train. ∎

## Meaning and audit boundary

Arbitrarily many translated packets and large coefficient cancellations do not introduce an
additional energy scale in this separated common-seed class: the worst active grid resonance
controls the growth order. The comparison constant is uniform even when packet counts and
coefficients change. This does not settle independently shaped or overlapping packets, nor
does it compare the unrestricted polar and nonpolar infima.

The finite-tail comparison is an elementary consequence of positivity and an integrable tail;
the logarithmic scaling input is already certified in `LogarithmicCompressionEnergy.lean`.
Logarithmic scaling itself has a classical counterpart in Lemma 2.5 of
[Laptev–Weth, *Spectral properties of the logarithmic Laplacian*](https://www.ma.imperial.ac.uk/~alaptev/Papers/laptev-weth-2020-revised.pdf).
That operator is distinct from the present archimedean functional; its theorem is context,
not a substitute for the source-level compression proof used here.
The new connected assertion is the uniform active-distance law for actual finite trains.

## Lean certification

`LocalCorrelationEnergyStability.lean` certifies 4 theorems, including the local energy
comparison and uniform smooth compression. `FiniteTrainUniformEnergy.lean` certifies 10
theorems, including the attained minimum, compatibility criterion, lower law, and endpoint
`exists_smooth_copyTrain_uniform_distance_cost`.

Both leaves passed direct `lake --old env lean` checks without diagnostics. Scratch
`/tmp/infinite_grid_uniform_audit.lean` audited all 14 theorem dependencies and the relevant
mathlib APIs: only `propext`, `Classical.choice`, and `Quot.sound` occur. Both modules are
wired into the field umbrella, and all 14 names appear in the generated API index.
Logs: `/tmp/infinite-grid-uniform-{local,train,axioms,index,lint}.log`.

Global formal lint reported one concurrent foreign module missing umbrella reachability:
`ProjectedHyperbolicGramControl`. Neither new module has a lint error. Repository-wide green
is not claimed; unrelated research was left untouched. This connected result is package 6
of the 100-package research objective.
