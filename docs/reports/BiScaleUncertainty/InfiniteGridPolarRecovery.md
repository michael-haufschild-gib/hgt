# Smooth polar recovery on the infinite logarithmic grid

## Target theorem

There exist `C` and an integer `N0` such that for every integer `N>=N0`, with
`T_N=(log N+log(N+1))/2`, there is a nonzero smooth compact source `k_N` whose canonical
polar copy `g_N(u)=k_N(u)-exp(-T_N/2)k_N(u-T_N)` satisfies every constraint
`h_gN(log n)=0` for `n>=2`, and

\[
\frac{e^{-1/2}}4 T_N\le E(g_N)\le C+T_N,
\qquad E(g)=\mathcal J_{\rm arch}(g)/h_g(0).
\]

Thus the linear separation cost is attainable in order. Neither coefficient is claimed optimal.
The polar moment vanishes exactly, not approximately. This theorem concerns actual scalar sources,
not a correlation relaxation or an assumed admissibility interface.

## Compression estimate [PROVED HERE]

For every nonzero compact C² source `f` with correlation support radius `D>0`, there is `A` such that

\[
E(f(\lambda\,\cdot))\le A+\log\lambda\qquad(\lambda\ge D). \tag{1}
\]

**Proof.** Put `R=h_f(0)>0`. The existing global source-Lipschitz argument supplies `M>=0`
with `0<=R-h_f(y)<=M|y|`. Also `R-h_f(y)<=2R` by correlation Cauchy–Schwarz.
Under scaling, `h_{f(lambda .)}(x)=lambda^{-1}h_f(lambda x)` and its origin energy is
`lambda^{-1}R`; hence the normalized integrand is `(R-h_f(lambda x))w(x)/R`.
Put `a=D/lambda<=1`. For `0<x<=a`, use `x w(x)<=(2x+1)exp(-x/2)<=3` to bound the
normalized energy contribution by `3MD/R`. For `x>a`, compact correlation support gives
`h_f(lambda x)=0`; the normalized integrand is exactly `w(x)`.

For `0<a<=1`, the exact existing weight-tail formula is
\[
\int_a^\infty w(x)dx=
\log\frac{1+e^{-a/2}}{1-e^{-a/2}}+2\arctan(e^{-a/2}).
\]
The elementary estimate `1-exp(-a/2)>=a/(2+a)>=a/3` gives the ratio at most `6/a`.
Since `arctan z<=pi/2`, the tail integral is at most `log(6/a)+pi`.
Use `a=D/lambda` to obtain (1), with
`A=3MD/R+log(6/D)+pi`. All energy integrals are integrable by compact C² regularity; the split
at `a` consists of disjoint intervals `(0,a]` and `(a,infinity)`. ∎

Without using a support radius, the same split at `1/lambda` and the bound `2R` gives the
auxiliary estimate `E(f(lambda .))<=A'+2log lambda` for `lambda>=1`. Both estimates are
formalized; only the stronger support estimate is used for the recovery family.

## Infinite-grid support geometry [PROVED HERE]

For `N>=1`, let `Delta_N=log(N+1)-log N`. Then
\[
\Delta_N\ge\frac1{N+1},\qquad
|\log n-T_N|\ge\frac{\Delta_N}{2}\quad(n\ge1).
\]

**Proof.** Apply `log z>=1-1/z` to `z=(N+1)/N`. For the second assertion, every integer
`n` is either at most `N` or at least `N+1`; use monotonicity of log in the two cases. ∎

Choose a fixed nonzero smooth compact source `f`, supplied by the existing bump construction.
Choose a correlation support radius `D>0`. Set
\[
\lambda_N=8(D+1)(N+1),\qquad k_N(u)=f(\lambda_Nu),
\qquad\rho_N=\frac1{8(N+1)}.
\]
Then `h_kN(x)=0` for `|x|>rho_N`, because `lambda_N rho_N=D+1>D`.
Every positive logarithmic grid node exceeds `rho_N`, since `log 2>=1/2>rho_N`.
Every node also stays at least `4rho_N` from `T_N`, by the preceding geometry. Finally
`log n+T_N>rho_N` when `T_N>=2`. Thus all three terms in
\[
h_{g_N}(x)=(1+e^{-T_N})h_{k_N}(x)
-e^{-T_N/2}\bigl(h_{k_N}(x-T_N)+h_{k_N}(x+T_N)\bigr)
\]
vanish at every `x=log n`, `n>=2`. This proves the entire infinite grid, without truncation.

## Energy and polar balance [PROVED HERE]

Take `N0=ceil(exp 2)`, so `T_N>=log N>=2` for `N>=N0`.
All `k_N` correlations have support radius at most one. The existing polar-copy error theorem
at radius one gives
`|E(g_N)-E(k_N)|<=P(k_N,1)exp(-T_N)`, where
\[
P(f,1)=\frac{2e^{1/2}\int|h_f(x)|dx}{R(1-e^{-2})}.
\]
Changing variables shows `integral |h_kN|=lambda_N^{-2} integral |h_f|` and
`h_kN(0)=lambda_N^{-1}R`. Therefore `P(k_N,1)=lambda_N^{-1}P(f,1)<=P(f,1)`.
Equation (1) and
`log lambda_N=log(8(D+1))+log(N+1)<=log(8(D+1))+log 2+T_N`
give the asserted upper bound, with
`C=A+log(8(D+1))+log 2+P(f,1)`.

The midpoints become arbitrarily large: choose `N>=ceil(exp B)` as well as `N>=N0` to obtain
`T_N>=log N>=B`. The source remains smooth and compact under scaling and translated-copy subtraction. The exact
polar-copy moment theorem gives `integral_0^infinity h_gN(x)cosh(x/2)dx=0`.
Its origin energy is `(1+exp(-T_N))h_kN(0)>0`. Finally `T_N>rho_N+1`, so the previous
two-copy barrier supplies the stated lower bound. This completes the paper proof.

## Scope and audit boundary

The family proves nonvacuity and order-sharpness of the separated-copy energy obstruction.
It does not identify the optimal leading coefficient, prove the general distance-to-grid law,
or control interference among more than two packets. These remain open.

Logarithmic scaling costs are classical: see
[Laptev–Weth, *Spectral properties of the logarithmic Laplacian*, Lemma 2.5](https://www.ma.imperial.ac.uk/~alaptev/Papers/laptev-weth-2020-revised.pdf).
The corpus contribution is the connected infinite-grid polar family with both energy bounds.
No exhaustive literature-novelty claim is made.

## Lean certificates and verification

`LogarithmicCompressionEnergy.lean` proves the integrable weight tail, explicit logarithmic
tail bound, both compression estimates, and exact scaling of the polar error constant.
`InfiniteGridPolarRecovery.lean` proves the midpoint geometry and the complete source endpoint
`exists_smooth_infinite_grid_polar_recovery`. The separate theorem
`exists_arbitrarily_large_logarithmicMidpoint` verifies unbounded separation.

Both leaves passed `lake --old env lean` with no diagnostics. Scratch audit
`/tmp/infinite_grid_recovery_audit.lean` checked every one of the 17 new theorems: only
`propext`, `Classical.choice`, and `Quot.sound` occur. Mathlib names were checked against the
installed toolchain in that scratch file. Both modules are imported by the field umbrella;
the refreshed generated API contains all 17 theorem names. No numerical experiments, new
axioms, heartbeat overrides, or full builds were used.

Audit logs: `/tmp/infinite-grid-compression-build.log`, `/tmp/infinite-grid-recovery-build.log`,
`/tmp/infinite-grid-recovery-axioms.log`, `/tmp/infinite-grid-recovery-index.log`.
The global lint check is recorded separately in `/tmp/infinite-grid-recovery-lint.log`;
its unrelated failures do not constitute a green repository-wide gate.
The final run reports six concurrent modules missing umbrella reachability:
`NonTemperedShiftedZetaPairCountermodel`, `WeilConeMismatchWitnesses`,
`ZeroCountRemainderNotIntegrable`, `LogarithmicPathKernel`, `PairedCosetSphereDuality`, and
`SignedCosetProductCoupling`. Neither new module has a lint error.
