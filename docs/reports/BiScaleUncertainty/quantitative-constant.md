# Quantitative constant: shared origin and polar escape

Work in progress, 2026-10-17. Statements marked paper-proved below are not claims of completed Lean verification or of global extremal sharpness.

## Domain and normalization

Let `f` be a nonzero real smooth compactly supported function, `h(x)=∫f(u)f(u+x)du`, and `R=h(0)>0`. Put

\[
w(x)=e^{x/2}/\sinh x,\qquad E(h)=R^{-1}\int_0^\infty(R-h(x))w(x)\,dx.
\]

For an integer `N≥2`, let `C_N^0` be the infimum over this class with `h(log n)=0` for `2≤n≤N`, and `C_N^pol` the infimum with the additional condition `∫₀∞h(x)cosh(x/2)dx=0`. No common support radius is imposed; the source need not be even. The even-source variant is a distinct domain and is not silently identified with this one. These definitions make explicit the admissible class not specified by the notation in the field overview.

## 1. Exact shared-origin support function [paper-proved]

Let finite blocks `u_m=(u_mk)` share a coordinate `u0`, and suppose
`u0²+Σ_k u_mk²≤R²` in every block, with `R≥0`. For arbitrary real coefficients `W0,w_mk`, define

\[
q_m=\sqrt{\sum_k w_{mk}^2},\quad Q=\sum_m q_m,\quad S=\sum_{m,k}w_{mk}.
\]

Assume the block index set is nonempty. Then

\[
W_0(R-u_0)+\sum_{m,k}w_{mk}(R-u_{mk})
\ge R\left(W_0+S-\sqrt{W_0^2+Q^2}\right).\tag{1}
\]

Proof: set `r=√(R²-u0²)`, which is real because at least one block exists. Blockwise Cauchy–Schwarz gives `Σ_k w_mk u_mk≤q_m r`. Sum once over blocks, then apply two-dimensional Cauchy–Schwarz to `(u0,r)` and `(W0,Q)`. This bounds the linear reward by `R√(W0²+Q²)` and proves (1).

The coefficient is sharp for this relaxation. If `Q>0`, put `D=√(W0²+Q²)`, `u0=RW0/D`, and `u_mk=RQ w_mk/(D q_m)` when `q_m>0`, zero otherwise. Every nonzero-weight block saturates its sphere; zero-weight blocks remain feasible. The reward equals `RD`. If `Q=0`, all weights vanish, and `u0=R sign(W0)`, `u_mk=0` attains the bound (choose zero when `W0=0`).

For `W0>0`, rationalization yields the weaker but useful bound

\[
E_{\mathrm{tuple}}\ge R\left(S-\frac{Q^2}{2W_0}\right).\tag{2}
\]

Thus the cost is `(Σ_m ||w_m||₂)²/(2W0)`, including cross terms. Summing the old single-chain bounds with the full `W0` in every chain incorrectly counts origin energy repeatedly. Equivalently, the optimal allocation of origin weight is `W_m=W0 q_m/Q`; all nonzero blocks have the same ratio `W_m/q_m`. Sharpness here concerns the specified block spheres, not all positive-definite kernels.

## 2. An explicit N-dependent integrated bound [paper-proved]

Set `L=log 2` and `δ_n=log(n/(n−1))`. For `0<y<L`, group the active nodes

\[
A_m(y)=\{n:3\le n\le N,\ n=m2^k\text{ for some }k\ge0,\ m\text{ odd},\ y<\delta_n\}
\]

by their unique odd part. Let

\[
S_N(y)=\sum_{n=3}^N\mathbf1_{y<\delta_n}w(\log n-y),\quad
Q_N(y)=\sum_{\substack{1\le m\le N\\m\text{ odd}}}
\sqrt{\sum_{n\in A_m(y)}w(\log n-y)^2},
\]
\[
B_N=\int_0^L\left[w(y)+S_N(y)-\sqrt{w(y)^2+Q_N(y)^2}\right]dy.\tag{3}
\]

Then `C_N^pol≥C_N^0≥B_N`. Every block is a divisibility chain of zero nodes. Apply its origin-anchored sphere law, then (1), with origin coordinate `h(y)` and collar coordinates `h(log n−y)`. Integrate over `(0,L)`. Each node's active collar maps exactly to `(log(n−1),log n)`. These intervals partition `(log 2,log N)` up to endpoints and are disjoint from the origin interval `(0,log 2)`. Thus the integral of the tuple energy is exactly the energy on `(0,log N)`, with no multiplicity. The remaining tail is nonnegative.

Convergence: the integrand `K_N` satisfies `0≤K_N≤S_N`, because `Q_N≤S_N` and `w>0`. For fixed `N`, all collar arguments are at least `log 2`, so `S_N` is bounded. Away from finitely many `δ_n`, the integrand is continuous. This also justifies integrating the pointwise inequality despite the singular origin weight. `B_2=0`; `B_N>0` for `N≥3`, since an active positive collar gives `sqrt(w²+Q²)<w+S`.

Adding node `N+1` inserts weight `a≥0` into exactly one block. Its norm increases by `Δq≤a`; since `q↦sqrt(w²+q²)` is 1-Lipschitz for `q≥0`, `K_{N+1}−K_N≥a−Δq≥0`. Hence `B_N` is nondecreasing. It is an explicit rigorous quadrature formula depending only on `N`, not an evaluated numerical estimate.

The existing reflected-pair bound gives a second certificate

\[
F=\int_0^{L/2}\left[w(y)+w(L-y)-\sqrt{w(y)^2+w(L-y)^2}\right]dy>0.
\]

The integrand lies between zero and `w(L−y)`, so the endpoint integral exists. Folding `(0,L)` proves `C_N^0≥F`. Consequently

\[
\boxed{C_N^{pol}\ge C_N^0\ge\max\{F,B_N\}>0\quad(N\ge2).}\tag{4}
\]

These certificates cannot be added without allocating overlapping energy. No claim that (4) equals the optimal constant is made.

### Reflection allocation combines both certificates [paper-proved; Lean integration pending]

There is a stronger single family that budgets the overlap exactly. For `0≤β≤1`, take origin weight `Wβ(y)=(1−β)w(y)`. Include node `2` in the odd-part-`1` block for every `0<y<L`, with weight `a₂(y)=βw(L−y)`. For nodes `n≥3`, take `a_n(y)=1_{y<δ_n}w(log n−y)` as above. Define

\[
S_{N,\beta}(y)=\sum_{n=2}^N a_n(y),\quad
Q_{N,\beta}(y)=\sum_{m\text{ odd},m\le N}
  \sqrt{\sum_{\substack{2\le n\le N\\\operatorname{oddpart}(n)=m}}a_n(y)^2},
\]
\[
L_N(\beta)=\int_0^L\left[W_\beta(y)+S_{N,\beta}(y)
-\sqrt{W_\beta(y)^2+Q_{N,\beta}(y)^2}\right]dy.
\]

Then

\[
\boxed{C_N^{pol}\ge C_N^0\ge\max_{0\le\beta\le1}L_N(\beta)
\ge\max\{F,B_N\}.}\tag{9}
\]

Proof: the origin term contributes `(1−β)∫₀ᴸ(R−h)w`; the reflected node-2 term contributes `β∫₀ᴸ(R−h)w` by `x=L−y`. All other collars still partition `(L,log N)`. Thus the integrated tuple energy remains exactly the energy on `(0,log N)`. Apply (1). At `β=0` the certificate is `B_N`; at `N=2, β=1/2` it is `F` by reflection symmetry. Inserting further positive node weights can only increase the kernel, by the same block-norm argument used above.

Convergence and attainment of the maximum: choose `ε>0` small enough that all collar arguments are bounded away from zero for `0<y<ε`. There the kernel is bounded above by `S`, uniformly in `β`. Near `L`, all nodes `n≥3` are inactive because `δ_n≤log(3/2)<L`; only node 2 remains, and the kernel is bounded by `Wβ≤w(y)`, also uniformly in `β`. On the intervening compact interval all weights are bounded. These bounds give an integrable majorant independent of `β`. Dominated convergence makes `L_N` continuous on `[0,1]`, where it attains its maximum. No unknown function appears in (9).

The factor `β` is an explicit allocation of the origin interval, not a polar Lagrange multiplier. Formula (9) is sharp only at the fiberwise block-sphere step; finding compatible extremizing autocorrelations remains open.

## 3. Polar neutrality has no infimum cost on this domain [paper-proved; source theorem Lean-verified]

In fact

\[
\boxed{C_N^{pol}=C_N^0\quad\text{for every finite }N.}\tag{5}
\]

The source-class claim is now formalized by `polar_log_grid_lower_bound_iff` in
`DistantCopyPolarEnforcement.lean`. It proves equality of the sets of valid lower bounds for
every differentiability order at least two, including smooth sources. It assumes only the
displayed admissible-domain conditions, and constructs the polar replacement. The even-source
and full positive-definite-cone extensions below still require their own Lean bridges.

Fix any admissible `f`, choose `D>0` with `h(x)=0` for `|x|>D`, and take `T>D+log N`. Set `a=e^{-T/2}` and

\[
f_T(u)=f(u)-a f(u-T).
\]

The positive exponential moment is exactly zero:
`∫f_T(u)e^{u/2}du=(1−a e^{T/2})∫f(u)e^{u/2}du=0`.
Fubini and evenness of autocorrelation give
`2∫₀∞h_T(x)cosh(x/2)dx=(∫f_Te^{u/2})(∫f_Te^{-u/2})=0`.
Expanding the autocorrelation gives

\[
h_T(x)=(1+a^2)h(x)-a[h(x-T)+h(x+T)].\tag{6}
\]

At zero and at all prescribed grid nodes, both cross terms vanish. Thus `h_T(0)=(1+a²)R>0`, and all grid zeros are preserved exactly. On the positive half-line `h(x+T)=0`, hence

\[
E(h_T)-E(h)=\frac{a}{(1+a^2)R}\int_{T-D}^{T+D}h(x-T)w(x)\,dx.\tag{7}
\]

For `x>0`, `w(x)=2e^{-x/2}/(1-e^{-2x})`. For `T≥D+1`, it follows that

\[
|E(h_T)-E(h)|\le
\frac{2e^{D/2}\|h\|_1}{R(1-e^{-2})}\,e^{-T}.\tag{8}
\]

The construction preserves real smooth compact support. Its energy therefore converges to that of the arbitrary original test. Since the polar class is a subset, the reverse inequality of infima is automatic, proving (5). Both classes are nonempty: start with a nonzero smooth bump of support diameter less than `log 2`, then apply the construction. Energies are finite by the existing smooth compact-source integrability theorem.

The positive survivor is an exact constraint-enforcement operation with quantitative error (8), not merely a failure of one proof strategy. It explains why polar lobe balance alone cannot yield a strictly larger best constant on an unrestricted-support class. It does not exclude combined certificates that improve (4) while also bounding the nonpolar infimum. Common support bounds, or infinite zero grids, require separate analysis.

### Even sources and simultaneous cancellation [paper-proved; Lean pending]

The same infimum equality holds when the source is required to be even. Use instead

\[
b=\frac1{2\cosh(T/2)},\qquad g_T(u)=f(u)-b[f(u-T)+f(u+T)].
\]

Both exponential moments acquire the factor `1−2b cosh(T/2)=0`; source-evenness is preserved. Direct expansion gives

\[
h_{g_T}(x)=(1+2b^2)h(x)-2b[h(x-T)+h(x+T)]
+b^2[h(x-2T)+h(x+2T)].
\]

For `T>D+log N`, normalization is `(1+2b²)R` and the grid zeros are unchanged. Write `I_j=∫_{jT-D}^{jT+D}h(x-jT)w(x)dx` and `K_D=2e^{D/2}||h||₁/(R(1−e^{-2}))`. For `T≥D+1`, `|I_j|/R≤K_D e^{-jT/2}` and `b≤e^{-T/2}`. Thus

\[
|E(h_{g_T})-E(h)|
=\frac{|2b I_1-b^2 I_2|}{(1+2b^2)R}
\le K_D(2e^{-T}+e^{-2T}).
\]

This proves equality between the even-source polar and even-source nonpolar infima. It does not identify the even-source and unrestricted-source infima with each other. More strongly, imposing *both* exponential moments to vanish has no infimum cost within either source class.

### Full continuous positive-definite cone [paper-proved; Lean pending]

The polar/nonpolar infimum equality also holds in the field's full real continuous positive-definite cone, with finite increment energy. In the polar subclass require absolute integrability of `h(x)cosh(x/2)`. This extension does not assume a scalar smooth convolution root.

First take a compactly supported real positive-definite `h`, supported in `[-D,D]`. The transform (6) is positive definite directly: in a unitary representation `h(x)=⟨g,U_xg⟩`, replace `g` by `g−aU_Tg`. Expanding this inner product gives (6). Its bilateral exponential moment is

\[
\int_{\mathbb R}h_T(x)e^{x/2}dx
=(1+a^2-ae^{T/2}-ae^{-T/2})\int_{\mathbb R}h(x)e^{x/2}dx=0.
\]

Since `h_T` is real and even, this is twice its half-line hyperbolic moment. For `T>D+A`, the normalized correlation is **exactly unchanged on `[-A,A]`**. Equation (7) and estimate (8) still apply; compact support makes every tail integral finite, while exact local agreement preserves finiteness at the origin. Thus polar enforcement preserves all local normalized constraints, not only zero samples.

Now let `h` be any continuous real positive-definite kernel with finite `E(h)`. For `A≥1`, set

\[
p_A(x)=(1-|x|/A)_+,\qquad h_A(x)=h(x)p_A(x).
\]

The function `p_A` is the normalized autocorrelation of the indicator of `[0,A]`; products of positive-definite kernels are positive definite, as seen by tensoring their unitary representations. Hence `h_A` is continuous, positive definite, compactly supported, and preserves `h_A(0)=R` and every prescribed zero. Moreover `|h(x)|≤R` gives

\[
|E(h_A)-E(h)|\le\int_0^\infty\min(x/A,1)w(x)dx
\le\frac{M_w}{A},\qquad M_w=\int_0^\infty xw(x)dx<\infty.
\]

The finiteness of `M_w` follows from `xw(x)→1` at zero and exponential decay at infinity. This estimate also proves that `E(h_A)` exists. Apply the compact-support polar transform to `h_A`, then send `T→∞` and `A→∞` in that order. The polar infimum is at most the energy of every original admissible `h`; the reverse inequality follows from inclusion. This proves equality of the two infima on the full cone. The bounds (3), (4), and (9) already use only positive-definiteness and nonnegative integration, so they hold on this full domain as well (allowing `E=+∞` makes the lower bounds immediate there).

The finite-grid restriction matters: after tapering, only finitely many nonzero-position constraints must be preserved by choosing `T` beyond them. No conclusion about infinitely many prescribed zero nodes follows from this argument.

### Finite exponential-moment constraints are invisible to the infimum [core Lean-verified]

The mechanism is more general than the single polar moment. Fix any finite list of real rates
`β₁,…,β_m`, allowing zero, negative, or repeated rates. Within real smooth compactly supported
sources with any fixed finite logarithmic zero grid, imposing
`∫f(u)e^{β_j u}du=0` for all `j` leaves the infimum of `E(h_f)` unchanged.

For `T>D+log N`, form the translation polynomial

\[
P_T(z)=\prod_{j=1}^m(1-e^{-\beta_jT}z)=\sum_{k=0}^m c_k(T)z^k,
\qquad F_T(u)=\sum_{k=0}^m c_k(T)f(u-kT).
\]

Its moment multiplier at rate `β_j` is `P_T(e^{β_jT})=0`. Let
`r_l=Σ_{k=0}^{m-l}c_k c_{k+l}` for `0≤l≤m`. Since `c₀=1`, `r₀>0`, and expansion gives

\[
h_{F_T}(x)=r_0h(x)+\sum_{l=1}^m r_l[h(x-lT)+h(x+lT)].
\]

Thus `h_{F_T}(0)=r₀R`, and normalized local correlations agree exactly with `h/R` on every fixed
window once `T` is sufficiently large. For each `l`, Cauchy–Schwarz on the two overlapping
coefficient subvectors gives `|r_l|≤r₀`. Using `I_l=∫h(x-lT)w(x)dx` on the positive half-line,

\[
E(h_{F_T})-E(h)=-\frac1{r_0R}\sum_{l=1}^m r_l I_l,
\qquad
|E(h_{F_T})-E(h)|\le K_D\sum_{l=1}^m e^{-lT/2}\le mK_D e^{-T/2},
\]

where `K_D` is the same explicit constant as above and `T≥D+1`. The bound is independent of the
sizes and signs of the rates. Coefficients may grow exponentially when some rates are negative;
normalization by their squared norm controls every autocorrelation coefficient uniformly. This
also covers zero mean (`β=0`), where attenuation does not tend to zero.

The reverse inequality of infima follows from inclusion. All moments, supports, and local zeros
are enforced by the constructed source, without an interpolation-existence assumption. The empty
rate list is the identity operation. Repeated roots additionally give derivative moment
conditions, but no derivative-moment theorem is claimed here without its separate proof.

The prior corpus already has finite translate-symbol multiplication and a five-term filter for
rates `0,±1/2` in `SuzukiPolarTranslateMultiplier.lean`. The new claim here is simultaneous *exact
local normalized preservation and vanishing archimedean energy cost*, uniformly in the filter
coefficients, and the resulting infimum invariance for arbitrary finite real rate lists. The
filter algebra alone is not a new contribution.

An alternative proof, used for formalization, avoids polynomial bookkeeping. For a single copy
with any real coefficient `a`, the bound `|a|/(1+a²)≤1` and the exact energy identity imply

\[
|E(h_{f-a f(\cdot-T)})-E(h_f)|\le K_D e^{-T/2}.
\]

At rate `β`, choose `a=e^{-βT}`. Every exponential moment is multiplied by
`1−a e^{sT}`, so every existing zero moment remains zero. Cancel the finite rate list successively,
choosing each separation beyond the current support and the fixed local window, and splitting
the desired error tolerance between steps. The triangle inequality controls total energy error;
exact equality of normalized local correlations composes. This proves the same infimum theorem
even though the separations at different steps need not be equal. The single-polynomial
`mK_D e^{-T/2}` estimate above is a separate explicit representation of the construction.

The successive-cancellation proof is verified in `FiniteMomentEnergyInvariance.lean`:
`normalizedArchEnergy_subtractCopy_uniform_error`,
`exists_source_cancel_rates_local_energy_close`, and
`finite_moment_log_grid_lower_bound_iff`. The formal domain includes every real compact source
of differentiability order at least two, including smooth sources. All five theorems passed a
separate axiom audit with only `propext`, `Classical.choice`, and `Quot.sound`; an explicit smooth
specialization at rates `0,±1/2` also passed. The common-separation polynomial estimate above
remains paper-only. Neither proof imposes source-evenness or a common support bound.

## 4. Finite-vector rank removal without energy loss [Lean-verified]

Let `f₁,…,f_m` be arbitrary real compact `C^r` sources, `r≥2`, and put
`H(x)=Σ_j h_{f_j}(x)`, `J=Σ_j J_arch(f_j)`. For every finite `A≥0` there exists a real compact
`C^r` source `k` such that

\[
h_k(x)=H(x)\quad(|x|\le A),\qquad J_{\rm arch}(k)\le J.
\]

This is exact local agreement and energy domination, not an approximation. No component is
required to satisfy the grid zeros separately: cancellation in their sum is preserved.

**Two-source proof.** Suppose `f,g` vanish outside `[-D_f,D_f]`, `[-D_g,D_g]`. Choose
`T>D_f+D_g+A` and set `q(u)=g(u−T)`. If `|x|≤A`, both mixed products
`f(u)q(u+x)` and `q(u)f(u+x)` vanish pointwise. Therefore both `k₊=f+q` and `k₋=f−q`
have local correlation `h_f+h_g`. Translation invariance and the pointwise parallelogram
identity give

\[
h_{k_+}(x)+h_{k_-}(x)=2(h_f(x)+h_g(x)),\qquad
J_{\rm arch}(k_+)+J_{\rm arch}(k_-)=2(J_{\rm arch}(f)+J_{\rm arch}(g)).
\]

All four energy integrands are integrable for compact `C²` sources. Thus one sign has energy
at most the component sum. It has exactly the required local correlation. Induct over the finite
list, separating each new source from the previously constructed source. The empty list uses
the zero source. Local equalities compose, as do the energy inequalities.

**Sharp-constant consequence.** Taking `A≥log N` shows that finite-dimensional real vector
sources with total mass `H(0)>0` and `H(log n)=0` have exactly the same best normalized lower
bound as scalar sources. Every vector source is dominated by one scalar source with the same
mass and grid data; the converse uses one component. Arbitrary nonnegative weights are absorbed
into the components by multiplying each source by the square root of its weight. Polar and
finite-exponential-moment invariance then give the same constant for scalar sources with those
constraints, with arbitrary small energy tolerance when enforcing the moments afterward.

**Convexity consequence.** For fixed `A≥0`, consider pairs `(p,e)` for which a real compact
`C^r` source `f` has `h_f(0)=1`, `h_f(x)=p(x)` for `|x|≤A`, and `J_arch(f)≤e`. This set is
convex before taking any closure. Given two such pairs and weights `a,b≥0`, `a+b=1`, apply the
two-source construction to `√a f,√b g`. Its local profile is `a p+b q`, its mass is exactly one,
and its energy is at most `a e+b d`. Thus finite-grid affine constraints cut an actual convex
energy epigraph of scalar sources. Closedness, minimizer existence, and strong duality do not
follow from this argument and remain separate obligations.

`FiniteSourceEnergyScalarization.lean` verifies the pair and finite-list constructions,
`convex_localSourceEnergyEpigraph`, `finite_source_log_grid_lower_bound_iff`, and the composed
`polar_finite_source_log_grid_lower_bound_iff`. The direct leaf build and a separate audit of all
14 public theorems passed; axiom sets contain only `propext`, `Classical.choice`, and `Quot.sound`.
Explicit smooth-order specializations of the convexity and polar/vector equivalence passed.

**Prior-work boundary.** `EvenSectorSmoothSourceScalarization.lean` and
`EvenSectorWindowPurification.lean` already give exact whole-profile scalarization for smooth
complex even pole-free mixtures, even within a fixed support window. The present argument does
not replace that stronger specialized result. It supplies a direct real-source construction
for arbitrary differentiability order at least two, without source parity, entire factorization,
or spectral realization premises. It preserves bounded-window data and dominates energy while
allowing support enlargement. It does not establish scalar realization of every continuous
positive-definite kernel, spectral strong duality, or a globally sharp numerical constant.

## 5. Finite spectral envelope realization [paper-proved; Lean under audit]

Define `Ψ(ω)=∫₀∞(1−cos(ωx))w_arch(x)dx`. Existing corpus Lévy–Khintchine identities give
`Ψ(ω)=gammaBracket(ω)−gammaBracket(0)`. For a real compact `C^r` source `f`, `r≥2`, put
`R=h_f(0)>0` and consider the two actual real sources `f(u)cos(ωu)` and `f(u)sin(ωu)`.
The cosine subtraction identity gives their summed correlation exactly as `h_f(x)cos(ωx)`.
Consequently their total energy is

\[
J_{\cos}+J_{\sin}=R\Psi(\omega)+
\int_0^\infty (R-h_f(x))\cos(\omega x)w_{\rm arch}(x)\,dx.
\]

The last integral is absolutely convergent and its absolute value is at most `J_arch(f)`,
because `R−h_f(x)≥0` and `|cos(ωx)|≤1`. This bound is uniform in frequency.

For a finite probability list `μ=Σ_j p_j δ_{ω_j}`, let `m_μ(x)=Σ_j p_j cos(ω_j x)` and
`S(μ)=Σ_j p_j Ψ(ω_j)`. Scaling the two components at frequency `ω_j` by `√p_j` gives a real
finite-vector source with total correlation `h_f m_μ`, total mass `R`, and normalized energy

\[
\left|E_{\rm vector}-S(\mu)\right|\le E(f).
\]

Scalarize on any prescribed window `[-A,A]`, then enforce polar neutrality using §3. For every
`ε>0` this constructs an actual real compact `C^r` polar source `g` with

\[
\frac{h_g(x)}{h_g(0)}=\frac{h_f(x)}{R}m_\mu(x)\quad(|x|\le A),\qquad
E(g)<S(\mu)+E(f)+\varepsilon.
\]

If `m_μ(log n)=0` for `2≤n≤N`, choose `A≥log N`; all grid zeros hold exactly for `g`.
There is no approximate-zero repair premise. The scalar source only has the stated upper bound:
the two-sided error estimate belongs to the vector construction before the energy-decreasing
sign selection.

**Vanishing envelope error [paper proof; Lean pending].** Fix any nonzero smooth compact bump
`φ`, and set `f_L(u)=φ(u/L)` for `L>0`. Write `R_φ=∫φ²` and `D_φ=∫(φ′)²`, both finite and
`R_φ>0`. The fundamental theorem of calculus, Cauchy–Schwarz on the interval of length `|t|`,
and Fubini give

\[
\int_{\mathbb R}(\phi(u+t)-\phi(u))^2du\le t^2 D_\phi.
\]

Indeed the square is at most `|t|` times the integral of `(φ′)²` over the intervening interval;
integration in `u` counts each derivative value for an interval of length `|t|`. The exact
translation-norm identity and a change of variables therefore imply

\[
E(f_L)\le\frac{D_\phi}{2R_\phi L^2}
\int_0^\infty x^2w_{\rm arch}(x)\,dx\longrightarrow0.
\]

The weight moment is finite: near zero `x²w_arch(x)=O(x)`, and at infinity it decays
exponentially times a polynomial. The corpus already proves its integrability via
`integrableOn_sq_mul_archLevyDensity`, using `w_arch=2 archLevyDensity`.
Thus the sharp polar source constant is **at most** every feasible finite spectral cost `S(μ)`.
This is the upper realization direction. Equality with a spectral optimization still requires
the reverse Fourier-measure argument and an exact finite-atomic moment reduction; neither is
silently inferred here. A uniform-in-frequency error bound alone does not prove strong duality.

For formalization a weaker rate gives a shorter dependency chain. Compact `C²` regularity makes
`φ` globally Lipschitz, with constant `K`. Hence
`R_φ−h_φ(t)≤K ||φ||₁ |t|`, by writing the correlation difference as
`∫φ(u)(φ(u)−φ(u+t))du`. For `φ_δ(u)=φ(δu)`, `δ>0`, the exact autocorrelation identity is
`h_{φ_δ}(x)=δ⁻¹h_φ(δx)`. Therefore

\[
E(\phi_\delta)\le\delta\frac{K\|\phi\|_1}{R_\phi}
\int_0^\infty xw_{\rm arch}(x)\,dx\longrightarrow0.
\]

The first moment is finite because `xw_arch(x)≤(2x+1)e^{-x/2}` for `x>0`; this follows from
`1−e^{-2x}≥2x/(1+2x)`. A standard smooth compact bump with value one near zero supplies the seed,
with positive mass verified by continuity and positivity of Lebesgue measure on open sets.
This argument removes the envelope-energy premise and preserves smoothness; its `O(δ)` rate
does not claim the sharper `O(δ²)` paper estimate has been formalized.

Prior `WeilWorkPBAPJointProfiles.lean` already proves cosine/sine correlation modulation for
complex smooth sources. The elementary modulation identity is not counted as new. The useful
additional assertion is uniform archimedean energy control plus actual real polar scalar-source
realization of exact finite cosine-grid data.

## 6. Deformation correction

The correct identity is
`(R−h)w+μhc=Rw−h(w−μc)=(R−h)(w−μc)+μRc`, with `c=cosh(x/2)`.
The expression `R(w+μc)−h(w−μc)` adds an erroneous `μRc`; the current field overview no longer displays it. Beyond `w=μc`, the coefficient of the negative lobe in the lobe-split formula is negative. A local crossover floor cannot be integrated past that point as a nonnegative term. The existing Lean deformation identity and its explicit `μc≤w` premise are correct.

## Prior-work boundary

The internal search found existing one-chain leverage and folded-pair energy bounds, but no certified shared-origin block combination; search reported partial semantic coverage and source-only candidates. The finite-dimensional support function is elementary convex geometry, and its use here is a quantitative bridge, not a claim to a new general inequality. Classical positive-definite extremal theory includes [Kolountzakis–Révész, Turán's extremal problem on groups](https://arxiv.org/abs/math/0312218) and [pointwise extremal problems with prescribed support](https://arxiv.org/abs/math/0302193). Their abstracts establish this neighboring context; no exhaustive novelty verdict is inferred from that limited comparison.

## Remaining research

Shared-origin support, concrete polar enforcement, and arbitrary finite real moment enforcement
with local preservation, quantitative energy control, and finite-grid lower-bound equivalence
are Lean-verified. Finite real vector rank removal and convexity of the actual scalar local energy
epigraph are also verified. Next formalize the remaining full-cone/even-source extensions and, if useful,
the common-separation polynomial estimate; connect the verified adjacent collar transport to the
reflection-allocation certificate. Determine globally sharp constants
or matching asymptotics; (9) does not solve that problem. Maintain the requested 100-contribution
ledger without counting routine proof lemmas as separate advances.
