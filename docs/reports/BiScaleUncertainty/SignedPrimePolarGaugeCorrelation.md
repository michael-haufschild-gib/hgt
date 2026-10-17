# Exact gauge energy of a collar and correlation-only packet control

Let f be any real compact continuous source, h its autocorrelation, R=h(0),
A=exp(a), d=exp(b), and g(u)=d⁻¹∫_[A,A+d]f(u-y)dy. Previous work constructs
g as a compact C¹ source, its slope s(u)=(f(u-A)-f(u-A-d))/d, and k=s-g/2.
Write B=∫g² and T=multiplierSourceRadius f, an existing positive support radius
derived from f. No derivative of f is assumed.

## Exact energy law and support budget

For every f,a,b,

∫s²=2(R-h(d))/d²,   ∫sg=0,

**∫k²=2(R-h(d))/d²+B/4.**

Changing A only translates g, so B and the displayed gauge energy depend on the
width d, not the positive collar position A. Moreover k vanishes outside
[A-T,A+d+T]. Consequently

**(∫|k|)²≤(2T+d)[2(R-h(d))/d²+B/4].**

This exposes the exact correlation cost of smoothing: the single-width deficit
R-h(d), scaled by d⁻², and one quarter of the coherent collar energy. The interval
position affects the error between f and g but not this gauge-energy budget.

## Dependency-closed proof

The verified shift-chord identity gives
∫(f(u-A)-f(u-A-d))²du=2(R-h(d)). Divide by d² to obtain the slope energy.
Since g is an actual compact C¹ source, (g²)'=2sg is continuous and compactly
supported. The integral of this derivative is zero, hence ∫sg=0. Expanding
(s-g/2)² and integrating gives the exact gauge energy; every integrand is
continuous and compactly supported, so all integral expansions are justified.

For positions A and A', moving-integral coordinates give
g_A(u)=g_A'(u+A'-A). Translation invariance of Lebesgue measure proves that B
is independent of A. The gauge energy formula then proves the same for ∫k².

If u lies outside [A-T,A+d+T], then for every y in [A,A+d] the point u-y lies
outside [-T,T]. Thus g(u)=0. The endpoint translates f(u-A) and f(u-A-d)
also vanish there, so s(u)=k(u)=0. Both |k| and k² are integrable, and their full
integrals equal the integrals over that interval. Apply integral Cauchy–Schwarz
to |k| and the constant 1 on the interval. Its length is exactly 2T+d. Substitute
the exact gauge energy to obtain the L¹ budget. This also covers f=0.

## Consequence for actual signed transport

Let E₂=∫₀ᴸ exp(-x)(ψ(exp x)-exp x)²dx, L=log(N+2), e_L=exp(-L/2)(ψ(exp L)-exp L),
δ=R+B-2H(0), and define

U_N=6(10+e_L²)B
 +6(2T+d)[2(R-h(d))/d²+B/4]E₂ +2M_N²δ.

Contribution 5 gives the same upper bound with (∫|k|)² in place of its new
explicit budget. Since E₂≥0, substitution gives Q_N(f)≤U_N. At every source-
admitted cutoff N=N₀(f)+K, the global Lévy–sinh transport theorem therefore gives,
for arbitrary independent transport parameters u,v,c,

|D∞(h)-W∞(u,v)| ≤ exp(c)J(u,v)
 +U_N/(2exp(c)exp(2v))∫_[exp(u),exp(u)+exp(v)]exp(-y/2)sinh(y)dy.

The reciprocal penalty is nonnegative on the actual positive annulus, so the
substitution is valid. All quantities come from f, its correlation, the actual
arithmetic error, and numerical parameters. There are no added analytic premises.

## Boundary

This is one package: exact gauge geometry, its source-derived support budget,
and elimination of the gauge-cost interface in signed transport. The actual
roughness term remains; no cutoff-uniform packet bound or arithmetic asymptotic
is claimed. T need not be the minimal support radius. No external novelty claim.
Formal verification is pending.
