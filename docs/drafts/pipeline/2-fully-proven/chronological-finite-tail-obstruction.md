# A fixed smooth tail space cannot repair a proportional Möbius prefix

**Paper proof complete; Lean formalization pending.** This is a restriction on
one explicit family, not a refutation of bounded chronological repair [R].
No numerical estimate, RH assumption, or simple-zero assumption is used.

## Exact theorem

Fix 0<θ<1 and a finite-dimensional real subspace V⊂C¹([θ,1]). Put

    r_(N,f)(t)=exp(−t)+Σ_(1≤k≤θN) μ(k)h(kt)
                         +Σ_(θN<k≤N) f(k/N)h(kt),
    h(t)=1/t−1/(exp(t)−1),
    E_N=inf_(f∈V) ||r_(N,f)||_(L²(0,∞)).

There exists ε>0 such that E_N≥ε for arbitrarily large N. Tail coefficients
may be arbitrarily large; no bound on f or its coordinates is needed.

In particular, least-coefficient-norm moment repair with a fixed number m of
moments cannot converge in full L². Its tail lies in
span{x⁻¹,1,x,x³,…,x^(2m−1)} on [1/2,1]. Increasing m remains an open option.

## Proof

Work in the complex Hilbert space H=L²([1,2],du), with inner product
⟨v,w⟩=∫conj(v)w. Choose one zero ρ of ζ with Re ρ=1/2, supplied
unconditionally by Hardy's theorem. For f∈V define

    F_f(u)=∫_θ¹ f(x)h(xu)dx,
    K_ρ(u)=∫₀^θ x^(ρ−1)h(xu)dx,
    W=complex span{F_f : f∈V}⊂H.

**1. Separation.** K_ρ does not belong to W. All these functions are real
analytic in u>0: h extends analytically across zero, and on each compact
positive u-interval its complex extension is uniformly bounded for 0≤x≤1.
Equality in H would therefore give equality for every u>0, by continuity
and the analytic identity theorem.

For real 0<s<1/2, absolute Fubini and substitution then give

    [∫₀∞ h(y)y^(s−1)dy] θ^(ρ−s)/(ρ−s)
      = [∫₀∞ h(y)y^(s−1)dy] ∫_θ¹ f(x)x^(−s)dx

for some complex linear combination f of V. Absolute convergence follows
from |h(y)|≤min(1,1/y) and Re ρ=1/2. The bracket is strictly positive,
since h(y)>0 for y>0. Cancel it. The right side after cancellation extends
to an entire function of complex s. The left side is analytic on Re s<1/2.
The complex identity theorem extends the equality to that half-plane.
Taking s=ρ−δ, δ↓0, makes its left side θ^δ/δ unbounded and its right side
bounded. Contradiction.

The same Mellin argument shows that f↦F_f is injective on C¹([θ,1]):
if F_f=0, the entire function ∫_θ¹ f(x)x^(−s)dx is zero. At s=−n its
values are all polynomial moments. Polynomial density on [θ,1], applied
separately to real and imaginary parts, gives f=0. Thus a basis of V maps
to a linearly independent basis of W.

Let Q be projection onto W-perp, d=||QK_ρ||>0, and ψ=QK_ρ/d. Then
||ψ||=1, ψ⊥W and ⟨ψ,K_ρ⟩=d.

**2. Exact discrete annihilation, independent of coefficient size.** For a
basis f₁,…,f_l of V set

    F_(j,N)(u)=N⁻¹Σ_(θN<k≤N) f_j(k/N)h(ku/N),
    W_N=span_C{F_(j,N)},
    ψ_N=Q_N K_ρ/||Q_N K_ρ||,

where Q_N projects onto W_N-perp. Ordinary C¹ Riemann-sum estimates,
including the partial cell at θ, give ||F_(j,N)−F_(f_j)||_H=O(1/N).
The limiting Gram matrix is positive definite by step 1. The explicit
finite Gram inverse formula for projection therefore gives
||Q_N−Q||_(H→H)=O(1/N). For large N the denominator defining ψ_N is
at least d/2, so ||ψ_N−ψ||_H=O(1/N). Every ψ_N has norm one and
annihilates the entire discrete tail exactly. This is why no bound on
the coefficients is required.

Define H₀(x)=∫₁² conj(ψ(u))h(xu)du, using h(0)=1/2. It is C¹ on
[0,1]. For real X≥1 put T(X)=Σ_(1≤k≤θX) μ(k)H₀(k/X).
Pair r_(N,f)(u/N)/sqrt(N) with ψ_N. The tail is zero. The target
exp(−u/N) contributes at most 1/sqrt(N). Replacing ψ_N by ψ in the
head contributes O(1/sqrt(N)): use |μ(k)|≤1, bounded h on [0,2],
at most N terms, and ||ψ_N−ψ||=O(1/N). Change variables t=u/N in
Cauchy–Schwarz to obtain, uniformly over every f∈V,

    |T(N)|/sqrt(N) ≤ ||r_(N,f)||₂ + O(N⁻¹/²).                 (A)

Taking the infimum over f is valid because the remainder is independent
of f. If E_N→0, this implies T(N)=o(sqrt(N)). For N≤X<N+1,
the boundedness of H₀ and H₀′ gives T(X)−T(N)=O(1): at most one new
term appears since θ<1; the changes in existing arguments total O(1).
Hence T(X)=o(sqrt(X)) for real X→∞.

**3. The critical zero prevents that weighted Möbius limit.** Let

    B(s)=∫₀^θ H₀(x)x^(s−1)dx,
    A(s)=∫₁∞ T(X)X^(−s−1)dX.

B is analytic on Re s>0. Under the conclusion of step 2, A is analytic
on Re s>1/2, by locally uniform domination, including logarithmic
derivatives. For Re s>1, absolute Fubini and the absolutely convergent
Möbius Dirichlet series give A(s)ζ(s)=B(s). Multiplying by s−1 removes
the sole pole of ζ. The identity theorem extends that product identity
to Re s>1/2, and hence A(s)ζ(s)=B(s) away from s=1.

For δ>0, direct head/tail splitting proves δ A(ρ+δ)→0: the bounded
head contributes O(δ), and |T(X)|≤η sqrt(X) beyond a fixed threshold
gives δ∫_X₀∞ |T(X)|X^(−3/2−δ)dX≤η X₀^(−δ)≤η.
Analyticity and ζ(ρ)=0 give ζ(ρ+δ)=O(δ), with no simplicity assumption.
Thus B(ρ)=lim_(δ↓0)ζ(ρ+δ)A(ρ+δ)=0. But absolute Fubini on compact
u and integrable x^(−1/2) gives

    B(ρ)=⟨ψ,K_ρ⟩=d>0,

a contradiction. Therefore E_N does not tend to zero. Since E_N≥0,
some positive ε occurs as a lower bound cofinally. This proves the theorem.

## Positive survivor and quantitative boundary

The nonzero invariant d=dist_H(K_ρ,W) measures the component of the
critical arithmetic profile that the fixed tail space cannot absorb.
Equation (A) is a uniform observation inequality for the actual residual.
It is stronger than failure of a particular interpolation algorithm.

More precisely, if L=limsup E_N is finite, the same proof gives
limsup_(δ↓0)|δ A(ρ+δ)|≤L. If ζ′(ρ)≠0, the product identity gives

    L ≥ d/|ζ′(ρ)|.

If ζ′(ρ)=0, finite L would give B(ρ)=0, so L=∞. These alternatives
require neither a selected numerical zero nor knowledge of multiplicity.
They concern limsup, not liminf or an eventual positive floor.

For any successful arrays with a fixed proportional Möbius prefix, their
tail samples must leave every fixed smooth finite-dimensional model
cofinally. For nested polynomial models their degree cannot stay bounded
eventually. This does not prove that degree tends to infinity along every
subsequence, or supply a growing-degree convergence estimate.

## Audit and remaining work

This paper argument uses only classical analyticity/Fubini, C¹ quadrature,
finite-dimensional projection, the Möbius Dirichlet identity and one Hardy
zero. Every estimate above retains the actual integer cutoff and half-line
L² norm. No continuous model replaces the discrete tail: ψ_N annihilates it
exactly, and only the bounded Möbius head pays the projection error.

Lean dependencies not yet implemented: the weighted Möbius critical-zero
obstruction for compact C¹ weights; heat-transform separation; quantitative
Gram projection under this Riemann discretization; the actual residual
observation inequality. Existing raw-Laplace obstruction is not a substitute
for these general weighted dependencies. Do not mark this result formalized
until the entire theorem and the invariant/observation survivor are checked.

No route is retired on the strength of this paper-only result. Growing m
in [K], arbitrary bounded arrays [R], and positive arithmetic averaging remain
open. Next hardest question: quantify coefficient and full-error costs with
m growing, while formalizing this exact fixed-space boundary.

**Literature/priority.** Classical natural-approximation divergence is treated
by [Báez-Duarte, 2002, §4](https://www.kurims.kyoto-u.ac.jp/EMIS/journals/HOA/IJMMS/Volume31_7/242719.pdf).
The present argument is recorded for this literal smooth-tail family; the
search did not establish priority, and no novelty claim is made.
