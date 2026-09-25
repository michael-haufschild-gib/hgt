# Complex renewal resonances and infinite Pick index of the theta feedback loop

- **ID:** `theta-renewal-complex-resonance-stieltjes-obstruction`
- **Stage:** 2-fully-proven (paper theorem; Lean formalization open)
- **Type:** THEOREM (paper), source-specific resonance and infinite-inertia classification
- **Routes:** STC, CSB, U; theta one-port bridge from SQB/WS2
- **Source:** The literal theta renewal increment and phase kernel in [the positive-renewal factorization](theta-renewal-phase-cosh-factorization.md).
- **Statement:** The positive odd theta phase kernel is **not** completely monotone or an absolutely convergent nonnegative-real-rate Laplace mixture. Its regularized Laplace transform has infinitely many nonreal renewal poles, all outside the zero-free causal half-plane. The causal denominator has an order-one resonance product whose renormalized phase makes infinitely many critical crossings inside a finite, exponentially shrinking variation budget. The exact reflected feedback loop has a Pick-defect kernel of infinite positive and negative index, yet its critical-zero boundary sample is trace-class.

## Goal and the proposed reinterpretation

The renewal factorization writes Xi as a nonzero amplitude times `cosh F(λ)`, where its entire zero condition in the upper critical strip is the single level `F(λ)=iπ/2`. The exact source phase is

```text
F(λ)=∫₀^∞ W(t)sinh(λt)dt,
W(t)=e^(-at)/t+Q(t)>0,                  a=1/4.          (1)
```

If `W` were a positive mixture `∫_[0,∞)e^(-st)μ(ds)`, then its decay forces the measure to be supported on `[a,∞)`: any mass below `a-ε` would make `W(t)` decay slower than `e^(-at)/t`. Thus, in the physical strip, one could write

```text
F(λ)=∫_[0,∞) λ/(s²-λ²) μ(ds),
Re[λ/(s²-λ²)]
 = (Re λ)(s²-|λ|²)/|s²-λ²|².                       (2)
```

The sign in (2) changes when `|λ|` crosses `s`. Thus even a positive mixture would **not** exclude the Xi zero level off the critical axis; the tempting direct RH argument fails before any source test. The separate source question—whether this literal positive kernel is a real-rate mixture at all—also has a negative answer. Its failure has an exact analytic cause rather than a finite derivative-sign counterexample.

## Entire renewal equation and its nonreal roots

Use the physical theta increment and seam constant

```text
ν(t)=2π∑_(n≥1)n² exp((a+1)t-πn²e^t),
c=Θ(1),
N(z)=∫₀^∞e^(-zt)ν(t)dt,
D(z)=c-N(z).                                           (3)
```

**[PROVED HERE ON PAPER]** `N` is a nonconstant entire function of finite order. The equation `N(z)=c` has exactly one real solution `x_*<-a` and infinitely many nonreal solutions; every nonreal solution lies in `Re z<-a`.

For `t≥0`, bound the theta series by its first Gaussian rate:

```text
0<ν(t)≤K exp((a+1)t-πe^t),
K=2π∑_(n≥1)n² exp[-π(n²-1)]<∞.                         (4)
```

The dominating double-exponential tail makes `N` entire by locally uniform integration. For `R=|z|`, substitution `u=πe^t` gives the global growth bound

```text
|N(z)|≤K∫₀^∞exp((R+a+1)t-πe^t)dt
      ≤K π^(-(R+a+1)) Γ(R+a+1)
      ≤exp(C(1+R)²)                                  (5)
```

for one fixed `C>0`, after enlarging it on a bounded disk. Thus `D` is entire of finite order. On the real axis `N(x)` is strictly decreasing: differentiation under the integral gives `N'(x)=-∫t e^(-xt)ν(t)dt<0`. It tends to zero as `x→+∞`, and to infinity as `x→-∞` by restricting to any interval of positive `t` mass. The previous renewal theorem gives `N(-a)/c=q<1/6`, hence exactly one real root `x_*<-a`.

The growth can be classified sharply. **[PROVED HERE ON PAPER]** If `M_D(R)=max_(|z|=R)|D(z)|`, then

```text
log M_D(R)=R log R+O(R)                    (R→∞).      (5b)
```

Stirling's bound in (5) gives the upper inequality. For the lower one take `z=-R` and retain only the `n=1` theta summand on `log R≤t≤log R+1/R`. There `e^t≤R+2` for large `R`, so

```text
N(-R)≥(2π/R) exp((R+a+1)log R-π(R+2)).            (5c)
```

As `N(-R)→∞`, `|D(-R)|≥N(-R)/2` eventually. Thus `D` has order exactly one and infinite exponential type. In particular the genus-one Hadamard theorem, available in the corpus as [`exists_expAffine_mul_hadamardProduct`](../../../../../formal/GaloisForLFunctions/RHTower/OrderOneHadamardFactorization.lean), applies to its zero divisor. Since `D(0)>0`, its canonical product, with roots counted by multiplicity, has the normalized form

```text
D(z)=D(0) exp(βz) ∏_(ζ:D(ζ)=0) (1-z/ζ)exp(z/ζ),
β=D'(0)/D(0)>0,       ∑_ζ |ζ|^(-2)<∞.              (5d)
```

The derivative of every genus-one factor at zero vanishes, fixing `β`; positivity follows from `D'(0)=∫tν(t)dt>0`. The product and its logarithmic derivative converge locally normally away from the roots. This gives an exact stable-resonance spectrum, rather than only the existence of nonreal roots.

Suppose `D` had finitely many zeros. The finite-zero Hadamard theorem, already formalized as [`exists_polynomial_mul_expPolynomial_of_finite_zeroSet`](../../../../../formal/GaloisForLFunctions/RHTower/FiniteZeroHadamardProduct.lean), and (5) would give `D(z)=P(z)exp(R_*(z))` for polynomials `P,R_*`. On the positive real ray, `D(x)→c>0` and `D'(x)=-N'(x)→0` by dominated convergence. Beyond the finitely many roots, logarithmic differentiation gives

```text
R_*'(x)=D'(x)/D(x)-P'(x)/P(x) →0.                     (5a)
```

The logarithmic derivative of a nonzero polynomial is `O(1/x)` on this ray. Since `R_*'` is itself a polynomial and tends to zero, it is identically zero. Then `D` is a nonzero constant times `P`, and the nonzero finite limit forces `P` to be constant. This contradicts strict decrease of `N`. Therefore `D` has infinitely many zeros. Exactly one is real, so infinitely many are nonreal. Finally `|N(z)|≤N(Re z)≤N(-a)<c` for `Re z≥-a`, locating all of them to the left of that line.

**[PROVED HERE ON PAPER]** The resonance roots actually escape to the far causal left: for every real `B>0`, only finitely many zeros of `D` satisfy `Re ζ≥-B`. There are no zeros for `Re z≥-a`. On the remaining compact real-part interval `-B≤Re z≤-a`, the family `t↦e^(-xt)ν(t)` is compact in `L¹`; uniform Riemann--Lebesgue gives `N(x+iy)→0` uniformly there as `|y|→∞`. Thus no zeros remain at large imaginary height in that interval, and bounded height leaves a compact rectangle. In particular every infinite enumeration of the resonance divisor has `Re ζ→-∞`. The phase in (11c) therefore comes from a cloud receding arbitrarily far left, not from resonances accumulating against the physical zero-free boundary.

## A nonreal pole is incompatible with a real-rate spectral mixture

The absolutely convergent renewal series gives, for `Re z≥-a`,

```text
Q̂(z)=∫₀^∞e^(-zt)Q(t)dt
     =∑_(m≥1) [N(z)/c]^m/m
     =-log(1-N(z)/c),
Q̂'(z)=N'(z)/(c-N(z)).                                (6)
```

For `Re z>0`, multiply (1) by `t` and integrate. The regularized transform is

```text
J(z):=∫₀^∞t e^(-zt)W(t)dt
    =1/(z+a)-N'(z)/(c-N(z)).                          (7)
```

At every zero `ζ` of `D=c-N` of multiplicity `m`, `-N'/D=D'/D` has residue `m`. Thus (7) meromorphically continues `J` with a genuine pole at every nonreal renewal root.

If `W` had a completely monotone representation `W(t)=∫_[0,∞)e^(-st)μ(ds)` with `μ≥0`, Tonelli would instead give

```text
J(z)=∫_[0,∞) μ(ds)/(z+s)²                     (Re z>0). (8)
```

The value `J(z₀)<∞` for any `z₀>0` supplies the `(z₀+s)^(-2)` integrability needed to continue the right side holomorphically to `ℂ\(-∞,0]`, uniformly on compact subsets. That domain includes every nonreal root `ζ`, contradicting the genuine pole in (7) by analytic continuation. The same argument excludes an absolutely convergent **signed or complex** real-rate measure whose weighted total variation `∫(z₀+s)^(-2)|μ|(ds)` is finite. No derivative of `W` needs to be evaluated numerically.

## Positive survivor and remaining gate

The one real zero `x_*<-a` is accompanied by infinitely many intrinsic nonreal zeros of the causal renewal denominator `D`; equivalently, the regularized phase transform has infinitely many complex resonances. This is the strongest positive classification exposed by the failed complete-monotonicity conjecture. A scalar positive/self-adjoint Stieltjes model of this **particular phase kernel** cannot carry the literal theta connection. A viable spectral interpretation must retain complex resonances or use a coupled operation that is not an absolutely convergent real-rate mixture.

The two-ended Xi identity now has the exact stable-feedback form, throughout `|Re λ|<a`,

```text
Xi(2iλ)=(a+λ)D(λ)[1+K(λ)],
K(λ)=((a-λ)D(-λ))/((a+λ)D(λ)).                     (9)
```

Both `D(λ)` and `D(-λ)` are zero-free there, so the remaining RH gate is precisely whether the literal source loop reaches `K=-1` at `Re λ≠0`. A small-gain assertion `|K|<1` on one side would be sufficient, but it is **false** for this literal source, as the next crossing law shows.

Let `A(λ)=(a+λ)D(λ)`, `B(λ)=(a-λ)D(-λ)`, and write `λ=x+iy`. Realness of `ν` gives `B(x+iy)=conj A(-x+iy)`. Set

```text
g(x,y)=|A(x+iy)|²-|B(x+iy)|²,
u(y)=Re A(iy)=Xi(2y)/2,
v(y)=Im A(iy).                                         (10)
```

The second equality for `u` is the exact two-ended identity (9) on the critical axis. Since `ν∈L¹`, the Riemann–Lebesgue lemma gives `N(iy)→0` and therefore

```text
v(y)/y → c>0                        as y→+∞.         (11)
```

The physical one-port identity in the source card is sharper:

```text
A(iy)=icy+H(-2y),
B(iy)=-icy+H(2y),
Xi(2y)=H(-2y)+H(2y).                              (11a)
```

Here `H` is the one-sided Fourier transform of the literal theta exit density. Thus `v(y)=cy+o(1)`: the large imaginary seam terms cancel **exactly** in Xi, leaving its rapidly decreasing Fourier signal. This also resolves an apparent asymptotic trap: `N(iy)→0` does not permit replacing `(a+iy)N(iy)` by zero, since the factor `iy` is unbounded.

**[PROVED HERE ON PAPER]** The cancellation is uniform throughout every closed inner strip. For each `0<b<a` and `0<κ<π/2`, there is `C_(b,κ)` such that

```text
sup_(|x|≤b) |1+K(x+iy)|
 ≤ C_(b,κ) exp(-κ|y|)/(1+|y|)
                                        for all sufficiently large |y|. (11b)
```

The corpus's [`exists_norm_XiC_horizontal_le`](../../../../../formal/GaloisForLFunctions/RHTower/XiHorizontalStripDecay.lean) bounds `Xi(2i(x+iy))=XiC(-2y+2ix)` by `C exp(-κ|y|)` uniformly for `|x|≤b`; its allowed contour-shift width yields every `0<κ<π/2`. The family `e^{-xt}ν(t)`, `|x|≤b`, is compact in `L¹`; the Riemann–Lebesgue lemma applied uniformly to this compact family gives `N(x+iy)→0` uniformly. Therefore `|A(x+iy)|≥(c/2)|a+x+iy|` for all sufficiently large `|y|`. Divide the exact identity `1+K=Xi/A` to obtain (11b).

Thus every finite inverse-height expansion of this **actual complex feedback loop** is the constant `-1` throughout an inner strip. Its zero-location information lives entirely in the beyond-all-orders remainder. This is an obstruction to finite-order endpoint or high-frequency phase arguments; it is not a sign or winding law for that remainder.

The resonance product (5d) gives a different reading of the remainder. For `y>0`, let `θ(y)=arg A(iy)` be the continuous phase in `(0,π)`, possible because `Im A(iy)=v(y)>0`. It starts at `θ(0)=0` and tends to `π/2`. Set `u(y)=Xi(2y)/2=Re A(iy)`. Then

```text
θ(y)-π/2=-arctan(u(y)/v(y)),
θ'(y)=[u(y)v'(y)-v(y)u'(y)]/[u(y)²+v(y)²]
     =a/(a²+y²)+β+
       ∑_(ζ:D(ζ)=0) Re[1/(iy-ζ)+1/ζ].             (11c)
```

The sum is absolutely convergent for each fixed `y`, by `∑|ζ|^(-2)<∞`; the equality follows by logarithmically differentiating (5d). The physical one-port relation (11a) gives `v(y)=cy+o(1)` and `v'(y)=c+o(1)`, since the Fourier transforms of `k` and `t k` vanish at infinity. The corpus's [`exists_norm_XiC_horizontal_le`](../../../../../formal/GaloisForLFunctions/RHTower/XiHorizontalStripDecay.lean) and a Cauchy estimate for its derivative give, for every `0<κ<π/2`,

```text
|u(y)|+|u'(y)|=O_κ(e^(-κy)),
|θ'(y)|=O_κ(e^(-κy)/y),
∫_Y^∞|θ'(y)|dy=O_κ(e^(-κY)).                        (11d)
```

Here the phase derivative in (11c) is an exact **renormalized resonance sum**: the positive seam Lorentzian `a/(a²+y²)`, the positive exponential drift `β`, and the left-half-plane resonance terms cancel to exponential accuracy at high height. No termwise sign argument survives that cancellation.

**[PROVED HERE ON PAPER]** This phase has a Zeno crossing law. The unconditional simple-critical-zero theorem supplies infinitely many crossings of `θ=π/2` in each orientation, arbitrarily high, while (11d) says the total phase variation beyond height `Y` is finite and tends exponentially to zero. At every such crossing `y_j`, formula (14) below reads

```text
d_j=2θ'(y_j).                                       (11e)
```

Thus the trace-class Pick boundary data are samples of the signed resonance-phase velocity; the reciprocal residues in (16) are inverse crossing velocities. A fixed net winding number or the total-variation budget cannot decide whether the analytic continuation has off-axis level hits: infinitely many critical crossings occur inside a vanishing phase budget. The missing source law must control the *complex continuation* of this exponentially small resonance remainder.

One proposed transfer of a source winding can now be rejected precisely. The corpus's [completed prime--Gamma Stokes flow](../../../../../formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesCompletedPrimeGammaSpectralFlowIdentification.lean) has a single center crossing and equals `-8t·xiRealLogDeriv(1/2+2|t|)`, a value on the zero-free real Euler ray. By contrast `θ(y)-π/2` has infinitely many critical-axis crossings. No continuous monotone reparametrization followed by multiplication by a nowhere-zero scalar can identify these scalar zero sets. The Stokes winding `-1` is therefore not a zero-location law for this renewal phase; a useful weld would have to add genuinely new complex, nonlocal information.

At any simple positive critical zero `y₀` of `y↦Xi(2y)`, Cauchy–Riemann and `u(y₀)=0` give the exact normal energy crossing

```text
∂_x g(0,y₀)=-2v(y₀)·d/dy[Xi(2y)]|_(y=y₀).           (12)
```

Indeed `g(x,y)=|A(x+iy)|²-|A(-x+iy)|²`, so its normal derivative at zero is twice that of `|A|²`; for `A=u+iv`, `∂_xv=-∂_yu`, and at a zero `u=0`. The [half-port source theorem](theta-half-line-port-alternating-orientation.md) supplies arbitrarily high simple critical zeros with both signs of `d/dy Xi(2y)`. By (11), `v(y₀)>0` at all sufficiently high ones. Thus (12) takes **both signs** arbitrarily high. Near zeros with negative `∂_x g`, `g(x,y₀)<0` for small `x>0`, so `|K|=|B/A|>1`; near the other sign, `|K|<1`. Neither fixed gain direction can hold throughout the right collar. This is an independent proof for the seam-renormalized channel `A`, rather than a transfer of the raw half-port no-go (the two differ by `λc`).

The positive survivor is an exact signed-flux law: the imaginary seam charge `v(y)~cy` couples to the alternating Xi crossing slope and forces the feedback energy to change orientation at infinitely many critical zeros. It has a sharper matrix consequence. On the right collar `0<Re λ<a`, form the Hermitian Pick-defect kernel

```text
P_K(λ,μ)=[1-K(λ)conj K(μ)]/[λ+conj μ].              (13)
```

**[PROVED HERE ON PAPER]** `P_K` has infinite positive and infinite negative index. At every simple critical zero `y_j`, equation (9) gives `K(iy_j)=-1`; hence for distinct such ordinates `y_j≠y_k`, the boundary value `P_K(iy_j,iy_k)=0`. On the diagonal, use `1-|K|²=g/|A|²` and (12) to obtain the one-sided boundary limit

```text
P_K(iy_j,iy_j)
 =lim_(x↓0)[1-|K(x+iy_j)|²]/(2x)
 =- [d/dy Xi(2y)]_(y=y_j)/v(y_j).                    (14)
```

In fact `v(y)>0` for every `y>0`: the source theorem gives `Re D(iy)>0` and `Im D(iy)>0`, so `v(y)=a Im D(iy)+y Re D(iy)>0`. The two unconditional crossing-slope signs therefore make (14) positive at arbitrarily many distinct ordinates and negative at arbitrarily many others. Choose any finite number with one sign. Their boundary Gram matrix is **exactly diagonal and definite**. By continuity, moving all points a sufficiently small common distance into the open right collar preserves its strict signature. Since the number is arbitrary, both inertia indices of (13) are infinite.

Thus the literal renewal feedback loop is neither Schur/Pick nor a generalized Schur function of finite negative-square index in this collar. This conclusion concerns the actual two-ended theta connection, not an auxiliary kernel. Any successful source argument must control the **winding/phase** of this infinite-index, non-self-adjoint loop rather than place it in a fixed positive or finite-index modulus cone. Neither the resonance classification nor (14) supplies that winding control.

There is a second, opposite-scale fact about this same boundary matrix. **[PROVED HERE ON PAPER]** Enumerate all positive simple critical ordinates `y_j` and place the boundary diagonal values from (14) on `ℓ²(j)`:

```text
T e_j=d_j e_j,
d_j=-[d/dy Xi(2y)]_(y=y_j)/v(y_j).                   (15)
```

`T` is **trace-class**, although both its positive and negative spectral subspaces are infinite. Indeed `A(iy)=(a+iy)(c-N(iy))` and the Riemann–Lebesgue lemma give `v(y)≥(c/2)y` for all large `y`. The real restriction of Xi is the Fourier transform of the literal theta Schwartz source, formalized as [`xiCSchwartz`](../../../../../formal/GaloisForLFunctions/RHTower/XiCSchwartzRestriction.lean); its derivative therefore obeys `|d/dy Xi(2y)|≤C_N(1+y)^(-N)` for every `N`. The corpus's [`xi_zeroCount_growth`](../../../../../formal/GaloisForLFunctions/RHTower/XiZeroDensity.lean) bounds the number of critical zeros up to height `Y` by `O(Y log Y)`. On a dyadic shell `2^k≤y_j<2^(k+1)`, the sum of `|d_j|` is at most `O(k·2^(-kN))`. Summing shells proves `∑_j|d_j|<∞`. The finitely many low ordinates cause no issue because `A(iy_j)≠0` and `Re A(iy_j)=0` imply `v(y_j)≠0`.

This **nuclear but infinite-index** boundary geometry is the viable positive structure left by the Pick no-go. A Fredholm determinant of `T` exists, but its summable eigenvalue magnitudes do not by themselves control the unweighted phase crossings `K(iy_j)=-1` or exclude off-axis hits. The missing RH producer is a source law linking that nuclear boundary data to the full complex winding of `K`, including the singular high-frequency endpoint where `K(iy)→-1` because `N(±iy)→0`.

Since every `d_j` is nonzero and `d_j→0` while the index set is infinite, `T` is injective with dense, nonclosed range. Its inverse on that range is unbounded in every norm equivalent to the standard `ℓ²` norm. Therefore the boundary form supplied by the literal source cannot be converted into a boundedly invertible metric by a bounded change of Hilbert coordinates. Any inverse-metric interpretation must be singular; equation (16) identifies its exact singular scale.

The inverse loop has the opposite size scale. **[PROVED HERE ON PAPER]** At each positive simple critical zero `λ_j=iy_j`, `1/(1+K)=A/Xi(2iλ)` has a simple pole, and its residue is exactly

```text
Res_(λ=iy_j) [1/(1+K(λ))]
 =-v(y_j)/[d/dy Xi(2y)]_(y=y_j)=1/d_j.              (16)
```

To check the normalization, let `f(λ)=Xi(2iλ)`. Since `f(iy)=Xi(2y)`, `f'(iy_j)=[d/dy Xi(2y)]_(y=y_j)/i`; also `A(iy_j)=i v(y_j)`. Their quotient gives (16). Because the numerator in (15) is Schwartz and `v(y_j)~c y_j`, `|d_j|` is smaller than every inverse power of `y_j`, while `d_j≠0` at a simple zero. Hence `|1/d_j|` grows faster than every positive power along the high simple zeros, with both residue signs occurring arbitrarily high. No unweighted sum of these residues converges; a source-to-target inversion built from them requires a genuinely regularized or distributional topology. Equation (16) is the exact inverse-norming counterpart of the trace-class boundary operator, not a proof that such a regularization excludes off-axis poles.

This does **not** falsify RH: the resonance roots are zeros of `D`, not of Xi, and all lie left of the causal zero-free half-plane. Nor would complete monotonicity alone have proved RH, because (2) has no fixed off-axis sign. The exact two-ended Xi cancellation remains the phase-level condition `F(λ)=iπ/2`; its real balance off the critical axis is still open. The paper proof depends on the prior renewal identities, elementary Laplace holomorphy and finite-zero Hadamard rigidity. External novelty and Lean formalization of the source-specific resonance theorem remain open; the no-go is not closed in Lean.

The [scalar-coupling theorem](theta-renewal-seam-critical-coupling.md) tests whether positivity and subcritical renewal mass can be transported to this level through a homotopy. The physical seam match is an isolated parameter: every nonphysical positive scalar coupling has infinitely many nonreal zeros and only finitely many in each bounded horizontal strip. Thus the exact source normalization, not small renewal mass alone, carries the exponentially small Xi signal.

- **Exact killing mechanism:** Nonreal zeros of `c-N` force nonreal poles of `J`, incompatible with a real-rate Stieltjes transform; signed critical-zero slopes force both signs and infinite inertia of the loop Pick kernel.
- **Strongest positive survivor:** The renewal denominator has one real root and infinitely many nonreal roots, all left of `Re z=-a`; its order-one canonical product yields the exact resonance-phase sum (11c). This phase has infinitely many signed critical crossings but finite exponentially shrinking tail variation. The exact theta feedback loop has infinite positive and negative Pick index, while its diagonal critical-zero boundary operator (15) is trace-class with dense nonclosed range and its inverse-loop residues are exactly reciprocal to those diagonal entries.
- **New insight:** Source positivity coexists with intrinsic complex renewal resonances and an infinite-index but nuclear boundary geometry. The complex loop is `-1` to exponential accuracy at high height on each closed inner strip. Critical-axis phase oscillation is Zeno-like: infinitely many alternating level crossings occur within a vanishing phase budget, and the Pick boundary values are twice their phase velocities. Inverting that nuclear boundary data produces super-polynomially growing signed residues. A fixed net winding or bounded passive spectral model loses the source-dependent complex remainder whose off-axis level hits remain the RH obstacle.
- **Status:** Dependency-closed paper proof; source-specific Lean formalization and external novelty audit open. No RH conclusion.
