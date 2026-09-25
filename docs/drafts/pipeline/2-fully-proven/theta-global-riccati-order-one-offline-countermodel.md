# Global reflected Riccati positivity does not orient an order-one Fourier divisor

- **Stage:** 2-fully-proven (paper); Lean formalization and literature-novelty audit open.
- **Routes:** STC, CSB, U, K-RVM, MPLF, RHist.
- **Source comparison:** `ThetaCuspGlobalReflectedRiccati.lean` proves the same two-variable reflected Riccati sign for the literal completed theta source. This card proves that sign is not a zero-location mechanism by itself.
- **Corpus distinction:** `ThetaSourceStrictLogConcavityFluxNoGo.lean` already gives a log-concave modulated-Gaussian off-axis zero. Its theorem does not assert the global two-variable Riccati margin, order-one transform growth, or arbitrary local off-axis zero count proved here.
- **No RH conclusion.** No numerical computation is used.

## Theorem

For every positive integer `N`, every `η>0`, and every nonempty open real interval `I`, there is a strictly positive, even, real-analytic density `g` on the real line with all of the following properties:

1. `g` and all its derivatives decay faster than every ordinary exponential, its Fourier transform is entire of order at most one, and `log g` is globally strictly concave.
2. Put `ℓ=log g` and define the reflected action
   `A(u,t)=2ℓ(u)−ℓ(u+t)−ℓ(u−t)`. For every real center `u` and displacement `t>0`,
   `A(u,t)>0`, `A_t(u,t)>0`, `A_tt(u,t)>0`, and
   `2 A_t(u,t) A_tt(u,t)−A_ttt(u,t)>0`.
3. The entire Fourier transform `F(z)=∫_ℝ g(x)e^(izx) dx` has at least `N` distinct zeros in `Re z∈I`, `0<Im z<η`.

Because `g` is real and even, `F` is even and satisfies `F(conj z)=conj(F(z))`; its off-real zeros therefore carry the same reflection-quartet symmetry as a centered completed zeta function.

Thus even **global**, strict, two-parameter Riccati/correlation-angle curvature, together with source positivity, reflection, strong log-concavity, and order-one entire growth, does not force critical-line zeros. The literal theta source has further exact modular/Euler assembly absent here; this theorem does not test that assembly.

## Explicit family and spectral zeros

Choose `0<a<1/2`, put `A₀=arcosh(1/(2a))`, choose `L>A₀/η` sufficiently large that the odd-π lattice `{(2n+1)π/L : n∈ℤ}` has at least `N` points in `I`, and choose `σ≥2L`. Let

```text
hσ(x)=exp(−x²/(2σ²)),
g₀(x)=hσ(x)+a hσ(x−L)+a hσ(x+L),
gε(x)=exp(−ε(cosh(x/σ)−1)) g₀(x),       ε>0.
```

Gaussian Fourier translation gives

```text
F₀(z)=√(2π) σ exp(−σ²z²/2) (1+2a cos(Lz)).
```

For every integer `n`, `z_n=((2n+1)π+iA₀)/L` is a simple zero of `F₀`: `sin(Lz_n)=−i sinh A₀≠0`. The chosen `L` puts at least `N` of these zeros strictly inside `Re z∈I`, `0<Im z<η`. Choose disjoint closed disks around those `N` zeros lying inside that rectangle and containing no other zero of `F₀`. As `ε↓0`, `Fε→F₀` locally uniformly on the complex plane: on any compact spectral set, Gaussian decay of `g₀(x)` times `exp(R|x|)` dominates the integrands, while `0<exp(−ε(cosh(x/σ)−1))≤1`. Rouché's theorem on the selected disks gives one zero of `Fε` in each disk for every sufficiently small `ε>0`. This proves item 3 without asserting that one fixed `ε` retains infinitely many zeros.

The damping makes `gε` superexponentially decreasing and entire as a function of `x`. It also makes `Fε` order at most one. Indeed `g₀(x)≤C exp(−x²/(2σ²)+c|x|)`, where `c=L/σ²`, and `cosh(x/σ)≥exp(|x|/σ)/2`. For `|z|≤R`, discard the Gaussian and split the damping into equal halves. The elementary maximum of `s y−(ε/4)e^y` over `y≥0`, with `s=σ(R+c)`, is `Oε(s log(2+s))`; the remaining `exp(−(ε/4)e^y)` has a finite integral independent of `R`. Hence `log max_|z|≤R |Fε(z)|=Oε,σ(R log(2+R))`, which gives entire order at most one. The same tail bound after differentiation proves the stated decay of every source derivative.

## Uniform global Riccati margin

Write `b=a exp(−L²/(2σ²))`, `c=L/σ²`, and `δ=L/σ≤1/2`. Then

```text
log g₀(x)=−x²/(2σ²)+f(cx),
f(y)=log(1+b e^y+b e^(−y)).
```

The derivatives of `f` are cumulants of the three-point random variable `X∈{−1,0,1}` under probabilities proportional to `b e^(−y),1,b e^y`. Therefore

```text
0≤f''(y)=Var(X)≤1,
f''''(y)=E[(X−EX)^4]−3 Var(X)^2≥−3.             (1)
```

For `g₀`, use dimensionless center `y=cu`, displacement `v=ct`, and `K=δ^(−2)−1≥3`. Its reflected action is

```text
A₀(u,t)=v²/δ²+2f(y)−f(y+v)−f(y−v).
```

For `v>0`, (1) and the fundamental theorem of calculus give

```text
∂_v A₀≥2Kv,
∂_v² A₀≥2K,
f'''(y+v)−f'''(y−v)≥−6v.
```

Since `−∂_v³ A₀=f'''(y+v)−f'''(y−v)`, the actual `t`-derivative Riccati margin satisfies the **uniform strict bound**

```text
2(A₀)_t(A₀)_tt−(A₀)_ttt
  ≥ c³(8K²v−6v)
  ≥ 66 c⁴ t > 0.                                      (2)
```

Moreover `(log g₀)''≤−1/σ²+c²≤−3/(4σ²)`, so `g₀` is strongly log-concave. The reflected action is positive for `t>0`, and its first two displacement jets have the strict positive bounds above.

Now write the action of `gε` as `A=A₀+E`, with

```text
E(u,t)=2ε cosh(u/σ)(cosh(t/σ)−1).
```

For `t>0`, `E_t,E_tt>0` and `E_ttt=E_t/σ²`. Also `(A₀)_tt≥2(1/σ²−c²)≥3/(2σ²)`. Expanding the nonlinear margin gives

```text
2A_t A_tt−A_ttt
 = [2(A₀)_t(A₀)_tt−(A₀)_ttt]
   +2(A₀)_t E_tt+2E_t E_tt
   +E_t(2(A₀)_tt−1/σ²),
```

and every added term is nonnegative. Thus (2) holds unchanged for `gε`; its reflected action and first two jets are strictly positive. Finally `(log gε)''=(log g₀)''−(ε/σ²)cosh(x/σ)<0`. This closes every assertion of the theorem.

## Conjecture loop and survivor

- **Conjecture:** the literal theta source's global reflected Riccati law could orient its Xi zeros. **False as a sufficient source class:** the family above satisfies that exact strict law while having arbitrarily many off-real strip zeros.
- **Conjecture:** imposing order-one entire growth and superexponential source decay repairs the sign argument. **False:** positive hyperbolic-cosine damping preserves the Riccati margin and selected off-real zeros while enforcing both properties.
- **Mechanism:** the damping changes the transform's global order from two to at most one for every `ε>0`, yet its transforms converge locally uniformly to the undamped order-two transform as `ε↓0`. Any finite spectral window keeps its selected zeros. A global growth class therefore gives no local phase orientation unless its quantitative bounds are tied to the exact arithmetic source.
- **Positive survivor:** inequality (2) gives a quantitative family of globally Riccati-positive sources stable under the displayed superexponential damping. It separates the differential curvature law from the nonperturbative arithmetic phase. Any RH producer using this theta law must additionally use exact modular/Euler coefficients or an equivalent nonlocal constraint that this family violates. The surviving target is the source-selected connection value `B(z)=−H(−z)/H(z)` from `theta-one-port-variogram-pencil.md`, not another consequence of its finite reflected jets.

The paper proof is dependency-closed using elementary cumulant differentiation, Gaussian Fourier translation, Rouché, and the displayed tail estimate. The exact combined countermodel is not yet formalized in Lean. Literature novelty has not been established.
