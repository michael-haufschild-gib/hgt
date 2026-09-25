# Exact scalar theta charges do not repair global Riccati zero control

- **Stage:** 2-fully-proven on paper; Lean formalization and external novelty audit open.
- **Routes:** CSB, K-RVM, MPLF, STC, U.
- **Comparison:** Strengthens [global Riccati countermodel](theta-global-riccati-order-one-offline-countermodel.md) by matching ordinary mass and both reflected half-density charges of the literal completed theta source exactly. It does not match Euler coefficients, the entire real-zero divisor, or all-sieve laws.
- **No RH conclusion.** No numerical computation is used.

## Theorem

For every `0<M<Q` and `η>0`, there is a strictly positive, even, real-analytic density `g` on `ℝ` such that:

1. `∫g=M` and `∫exp(x/2)g(x)dx=∫exp(-x/2)g(x)dx=Q`.
2. `g` and all its derivatives decay faster than every ordinary exponential, `log g` is globally strongly concave, and its Fourier transform `F(z)=∫g(x)exp(izx)dx` is entire of order at most one.
3. For `A(u,t)=2log g(u)-log g(u+t)-log g(u-t)`, all real `u` and `t>0` satisfy `A,A_t,A_tt>0` and `2A_t A_tt-A_ttt>0`.
4. `F` has a nonreal zero with `0<Im z<η`. Evenness and reality give its reflection quartet.

For the literal completed theta source `φ=thetaCuspFullSource`, the corpus proves `φ(x)>0`, `φ(-x)=φ(x)`, and `∫exp(x/2)φ(x)dx=1/2` (`ThetaCuspReflection.lean`, `PrimeArchThetaWardLaplaceHalfDensity.lean`). Hence its ordinary mass `Mθ=∫φ` obeys `0<Mθ<1/2`: by evenness the charged integral is `∫cosh(x/2)φ(x)dx`, strictly larger than `∫φ` because `cosh(x/2)>1` off zero. Taking `(M,Q)=(Mθ,1/2)` matches all three literal scalar budgets. The constructed density is still not the theta source.

## Charge fitting and surviving zero

Fix `L/σ=1/2`. For `0<a<1/2`, define `hσ(x)=exp(-x²/(2σ²))`, `L=σ/2`, and `g₀(a,σ;x)=hσ(x)+a hσ(x-L)+a hσ(x+L)`. Gaussian integration gives

```text
R₀(a,σ)=[∫exp(x/2)g₀(a,σ;x)dx]/[∫g₀(a,σ;x)dx]
       =exp(σ²/8)[1+2a cosh(σ/4)]/(1+2a).             (1)
```

For every fixed `0<a≤1/2`, `σ↦R₀(a,σ)` is continuous and strictly increasing from `1` to infinity: the logarithmic derivative of (1) is `σ/4+(a/2)sinh(σ/4)/(1+2a cosh(σ/4))>0` for `σ>0`. Given `R=Q/M>1`, it has a unique solution `σ(a)>0` to `R₀(a,σ(a))=R`. As `a↑1/2`, `σ(a)` tends to the unique positive solution `σ*` of `R₀(1/2,σ*)=R`, while `A_a=arcosh(1/(2a))↓0`. Choose `a<1/2` close enough to `1/2` that `2A_a/σ(a)<η`.

The Gaussian Fourier formula is

```text
F₀(a,σ;z)=√(2π)σ exp(-σ²z²/2)[1+2a cos(σz/2)].
```

It has a simple zero at `z₀=(2π+i2A_a)/σ(a)`, strictly in `0<Im z<η`.

Introduce order-one damping `bε(a,σ;x)=exp[-ε(cosh(x/σ)-1)]g₀(a,σ;x)` for `ε>0`, and let `Rε(a,σ)` be its positive half-charge divided by its ordinary mass. On compact positive `σ` intervals, Gaussian domination proves continuity of `Rε` and local uniform convergence `Rε→R₀` as `ε↓0`. Strict monotonicity of `R₀` gives arbitrarily close endpoints on opposite sides of `R`; the intermediate-value theorem supplies `σε` between them with `Rε(a,σε)=R` for all small `ε`. Every such choice satisfies `σε→σ(a)` as `ε↓0` by compactness and uniqueness of the `R₀` root.

The transforms of `bε(a,σε;·)` converge to `F₀(a,σ(a);·)` locally uniformly in `z` by the same domination. Choose a disk around `z₀` inside `0<Im z<η` containing no other `F₀` zero. Rouché gives a zero of the damped transform in that disk for all sufficiently small `ε>0`. Finally set `Cε=M/[∫bε(a,σε;x)dx]` and `g=Cε bε(a,σε;·)`. Then `∫g=M`, its positive half-charge is `MR=Q`, and its negative half-charge is `Q` by evenness. Multiplication by `Cε>0` changes neither logarithmic derivatives nor zeros.

## Global Riccati law and growth

For every `a,σ` here, `L/σ=1/2`. The prior countermodel's three-point cumulant proof applies: for `f(y)=log(1+b e^y+b e^-y)`, `0≤f''≤1` and `f''''≥-3`. With `c=L/σ²` and `K=(L/σ)^-2-1=3`, its reflected action satisfies

```text
2(A₀)_t(A₀)_tt-(A₀)_ttt ≥ 66c⁴t>0,
(log g₀)''≤-3/(4σ²),       (A₀)_tt≥3/(2σ²).
```

Damping adds `E(u,t)=2εcosh(u/σ)(cosh(t/σ)-1)` to the action. Its first two displacement jets are positive and `E_ttt=E_t/σ²`; expanding the margin makes every added term nonnegative because `2(A₀)_tt-1/σ²>0`. Thus the strict Riccati inequality and positive action jets persist. Damping subtracts `(ε/σ²)cosh(x/σ)` from `(log g₀)''`, preserving strong concavity. Its double-exponential tails make all source derivatives decay faster than exponentials; maximizing `s y-(ε/4)e^y` bounds `log max_|z|≤R |F(z)|` by `O(R log(2+R))`, proving entire order at most one.

## Conjecture loop and survivor

- **Conjecture:** the theta source's two exact critical scalar charges, ordinary mass, global Riccati law and order-one Fourier growth jointly exclude off-line zeros. **False:** the theorem supplies all those properties and an off-line zero arbitrarily near the critical line.
- **Attempt:** rescale the previous Gaussian family to fit the charges. **Fails:** amplitude fixes only one scalar budget. Tuning `σ` fixes the half-charge/mass ratio; retuning after damping preserves both the ratio and a simple spectral zero.
- **Positive survivor:** the exact charge-fitting map is compatible with strict global Riccati positivity and a nonreal Fourier divisor. A source-side RH proof must use an additional non-scalar arithmetic constraint: exact Euler coefficients, an equivalent all-prime phase law, or the full reflected complex boundary response. This construction does not rule out such a constraint.
