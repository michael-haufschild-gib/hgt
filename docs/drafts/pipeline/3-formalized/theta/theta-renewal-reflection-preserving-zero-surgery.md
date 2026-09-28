# Off-axis zero surgery inside the exact positive renewal reflection class

- **ID:** `theta-renewal-reflection-preserving-zero-surgery`
- **Stage:** 3-formalized (paper proof formalized unconditionally in Lean; see `theta-renewal-reflection-preserving-zero-surgery-formalized.md`)
- **Type:** source-class countermodel and exact mass-preserving interpolation theorem
- **Routes:** STC, CSB, U; theta one-port interface
- **Status:** [PROVED HERE ON PAPER] [FORMALIZED IN LEAN] [NOT AN RH PROOF]
- **Dependencies:** [Literal renewal factorization](../../3-formalized/theta/theta-renewal-phase-cosh-factorization.md), [all-shift theta Fourier identity](../../../../../formal/GaloisForLFunctions/RHTower/HedenmalmThetaSourceSpectrumExact.lean), and [horizontal Xi decay](../../../../../formal/GaloisForLFunctions/RHTower/XiHorizontalStripDecay.lean).
- **Scope:** The construction changes the theta source. It neither gives an off-axis zero of literal Xi nor proves RH.

## Reinterpretation and theorem

The scalar renewal deformation in [critical seam coupling](../../3-formalized/theta/theta-renewal-seam-critical-coupling.md) misses smoothness at the modular seam. Indeed, with `D_r=c-rN` and `D=(λ-a)L`, its inverse one-sided Laplace source is

```text
P_r(t)=rP(t)+(1-r)c exp(at),              t≥0.
```

Although `P_r(0)=c`, its even extension has derivative jump `2ac(1-r)`. The corresponding spectral constant `2ac(1-r)` is the Fourier transform of a central Dirac atom. The physical `r=1` source is the unique smooth member of this scalar family. This observation leaves a sharper question: does **exact** smooth reflection, together with positive renewal and its mass, force critical-strip zero location? The answer is no.

Fix `a=1/4`, `c=Θ(1)` and the literal even real-analytic function `P(t)=exp(at) Θ(exp t)`. Put `ν=aP-P'` on `t≥0`, and let `q=c⁻¹∫₀∞exp(at)ν(t)dt<1/6`. For any integer `N≥0` and any `0<b<a`, there are arbitrarily large `T` and even real-analytic functions `P_T` on the entire real axis such that:

1. `P_T(0)=c`, and `P_T` has the same derivatives as `P` through order `2N+1` at zero. Moreover `P_T-P` and all its fixed-order derivatives converge to zero in every exponentially weighted uniform norm on the real axis.
2. `ν_T=aP_T-P_T'` is strictly positive on `t≥0`, and its weighted renewal mass is **exactly** `q`: `c⁻¹∫₀∞exp(at)ν_T(t)dt=q<1/6`. The positive logarithmic convolution kernel `Q_T=Σ_{m≥1}ν_T^{*m}/(mc^m)` is therefore defined and stable on `Re λ≥-a`.
3. The real-analytic continuation of `Q_T` obeys the **exact same** all-real reflection identity as the literal source:

```text
Q_T†(-t)+Q_T(t)=2 sinh(at)/t,             t>0.       (1)
```

4. The two-ended entire function defined from this source,

```text
D_T(λ)=c-∫₀∞exp(-λt)ν_T(t)dt,
X_T(z)=(a-iz)D_T(-iz)+(a+iz)D_T(iz),
```

has a zero at `T+ib`, strictly inside the natural strip `|Im z|<a`. The perturbation is nonzero, and reality/evenness give its reflected zero quartet.
5. In the ordinary full-source coordinate, the perturbed Fourier density remains strictly positive. More strongly, **every finite literal prime deletion** of that density is positive on the right ray, simultaneously for all finite prime sets.

Thus **even exact analytic seam reflection, exact renewal mass, positive increments, all finite-prime deletion inequalities and arbitrarily many exact seam jets do not select the critical line**. A producer must distinguish the literal square-lattice theta source from this entire class; the renewal reflection law alone does not do so.

## Paper proof

Choose the even, strictly positive away from zero, real-entire envelope

```text
ψ(t)=t^(2N+2) exp[-exp(2t)-exp(-2t)].
```

It and every derivative decay faster than `exp(-B|t|)` for every `B>0`. On the positive tail they decay faster than the literal first theta atom `exp((a+1)t-π exp t)`, which is a lower bound for `ν(t)` up to a positive constant. Define three even real-analytic directions

```text
g₀(t)=ψ(t),
g₁,T(t)=ψ(t) cos(Tt),
g₂,T(t)=t ψ(t) sin(Tt).                              (2)
```

All three vanish through order `2N+1` at the seam. The exact mass functional on a perturbation `g` is

```text
M(g)=∫₀∞ exp(at)[a g(t)-g'(t)]dt
    =2a∫₀∞ exp(at)g(t)dt,                            (3)
```

because `g(0)=0` and the distant boundary term vanishes. Hence `M(g₀)>0`, while `M(g₁,T),M(g₂,T)→0` by the Riemann--Lebesgue lemma.

At `z_T=T+ib`, write `E_T(g)=∫_ℝ exp(iz_Tt)g(t)dt`. Splitting the oscillatory factors into exponentials and applying the same lemma gives

```text
E_T(g₀)→0,
E_T(g₁,T)→(1/2)∫_ℝ ψ(t)exp(-bt)dt >0,
E_T(g₂,T)→-(1/2i)∫_ℝ tψ(t)exp(-bt)dt ∈ iℝ\{0}.  (4)
```

The last integral is strictly negative: after pairing `t` and `-t`, it equals `-2∫₀∞tψ(t)sinh(bt)dt`. Therefore the real `3×3` matrix whose rows are `Re E_T`, `Im E_T`, and `M`, and columns are the directions (2), converges to an invertible matrix (up to column order).

This yields a positive controllability theorem stronger than the one planted zero: for all sufficiently large `T`, the restriction

```text
E_T : ker(M) ∩ span_ℝ{g₀,g₁,T,g₂,T} → ℂ
```

is a real-linear isomorphism, and its inverse has a coefficient norm bounded independently of `T`. Thus **every** sufficiently small prescribed complex spectral value at `T+ib` can be reached by a mass-neutral analytic source perturbation; choosing the value that cancels literal Xi gives the zero below.

For any even perturbation `g` with `g(0)=0`, one-sided integration by parts gives `δD(λ)=(λ-a)∫₀∞exp(-λt)g(t)dt`. Substitution into the two-ended identity yields the exact variation

```text
X_(P+g)(z)-Xi(2z)=-(z²+a²) E_z(g).                (5)
```

The all-shift Fourier identity and its horizontal decay imply `Xi(2z_T)→0` exponentially as `T→∞`. Solve the invertible real system for coefficients `ε₀,T, ε₁,T, ε₂,T` satisfying

```text
M(Σ εⱼ,T gⱼ,T)=0,
E_T(Σ εⱼ,T gⱼ,T)=Xi(2z_T)/(z_T²+a²).            (6)
```

The inverse matrices stay bounded, so the three real coefficients tend to zero faster than every power of `T`. Put `P_T=P+Σ εⱼ,T gⱼ,T`. Equation (5) gives `X_T(z_T)=0`, and (3), (6) preserve `q` exactly. Avoid the discrete values of `T` where `Xi(2z_T)=0` to make the perturbation nonzero.

For each fixed derivative order and exponential weight, derivatives of the directions (2) grow by at most a polynomial in `T`, while their coefficients decay faster than every power; this proves the claimed convergence. The ratios of each direction and its first derivative to `ν` are bounded on `t≥0` by `O_N(1+T)` because the envelope dies faster than the first theta atom at infinity and `ν(0)=ac>0`. Hence `ν_T>0` for all sufficiently large `T`. The same argument preserves `P_T(t)>exp(at)` for `t≥0`, if that optional source-tail inequality is required.

For assertion 5, use the full-source convention `XiC(w)=∫_ℝ exp(-iwx)k(x)dx`. Since `Xi(2z)=XiC(2z)`, (5) and Fourier differentiation show that its perturbed density is exactly

```text
k_T(x)=k(x)+2[g_T''(2x)-a²g_T(2x)],
g_T=P_T-P.                                           (7)
```

This density is even and real. In the [compact source surgery card](../../3-formalized/theta/theta-compact-critical-strip-zero-engineering.md), the literal finite-prime deletion `D_S=∏_(p∈S)(1-p^(-1/2)T_(log p))` satisfies `D_S k(x)≥h(x)>0` for `x≥0`, where `h` is the first square-lattice atom. For any finite `S`, expansion over squarefree products and (7) give

```text
|D_S(k_T-k)(x)|
 ≤ ∑_(d≥1 squarefree) d^(-1/2)|k_T-k|(x+log d).      (8)
```

Each basis direction in (2), after two derivatives and the rescaling `t=2x`, is bounded by `C_N(1+T)²` times a polynomial in `x` and `exp(4x)`, multiplied by `exp[-exp(4x)]` on `x≥0`. In (8), the `d`-th term gains `exp[-d⁴ exp(4x)]`. The sum is therefore bounded by `C_N'(1+T)² max_j|εⱼ,T| B(x)`, with `B(x)/h(x)` bounded on `[0,∞)` and tending to zero at infinity: `B` decays like `exp[-c exp(4x)]`, whereas `h` has first-atom scale `exp[-π exp(2x)]` times a positive elementary factor. Since `(1+T)² max|εⱼ,T|→0`, (8) is strictly smaller than `h(x)` for every `x≥0`, **uniformly in the finite set `S`**. Thus `D_Sk_T(x)>0`; the empty set gives `k_T(x)>0` on the right, and evenness gives global positivity.

Finally, the proof of (1) in the literal renewal card uses only: even real analyticity of `P`, its seam value `c`, rapid decay of `P-exp(at)` on the positive tail, and the convergent logarithmic renewal series. All these properties hold for `P_T`. More explicitly, the large-positive-`λ` expansion of `λ L_T(λ)/c` has only even inverse powers because the odd seam derivatives vanish. Consequently the odd inverse-power coefficients of `-log(D_T(λ)/c)` come solely from `-log(1-a/λ)`, giving `Q_T^(2j)(0)=a^(2j+1)/(2j+1)` for all `j`. Analytic continuation of this even germ yields (1) for every real `t`.

## What survives and what remains open

The strongest positive survivor is the uniform high-frequency controllability isomorphism above, inside the exact mass-neutral analytic reflection class. It shows precisely how two complex spectral degrees of freedom remain after the renewal scalar charge has been fixed. The full renewal reflection identity, its mass, and the entire family of finite-prime deletion positivity inequalities are **not** the arithmetic rigidity needed for RH. The literal square-lattice atom law, or a global identity that detects it and is violated by (2), remains a possible discriminator. This combines constraints previously separated between [compact theta zero surgery](../../3-formalized/theta/theta-compact-critical-strip-zero-engineering.md) and the positive renewal construction.

The construction does not preserve the literal integer-square theta expansion or Euler coefficients. No source-derived zero-exclusion law for those exact data is established here. The theorem is dependency-closed on paper and formalized unconditionally in Lean, including the controllability isomorphism, the interpolation and the positivity of every finite prime deletion; the external novelty audit remains open. No route is retired.

## Log

- 2026-09-28: every claim formalized unconditionally in Lean (modules `ThetaReflectionPreservingZeroSurgery`, `ThetaSurgeryControllability`, `ThetaProfileSurgeryVariation`, `ThetaSurgeryEnvelope`, `ProfileRenewalLogKernel`, `ProfileRenewalAnalyticContinuation`); moved to stage 3.
