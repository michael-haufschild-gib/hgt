# Mass-Bessel cofinal radiation divergence

**Stage:** 3 — formalized in Lean 4  
**Date frozen:** 2026-08-04  
**Label:** `[LOCAL-RESEARCH] [PAPER-PROVED] [LEAN-CERTIFIED] [UNCONDITIONAL]`  
**Origin:** positive survivor of the uniform finite-aperture completion conjecture

## 1. Exact theorem

Fix `a>0` and `\sigma>0`.  For `X\ge2`, let

\[
 D_X(u)=
 \sum_{X<n\le2X}\frac{\Lambda(n)}{\sqrt n}
 \frac{2a(\sigma+iu)
 K_1\!\left(a\sqrt{(\sigma+iu)^2+(\log n)^2}\right)}
 {\sqrt{(\sigma+iu)^2+(\log n)^2}}.
\]

Put `u_X=(\log X)^4`.  Then

\[
 D_X(u_X)=
 \sqrt{2\pi a}\,(\sigma+iu_X)^{-1/2}e^{-a(\sigma+iu_X)}
 \left(2(\sqrt2-1)\sqrt X+o(\sqrt X)\right).
\]

In particular, there are `c_{a,\sigma}>0` and `X_0` such that

\[
 |D_X(u_X)|\ge
 c_{a,\sigma}\frac{\sqrt X}{(\log X)^2}
 \qquad(X\ge X_0).
\]

Consequently

\[
 \limsup_{X\to\infty}\|D_X\|_{L^\infty(\mathbb R_u)}=+\infty,
\]

and the finite mass-Bessel prime apertures are not Cauchy in vertical sup norm.

## 2. Proof

Set `L=\log X`, `t=\sigma+iL^4`, and `x=\log n`.  On `X<n\le2X`,
`x=L+O(1)`, hence `x^2/t^2=O(L^{-6})`.  The principal square root is analytic
in a fixed neighborhood of `1`, so uniformly on the shell

\[
 z:=\sqrt{t^2+x^2}
 =t\sqrt{1+x^2/t^2}
 =t+\frac{x^2}{2t}+O(x^4/|t|^3)
 =t+O(L^{-2}).
\]

The points `az` stay in a closed subsector of `|\arg z|<3\pi/2`.  Uniform
large-argument asymptotics give

\[
 K_1(az)=\sqrt{\frac{\pi}{2az}}e^{-az}(1+O(|z|^{-1})).
\]

Using `z/t=1+O(L^{-6})` and `e^{-a(z-t)}=1+O(L^{-2})`, we obtain

\[
 \frac{2atK_1(az)}z
 =\sqrt{2\pi a}\,t^{-1/2}e^{-at}(1+O(L^{-2}))
\]

uniformly for the entire dyadic shell.  Because all coefficients
`\Lambda(n)/\sqrt n` are nonnegative, the relative error remains `O(L^{-2})`
after summation.

Partial summation from `\psi(x)=x+o(x)` gives

\[
 \sum_{X<n\le2X}\Lambda(n)n^{-1/2}
 =2(\sqrt2-1)\sqrt X+o(\sqrt X).
\]

Substitution proves the asymptotic.  Finally

\[
 |t|^{-1/2}=L^{-2}(1+o(1)),
 \qquad |e^{-at}|=e^{-a\sigma},
\]

which proves the lower bound and divergence.

## 3. Dependency ledger

- analytic expansion of the principal square root near `1`;
- uniform sectorial large-argument asymptotic for `K_1`;
- prime number theorem and partial summation;
- positivity of `\Lambda`.

No RH-equivalent estimate enters.

## 4. Scientific content

The divergence comes from the opposite regime to the light-cone saddle studied
previously.  At `u\gg(\log X)^2`, every prime in a fixed logarithmic aperture
has the same leading massive radiation phase.  Finite-source positivity then
amplifies rather than cancels.

Therefore the desired bounded full trace cannot be assembled uniformly from
bounded finite traces.  It requires cancellation with primes whose aperture
grows with observation time.  This makes the open core intrinsically cofinal.

## 5. Novelty audit

Parent ingredients are classical.  The exact dyadic cofinal divergence and its
interpretation as failure of regular source completion were not found in the
route corpus or exact-collision search.  Label remains `[LOCAL-RESEARCH]` until
a wider literature audit establishes priority.

## 6. Lean target

Required formal stack:

1. define the mass carrier by its Fourier integral, avoiding an unformalized
   `K_1` constant;
2. prove uniform deep-time stationary phase for `x` in a dyadic logarithmic
   shell;
3. import/formalize the needed PNT partial-summation consequence;
4. derive the explicit dyadic lower bound.

Status: `[PAPER-PROVED]`; no unconditional Lean theorem yet.

## 7. Lean certificate

Every statement of section 1 is proved unconditionally in Lean 4.  All modules are wired into
their theorem-area umbrella and all declarations audit to
`[propext, Classical.choice, Quot.sound]`.

| Card statement | Declaration |
|---|---|
| `D_X(u)` for the dyadic block | `RHTower.massBesselDyadicAperture` |
| **the displayed asymptotic** `D_X(u_X) = √(2πa)(σ+iu_X)^{-1/2}e^{-a(σ+iu_X)}(2(√2−1)√X + o(√X))` | `RHTower.tendsto_massBesselDyadicAperture_asymptotic` |
| **the lower bound** `\|D_X(u_X)\| ≥ c√X/(log X)²` | `RHTower.exists_massBesselDyadicAperture_lower` |
| **`limsup_X ‖D_X‖_{L^∞(ℝ_u)} = +∞`** | `RHTower.tendsto_norm_massBesselDyadicAperture_atTop` |

The last is the card's boxed consequence in the strongest available form: along the deep-time ray
`u_X = (log X)^4` the aperture modulus tends to infinity, so the finite mass-Bessel prime apertures
are not Cauchy in vertical sup norm.

The four modules below carry the four items of the card's own dependency ledger.

### `BesselOrderAbsoluteAsymptotic` — the sectorial `K₁` asymptotic

The corpus already owned the Laplace form of the order-one Schläfli integral
(`besselK1C_sub_leading`) with the remainder bounded by `(Re w)^{-3/2}`.  That bound is useless on a
ray approaching the imaginary axis, which is exactly the regime `t = σ + i(log X)^4` of this card.
Integrating by parts once converts the remainder's power of `v` into a power of `w`:

| Card item | Declaration |
|---|---|
| the profile defect `P(v) − 1/√2` and its difference quotient `(P(v)−1/√2)/v` | `besselLaplaceDefect`, `besselLaplaceRatio` |
| `P'(v) = v(3+v²)/(2+v²)^{3/2}` | `besselLaplaceProfileDeriv`, `hasDerivAt_besselLaplaceProfile` |
| the difference quotient is differentiable off the origin | `besselLaplaceRatioDeriv`, `hasDerivAt_besselLaplaceRatio` |
| **the difference quotient and its derivative are bounded by two** | `abs_besselLaplaceRatio_le`, `abs_besselLaplaceRatioDeriv_le` |
| near the origin the difference quotient is linear | `abs_besselLaplaceRatio_le_linear` |
| the antiderivative of `v e^{-wv²}` | `besselGaussAnti`, `hasDerivAt_besselGaussAnti` |
| integration by parts on a compact subinterval of the half line | `integral_defect_gauss_interval` |
| the exhaustion `⋃ₙ (1/(n+1), n+1] = (0,∞)` and its integral limit | `iUnion_Ioc_eq_Ioi`, `tendsto_setIntegral_Ioc_atTop` |
| **the integration-by-parts identity on the half line** | `integral_defect_gauss_eq` |
| **`‖K₁(w) − e^{-w}√(π/(2w))‖ ≤ e^{-Re w}√(π/Re w)/\|w\|`** | `norm_besselK1C_sub_leading_le_norm` |

The relative error against the leading term is `O((Re w · \|w\|)^{-1/2})`, so on the card's ray
`w = a√(t²+x²)` with `Re w ≍ aσ` and `\|w\| ≍ a(log X)^4` it is `O((log X)^{-2})` — exactly the
uniform relative error the card's proof needs.  This is the card's dependency-ledger item
"uniform sectorial large-argument asymptotic for `K₁`", proved unconditionally.

### `MassBesselDeepTimeCarrier` — the carrier and its deep-time profile

| Card item | Declaration |
|---|---|
| a square root with positive real part off the negative axis | `norm_add_re_pos_of_im_ne_zero`, `csqrtRe_pos_of_im_ne_zero`, `csqrt_sq_of_im_ne_zero` |
| `√(t²+x²)`, `B_a(t,x) = 2atK₁(a√(t²+x²))/√(t²+x²)`, and the profile `√(2πa)e^{-at}/√t` | `massBesselRoot`, `massBesselCarrier`, `massBesselLeading` |
| `(π/(az))^{1/2} = √π/(√a √z)` | `cpow_half_pi_div_eq` |
| **`2a·(leading Schläfli term at z) = √(2πa)e^{-az}/√z`** | `two_mul_besselLeading_eq` |
| **the carrier is the profile times an explicit distortion, plus the Schläfli remainder** | `massBesselCarrier_eq` |
| the shell is off the branch cut: `Im(t²+x²) = 2·Re t·Im t` | `massShell_im`, `massShell_im_ne_zero` |
| the root has positive real and imaginary parts and squares back | `massBesselRoot_sq`, `massBesselRoot_re_pos`, `massBesselRoot_im_pos` |
| **`\|√(t²+x²) − t\| ≤ x²/Im t`**, and the resulting real-part floor | `norm_massBesselRoot_sub_le`, `massBesselRoot_re_ge` |
| `‖√(2πa)e^{-at}/√t‖ = √(2πa)e^{-a Re t}/√\|t\|` | `norm_massBesselLeading` |
| the Schläfli remainder at the shell argument | `norm_massBesselRemainder_le` |
| the principal square root is Lipschitz with constant `1/Re √t` | `norm_csqrt_sub_le` |
| **`‖B_a(t,x) − √(2πa)e^{-at}/√t‖ ≤ ‖profile‖(4α+2β+γ) + remainder`** | `norm_massBesselCarrier_sub_leading_le` |

Here `α` bounds `\|z−t\|/\|z\|`, `β` bounds `\|√t−√z\|/\|√z\|` and `γ` bounds `2a\|z−t\|`; the three
are combined by the corpus's near-unit product law `norm_mul3_sub_one_le`.  The card's displayed
uniform shell estimate

`2atK₁(az)/z = √(2πa) t^{-1/2} e^{-at}(1 + O(L^{-2}))`

is this inequality with `\|z−t\| ≤ x²/L⁴ = O(L^{-2})`, `\|z\| ≍ L⁴` and `Re √t ≍ L²`.

### `RHTower/DyadicVonMangoldtSqrtMass` — the prime input

| Card item | Declaration |
|---|---|
| the weighted dyadic mass `∑_{X<n≤2X} Λ(n)n^{-1/2}` | `dyadicSqrtVonMangoldtMass` |
| `ψ(2X) − ψ(X) = ∑_{X<n≤2X} Λ(n)` | `sum_range_succ_sub`, `chebyshevPsiReal_dyadic_sub` |
| weighting costs at most the endpoint weight `(2X)^{-1/2}` | `dyadicSqrtVonMangoldtMass_ge` |
| **`(ψ(2X) − ψ(X))/X → 1`** | `tendsto_chebyshevPsiReal_dyadic_sub` |
| **the weighted dyadic mass is eventually at least `√X/3`** | `eventually_dyadicSqrtVonMangoldtMass_ge` |

This is the card's dependency-ledger item "prime number theorem and partial summation", in the
two-sided form the divergence corollary needs.  The prime input is the corpus's own
`RHTower.Sieve.tendsto_sum_vonMangoldt_div`, so this module lives in `RHTower/`.

### `HTGeometry/MassBesselShellEstimate` — the uniform shell estimate

| Card item | Declaration |
|---|---|
| the spectral point `σ + iu` and its modulus | `apertureSpectralPoint`, `norm_spectralPoint_sq`, `le_norm_spectralPoint`, `norm_spectralPoint_le` |
| `‖√(t²+x²)‖² ≥ ‖t‖² − x²` | `norm_add_ge_sub`, `norm_massBesselRoot_sq_ge` |
| **the card's displayed uniform shell estimate** | `norm_massBesselCarrier_sub_leading_le_shell` |

The last reads: for `0 < a`, `0 < σ ≤ u`, `1 ≤ u`, `2x² ≤ u`, `4x² ≤ σu`, `2ax² ≤ u`,

```text
‖B_a(σ+iu, x) − √(2πa)e^{-a(σ+iu)}/√(σ+iu)‖
  ≤ (12+2a)·(x²/u)·‖√(2πa)e^{-a(σ+iu)}/√(σ+iu)‖
    + 8·e^{-aσ/2}·√(2π/(aσ))/u.
```

At `u = (log X)^4` and `x ≤ 2 log X` both error terms are `O((log X)^{-2})`, which is the card's
`(1 + O(L^{-2}))`.

### `RHTower/MassBesselDyadicAperture` — the aperture and its divergence

| Card item | Declaration |
|---|---|
| `D_X(u) = ∑_{X<n≤2X} (Λ(n)/√n)·B_a(σ+iu, log n)` | `massBesselDyadicAperture` |
| the aperture centred at the common profile | `massBesselDyadicAperture_sub` |
| **the aperture cannot cancel: `‖D_X‖ ≥ ‖profile‖·(prime mass)/4`** | `norm_massBesselDyadicAperture_ge` |
| the profile floor `√(2πa)e^{-aσ}/(√2 (log X)²)` | `apertureProfileConst`, `apertureProfileConst_div_le` |
| `√X/(log X)² → ∞` | `tendsto_sqrt_div_log_sq_atTop` |
| **`‖D_X(u_X)‖ ≥ c√X/(log X)²` for large `X`, with `c = √(2πa)e^{-aσ}/(12√2)`** | `exists_massBesselDyadicAperture_lower` |
| **the card's `limsup_X ‖D_X‖_{L^∞} = +∞`** | `tendsto_norm_massBesselDyadicAperture_atTop` |

`tendsto_norm_massBesselDyadicAperture_atTop` is the card's boxed consequence, proved
unconditionally: along the deep-time ray `u_X = (log X)^4` the aperture modulus tends to infinity,
so the finite mass-Bessel prime apertures are not Cauchy in vertical sup norm.

### `RHTower/DyadicVonMangoldtSqrtAsymptotic` — the exact prime constant

| Card item | Declaration |
|---|---|
| `t ↦ t^{-1/2}` and its derivative | `invSqrt`, `hasDerivAt_invSqrt`, `deriv_invSqrt` |
| **Abel summation:** `∑_{X<n≤2X}Λ(n)n^{-1/2} = ψ(2X)/√(2X) − ψ(X)/√X + (1/2)∫_X^{2X}ψ(t)t^{-3/2}dt` | `dyadicSqrtVonMangoldtMass_abel` |
| `∫_X^{2X} t^{-1/2}/2 dt = √(2X) − √X = (√2−1)√X` | `integral_sqrtWeight`, `sqrt_two_mul_sub` |
| `ψ` is a bounded measurable step function, so the weighted integrand is integrable | `integrableOn_psiWeight` |
| the prime-number-theorem error in the integral | `abs_integral_psiWeight_sub_le` |
| **`∑_{X<n≤2X} Λ(n)n^{-1/2} / √X → 2(√2−1)`** | `tendsto_dyadicSqrtVonMangoldtMass_div_sqrt` |

Abel summation is mathlib's `sum_mul_eq_sub_sub_integral_mul`; the prime input is the corpus's own
`RHTower.Sieve.tendsto_sum_vonMangoldt_div` (`ψ(x)/x → 1`) in the scaled form
`tendsto_chebyshevPsiReal_scaled`.

### What the formal proof does differently

**No Bessel constant is assumed.**  The card's dependency ledger lists a *uniform sectorial*
large-argument asymptotic for `K₁`.  The corpus's existing bound has error `(Re w)^{-3/2}`, which
is worthless on a ray approaching the imaginary axis — exactly this card's regime.  One integration
by parts against the difference quotient of the Schläfli profile defect converts a power of the
integration variable into a power of `w`, giving an error in `|w|` and hence a relative error
`O((Re w · |w|)^{-1/2})` valid along every ray.

**The relative error is tracked, not the absolute one.**  The carrier is written as the profile
times an explicit distortion — a ratio of shell root to spectral point, a ratio of their principal
square roots, and an exponential of the root defect — plus the Schläfli remainder.  Each factor is
handled by the corpus's near-unit product law, so the shell estimate is an inequality with named
constants rather than an asymptotic with hidden ones.

**The aperture bound is a non-cancellation statement.**  Because the coefficients `Λ(n)/√n` are
non-negative and every carrier is within a quarter of the common profile, the reverse triangle
inequality gives a *lower* bound on the aperture directly, with no oscillation argument.
