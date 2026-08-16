# Mass-Bessel cofinal radiation divergence

**Stage:** 2 — fully proven on paper  
**Date frozen:** 2026-08-04  
**Label:** `[LOCAL-RESEARCH] [PAPER-PROVED]`  
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

## 7. Lean progress

Two new modules under `formal/GaloisForLFunctions/HTGeometry/`, both wired into the
`GaloisForLFunctions.HTGeometry` umbrella and both axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

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

### What remains

- the exact constant `2(√2−1)` of the asymptotic, which needs the Riemann-sum refinement of the
  dyadic block (subdivide `(X,2X]` into `K` geometric pieces and let `K → ∞`); the divergence
  corollary needs only the crude lower bound above, which is proved;
- the dyadic assembly of the shell estimate against that mass at `u_X = (log X)^4`: feeding
  `‖√(t²+x²) − t‖ ≤ x²/(log X)^4 = O((log X)^{-2})`, `‖√(t²+x²)‖ ≍ (log X)^4` and
  `Re √t ≍ (log X)^2` into `norm_massBesselCarrier_sub_leading_le` gives a uniform *relative*
  deviation `O((log X)^{-2})` over the shell, whence
  `\|D_X(u_X)\| ≥ (1/2)·√(2πa)e^{-aσ}·(√X/3)/(log X)^2`.

No further analytic input is needed: both remaining items are inequality bookkeeping on top of the
three modules above.
