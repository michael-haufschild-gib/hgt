# CLG/TTF complete two-atom error through derivative twelve

- **Stage:** 3-formalized
- **Closed result:** Every derivative and reflected entry needed by the corrected even four-by-four source has a complete omitted-source bound on `q≥37/10`. The correction itself has a complete error bound. An explicit finite two-atom quadratic form, using rational coefficient endpoints, minus this error bounds the actual canonical quadratic form from below.
- **Open:** A positive interior comparison below `x=6/5`, quantitative small-center control, the actual mixed rank-seven sign and all-order positivity. The [complete corrected source is strict on the explicit outer ray `x≥6/5`](clg-ttf-even-four-explicit-tail.md). RH remains unproved.
- **Full chain:** Literal theta source → every signed center-mixed Hankel section nonnegative → global Fourier-current sign → Xi Bezoutian orientation → RH.

## The source and its fixed tail calibration

Write `q=π exp(2x)`, `φ=thetaCuspSourceTerm x 1`, `T=thetaCuspSourceTerm x 1+thetaCuspSourceTerm x 2`, and `ℓ=T/φ`. The existing exact source identity is

`Φ−T=φ ε`,

where `ε` is the complete likelihood tail of atoms `n≥3`. Its fixed positive spectral measure `ν` is supported on `t≥8`. At tilt `B₀=19/20`, the proved whole-tail calibration is

`∫ exp(−B₀t)dν(t)≤10^−6`.

Set `B=q−3/2` and `d=B−B₀=q−49/20`. The error scale is `δ=10^−6 exp(−8d)`. Throughout `q≥37/10`, one has `d≥5/4` and `x>0`. Every polynomial moment of the tilted complete measure is integrable.

## Extending support transport past order ten

The sharp support-edge estimate `M_n(B)≤8^nδ` requires `n/8≤d`. That covers orders through ten at the left endpoint, but not orders eleven and twelve.

First, the movable-radius inequality proves, for `0<b≤a`, `t≥b`, and `n/a≤d`,

`t^n exp(−dt)≤a^n exp(−db)`.

Apply the existing monotonicity estimate at `t+a−b≥a`, multiply by `exp(d(a−b))`, and use `t^n≤(t+a−b)^n`. This retains the physical support edge in the exponential while allowing a larger polynomial radius. Integration gives `M_n(B)≤a^nδ` for every `a≥8` with `n/a≤d`; in particular `a=48/5` covers all orders through twelve on the original middle ray.

A sharper bound for the two new orders uses the exact stationary radius. The elementary inequality `u≤exp(u−1)` gives

`t^n exp(−nt/a)≤a^n exp(−n)` for `a>0`, `t≥0`.

At reference decay `5/4`, take `a=44/5` for order eleven and `a=48/5` for order twelve. The already proved rational exponential bound `exp(−1)≤10/27` and exact rational inequalities

`(44/5)^11(10/27)≤(5/4)8^11`,

`(48/5)^12(10/27)^2≤(5/4)8^12`

give `t^n exp(−5t/4)≤(5/4)8^n exp(−10)` at both new orders. For `d≥5/4`, the remaining factor satisfies `exp(−(d−5/4)t)≤exp(−8(d−5/4))` on the actual support. The exponents combine to `exp(−8d)`. Thus

`M_n(B)≤(5/4)8^nδ` for `n=11,12`.

This is an estimate for the complete infinite tail. No numerical maximizer, quadrature, sampled sign or computed certificate is used in its proof.

## Actual logarithmic derivatives through twelve

The existing exact differentiation recurrence is

`L_(0,m)(z)=z^m`,

`L_(n+1,m)(z)=2m L_(n,m)(z)−2 L_(n,m+1)(z)`.

The actual derivative `ε^(n)(x)` is the integral of `L_(n,0)(qt) exp(−Bt)` against the complete measure. The new scalar polynomial identities at orders eleven and twelve prove

`0≤(−1)^n L_(n,0)(z)≤(2z)^n` for `z≥24`.

Both inequalities have exact nonnegative-coefficient expansions after translation by twenty-four. Together with the previously proved orders through ten, they apply on the whole deep support, since `qt≥8·37/10>24`. Integrating the signed inequalities and applying the moment bounds gives

`|ε^(n)(x)|≤D_n(x)`, for `0≤n≤12`,

where `D_n=c_n(16q)^nδ`, `c_n=1` for `n≤10`, and `c_n=5/4` for `n=11,12`. Every existing lower-order constant is preserved.

## Complete source, reflected and correction errors

Define the finite source error

`A_n=Σ_(i=0)^n binom(n,i)|φ^(i)|D_(n−i)`.

The exact derivative identity for `Φ−T=φε` proves `|Φ^(n)−T^(n)|≤A_n` through order twelve.

For the reflected product, factor out the exact first-atom reflection before taking absolute values. Put

`R_n=Σ_(i=0)^n binom(n,i)(|ℓ^(i)|D_(n−i)+D_i|ℓ^(n−i)|+D_iD_(n−i))`,

`E_n=Σ_(i=0)^n binom(n,i)|j_i[φ]|R_(n−i)`.

Here `j_n[F]=D_t^n[F(x+t)F(x−t)]|_(t=0)`. The exact product decomposition retains the two linear cross terms and the quadratic tail term. It proves

`|j_n[Φ]−j_n[T]|≤E_n` for `n≤12`.

Division by the positive `φ²q^k` also gives complete error bars for all seven signed normalized even entries, `0≤k≤6`.

The correction is `G[F]=3F²+2xFF′`. Define

`J=3(2|T|A₀+A₀²)+2|x|(|T|A₁+|T′|A₀+A₀A₁)`.

The exact product expansion `fg−FG=F(g−G)+G(f−F)+(f−F)(g−G)` proves `|G[Φ]−G[T]|≤J`. Therefore every `10^12≤C≤3·10^12` satisfies

`|C G[Φ]−C G[T]|≤3·10^12 J`.

All retained quantities are finite-source expressions. The corpus's exact scale-polynomial identities express every derivative of each retained atom using `P₀(q)=4q²−6q` and `P_(n+1)=(1/2−2q)P_n+2qP_n′`, evaluated at `q` and `4q`. Thus no unknown infinite-source derivative remains on the error side.

## A finite lower comparison for the actual matrix

Let `N_C=[(−1)^(i+j)j_(2(i+j))[Φ]]_(i,j<4)+C G[Φ]e₃e₃ᵀ`. Let `T_C` denote the same matrix built from the retained source. Define the nonnegative error matrix

`H_ij=E_(2(i+j))+1_(i=j=3)·3·10^12 J`.

The new complete-source theorem proves `|(N_C−T_C)_ij|≤H_ij` at every entry, uniformly throughout the rational coefficient band. Summing after multiplying by the vector coordinates gives

`|vᵀ(N_C−T_C)v|≤Σ_(i,j)|v_i|H_ij|v_j|`.

Replace the last diagonal correction of the retained matrix by

`min(10^12 G[T],3·10^12 G[T])`

to define the fixed rational lower model `T_lower`. Its quadratic form is below that of every `T_C` in the coefficient band: the appropriate endpoint is selected by the sign of `G[T]`, and only the last diagonal changes. The canonical coefficient has its band proved from the literal modular source. Consequently, for every `x≥8/95` and every `v∈ℝ⁴`,

`vᵀN_(C_*)v ≥ vᵀT_lower v − Σ_(i,j)|v_i|H_ij|v_j|`.

This is the actual canonical quadratic form, bounded by a finite retained expression and the complete omitted-source error. Positivity of the right-hand side remains unproved. The small-center interval also still needs a quantitative four-dimensional comparison; existing endpoint positivity does not supply it. No rank-seven or all-order sign follows from the error theorem alone.

## Lean verification

Eight new modules: `HTGeometry/LogarithmicLaplaceScoreTwelve`; `RHTower/ThetaCusp/ThetaCuspDeepTailExtendedSupport`, `ThetaCuspDeepTailPeakTwelve`, `ThetaCuspDeepTailCoolingTwelve`, `ThetaCuspTwoAtomSourceTwelve`, `ThetaCuspTwoAtomReflectedTwelve`, `ThetaCuspTwoAtomCompensationError`, `ThetaCuspEvenFourTwoAtomError`.

Each was checked in scratch with one foreground `lake env lean` process at a time. Only needed oleans were emitted. The sharper peak bound was propagated through the four affected new error modules and checked. Imports are wired into the umbrellas without umbrella or full builds. Six new capstones were audited once; their only axioms are `propext`, `Classical.choice` and `Quot.sound`. The formal lint gate passed.
