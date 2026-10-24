# Literal critical source on the compact L² energy domain

- **ID:** sz-critical-source-extended-energy-domain-2026-10-24
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `sz-critical-source-first-variation-2026-10-18`; corpus Krein increments and critical Beta kernel.
- **Statement:** Every real compactly supported L² source has an extended-real critical first variation of the literal Suzuki arithmetic source, equal to its complete Weil energy, including value `+infinity` when its Lévy energy is infinite.

## Route and significance

WL still requires an arithmetic one-sided critical bound at every positive exponential slack.
This theorem concerns the analytic source domain, not that missing sign. It makes the
literal critical source available on the closed energy domain without a smoothness premise,
and identifies the positive critical divergence of sources with infinite energy.
The compact C² parent theorem is now certified, including its literal arithmetic terms:
`../3-formalized/sz-critical-source-first-variation-2026-10-18.md`.

## Exact statement

Let `f : R -> R` belong to L² and have compact support. Put
`C(t)=integral f(u)f(u+t)`, `R=C(0)`, and
`J=integral_0^infinity (R-C(t))*2exp(-t/2)/(1-exp(-2t))`, interpreted in `[0,infinity]`.
Choose `A>0` with `C(t)=0` for `|t|>=A`, and put `N=floor(exp A)`.
For the literal source, set
`Q_w=integral_0^infinity C(t)*exp(t/2)*Re(suzukiSourceHFinite w (exp t))`.
The limit as `w -> 0+` is

`(R-Q_w)/w -> (Re psi(1/4)-log pi)*R + J`
`               + 4 integral_0^infinity cosh(t/2)*C(t)`
`               - 2 sum_(2<=n<=N) Lambda(n)*C(log n)/sqrt(n)`.

Only `J` may be infinite. All other terms are finite; no subtraction of infinities occurs.
This is not an assertion that the finite limit is nonnegative.
The extended complete Weil energy here means this physical prime–Gamma–polar
expression. At infinite energy it is not a totalized real or complex Bochner integral.

## Attack and proof — [PROVED HERE]

Verdict: **BRIDGE**. The parent proof's smoothness use supplies finite Lévy energy and continuity
of correlation. L² translation continuity already supplies the latter. The mathematical
content to establish is the literal-source limit on this larger domain, not a new positivity
criterion. No external novelty claim is made.

1. The corpus's `AutocorrelationKrein.integrable_mul_shift` and `increment_sq_le` apply to
   every real L² source. Cauchy–Schwarz gives `|C(t)|<=R`. Strong translation continuity is
   supplied by `SobolevShear.continuous_physicalTranslation`, whose velocity space is real
   L². Equivalently its proof applies `Continuous.compMeasurePreservingLp` to the maps
   `u -> u+t`. Pair this continuous orbit with `f` by the continuous Hilbert inner product:
   `C(t)=<f,translate_t f>` is continuous. If the support of `f` is contained in `[-B,B]`,
   then `f(u)f(u+t)=0` whenever `|t|>2B`; therefore `C` has compact support. This also follows
   from `ArchimedeanExactForm.hasCompactSupport_autocorr`, which requires no smoothness.
   Thus `C` is uniformly continuous on the whole real line.
2. The positive primary density `B_w` has mass `M_w -> 1`. For every `delta>0`, its mass on
   `[delta,infinity)` is at most `w*a_w*integral_delta^infinity w_arch`, which tends to zero.
   Indeed `w_arch(t)<=2exp(-t/2)/(1-exp(-2delta))` there, so the last integral is at most
   `4exp(-delta/2)/(1-exp(-2delta))`, finite for every `delta>0`.
   Split `integral B_w(t)*(C(u+t)-C(u))` at `delta`. Uniform continuity bounds the small part
   uniformly in `u`; `2R` bounds the tail. Thus all primary cusps converge uniformly without
   assuming finite `J`.
3. Compact-test L¹ convolution gives the full pole pairing as
   `integral_0^A exp((1/2-w)s)*primaryCusp_w(u+s) ds` for `u>=0`. The uniform primary limit
   and the compact exponential bound give its limit, including the growing pole.
4. Write `Delta=R-C>=0` and `K=2exp(-5t/2)/(1-exp(-2t))`. The exact identity is
   `(R-primaryCusp_w(0))/w=((1-M_w)/w)*R+integral Delta*B_w/w`.
   If `J<infinity`, the existing domination `B_w/w<=a_w*w_arch` gives dominated convergence.
   If `J=infinity`, the identity `w_arch-K=2exp(-t/2)` and `0<=Delta<=2R` imply
   `integral Delta*K=infinity`. For any positive sequence `w_j -> 0`, Fatou gives
   `infinity=integral Delta*K<=liminf_j integral Delta*B_(w_j)/w_j`.
   If the positive-shift limit were not `+infinity`, some real `M` would admit arbitrarily
   small positive `w` with that integral at most `M`. Choose such `w_j<1/(j+1)`; the preceding
   inequality contradicts the bound `M`. Thus the full positive-shift limit is `+infinity`.
   Every integral before passage to the limit is finite, since `Delta<=2R` and `B_w` is
   integrable. No rate or monotonicity in `w` is used.
5. Every pole contribution and every non-unit arithmetic cusp has a finite limit. To verify
   the fixed-cutoff source identity on this domain, for `t<=A` use
   `suzukiSourceHFinite_eq_fixedSum` with `N=floor(exp A)`; for `t>A` use `C(t)=0`.
   The source vanishes at nonpositive logarithmic arguments. Translation by `log n` gives
   `Q_w=sum_(1<=n<=N) c_w(n)*exp(-log(n)/2)*sourceCusp_w(log n)`.
   The translated integrals are absolutely convergent: the primary term is bounded by
   `M_w R`, and the pole by `M_w R A exp(A/2)`. Thus finite-sum integration and translation
   are legitimate for this L² source's continuous compact correlation.
   At `n=1` the coefficient is identically one. At every `n>=2`, the exact Euler coefficient
   has `c_0(n)=0`, `c'_0(n)=2Lambda(n)` (`hasDerivAt_suzukiShiftedCoefficient`). Step 2 and
   the pole factor `2w` give `sourceCusp_w(log n)->C(log n)`. There are finitely many terms,
   so their divided differences tend to `2Lambda(n)*C(log n)/sqrt(n)`. Neither the pole
   nor arithmetic terms can cancel an infinite positive compensated limit.
6. The Gamma recurrence and `w_arch-K=2exp(-t/2)` give the displayed normalization.

## Positive bounded profiles: first exact Lean target

For every bounded measurable `D : R -> [0,infinity)`, with no finite-energy premise,

`integral_0^infinity^+ D(t)*B_w(t)/w -> integral_0^infinity^+ D(t)*K(t)`

in `[0,infinity]`. If the right side is infinite, Fatou gives the limit. If it is finite,
boundedness of `D` makes `integral D(t)*2exp(-t/2)` finite. Since
`w_arch=K+2exp(-t/2)`, the full Lévy majorant is integrable. The already proved real
compensated tangent then applies, and continuity of `ENNReal.ofReal` gives the asserted
extended integral limit. For each positive small shift, boundedness also gives absolute
integrability against `B_w/w`. Thus this statement retains the ordinary real integrals
where they exist and never interprets a divergent limiting energy as zero.

This strengthens the existing primary finite-energy theorem by proving convergence on
every bounded nonnegative profile, including the infinite-energy branch. The source
application is `D(t)=C(0)-C(t)`, bounded between zero and `2C(0)` by the L² correlation laws.

## Dependency audit and Lean obligations

- L² correlation continuity, compact support, and Krein dependencies are checked above.
- Primary mass, positive-shift scale, pointwise tangent, and the Lévy envelope are the
  declarations of `SuzukiCriticalBetaKernel.lean`; none assumes RH or source positivity.
- Fatou is the nonnegative integral inequality `lintegral_liminf_le`; no limiting integral
  is represented by a totalized nonintegrable real Bochner integral.
- Uniform primary weak convergence follows from smooth L² density and the exact kernel-mass stability bound.
- The extended-real Fatou passage and literal fixed-cutoff arithmetic assembly are implemented in the canonical leaves below.
- The ordinary finite-energy and infinite-energy branches are kept separate; divergent limiting energy is never represented by a totalized real integral.

The complete paper proof is implemented by nine canonical Lean leaves. The
source-domain hypotheses are exactly real L² membership and compact support;
no differentiability or finite limiting-energy premise is added. All canonical
source checks and all 42 public transitive axiom audits passed.

For the L² specialization, let `q` be the source's Hilbert-space class and `T_t` the
measure-preserving translation isometry. Almost-everywhere representative invariance gives
`C_f(t)=<q,T_t q>`. Strong continuity of `T_t` proves continuity of `C_f`; Cauchy–Schwarz
and `||T_t q||=||q||` give `|C_f(t)|<=||q||²=C_f(0)`. Thus `D=C_f(0)-C_f` satisfies all
three profile conditions above for every real L² source, without compact support.
The same calculation gives the uniform stability estimate
`|C_q(t)-C_r(t)| <= (||q||+||r||)||q-r||`, by splitting the difference as
`<q-r,T_t q>+<r,T_t(q-r)>`. This supplies an alternative smooth-density proof of the
primary weak limit, with no limiting-energy assumption.

For completeness, that density passage is quantitative. Write
`E(q,r)=(||q||+||r||)||q-r||`. Positive primary mass gives, for every cusp location,
`|primaryCusp(q,w,u)-primaryCusp(r,w,u)| <= M_w E(q,r)`.
Given `epsilon>0`, smooth compact L² density supplies a class `r` with
`||q-r|| < min(1,epsilon/(6(2||q||+1)))`. The triangle inequality gives
`||r||<=||q||+||q-r||`, hence `E(q,r)<epsilon/6`. A smooth compact representative of
`r` has uniform primary cusp error less than `epsilon/3` for all sufficiently small
positive shifts, by the parent theorem. Also `M_w<2` eventually. Adding the two
correlation errors and the cusp error bounds the total uniformly by
`2E(q,r)+epsilon/3+E(q,r)<epsilon`. This proves the primary cusp convergence for
every real L² source, even without compact support or finite limiting energy.

## Pointwise pole limit without a second compact Fubini proof

The corpus also supplies `CHMDDoobGraph.integrable_archLevy_firstMoment` and
`archLevy_firstMoment_le`. Its density is half of `w_arch`; hence
`integral_0^infinity t*w_arch(t)` is finite. Apply the primary compensated limit
with `D(t)=t` on the positive ray. Multiplying its finite limit by `w` proves
`L_w=integral_0^infinity t*B_w(t) -> 0`. The bound
`B_w(t)<=w*a_w*w_arch(t)` also proves ordinary absolute integrability of this
first moment for every sufficiently small positive shift.

Fix `t>0` and `0<w<=1/2`, and set `a=1/2-w`. On `r>0`, define
`v_(w,t)(r)=exp(-a*r)` for `r<t`, and zero otherwise. Then
`0<=v<=1` and `0<=1-v<=(1+1/t)r`: on `r<t`, use
`exp(-ar)>=1-ar` and `a<=1`; on `r>=t`, use `1<=r/t`.
The literal pole satisfies
`Q_w(t)=exp(a*t)*integral_0^infinity B_w(r)*v_(w,t)(r) dr`.
Consequently

`0 <= M_w-exp(-a*t)Q_w(t) <= (1+1/t)L_w`,
`0 <= Q_w(t) <= M_w exp(t/2)`.

Since `M_w->1` and `L_w->0`, this proves `Q_w(t)->exp(t/2)` for every `t>0`.
Measurability follows by writing its defining triangle integral as a measurable
indicator on `(t,r)`. For a compact L² autocorrelation, the bound `|C|<=R`,
its support cutoff, and eventually `M_w<=2` give the integrable majorant
`2R exp(A/2)` on `(0,A)`. Dominated convergence therefore proves the full pole
pairing limit on this source domain. The same bound supplies its absolute
integrability at every small shift. This alternative preserves the growing
pole and avoids extending the earlier private convolution lemmas.

## Gates

- [x] Precise source-domain conjecture and attack mechanism.
- [x] Dependency-closed paper proof with the L² and extended-limit dependencies checked.
- [x] Canonical Lean check and public-declaration axiom audit.

## Lean implementation

All paths below are under `formal/GaloisForLFunctions/RHTower/Suzuki/`.

| Module | Public declarations | Contribution |
|---|---:|---|
| `SuzukiCriticalExtendedEnergy` | 3 | Bounded-profile extended energy limit |
| `SuzukiCriticalL2Energy` | 8 | L² correlation and energy laws |
| `SuzukiCriticalL2Cusp` | 5 | Uniform translated primary convergence |
| `SuzukiCriticalL2PrimaryVariation` | 4 | Exact extended primary quotient |
| `SuzukiCriticalPolePointwise` | 8 | First moment and pointwise growing-pole limit |
| `SuzukiCriticalL2Pole` | 6 | Compact L² pole and signed-cusp limits |
| `SuzukiCriticalL2Arithmetic` | 3 | Literal arithmetic assembly and tangent |
| `SuzukiCriticalL2WeilNormalization` | 3 | Positive-tail and Gamma normalization |
| `SuzukiCriticalL2FirstVariation` | 2 | Full extended first variation and infinite-energy deficit |

The capstones are
`RHTower.tendsto_suzukiCriticalSourcePairing_extended_firstVariation` and
`RHTower.eventually_suzukiCriticalSourcePairing_lt_mass_of_infiniteEnergy`.
The limit reuses `ArithmeticPositivityTheory.sourceLevyEnergy` and
`SignedPrimePolar.fullPairing`; it does not introduce an assumed positivity
interface or a totalized divergent spectral integral.

## Verification

All nine canonical modules compile. All 42 public declarations have transitive
axioms contained in `propext`, `Classical.choice`, and `Quot.sound`. The combined
audit runs in `SuzukiCriticalLiteralFamilyContraction.lean`, which imports the
complete chain and prints these 42 declarations plus its two consequences:

```sh
cd formal
lake --old env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalLiteralFamilyContraction.lean
```

This command passed. No placeholders, extra axioms, trusted-computation shortcuts,
or raised proof limits occur in these modules. Only oleans required by written
downstream modules were created. Each finished module is imported once by
`RHTower.lean`; no umbrella compilation was run.
