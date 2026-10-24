# Literal critical source on the compact L² energy domain

- **ID:** sz-critical-source-extended-energy-domain-2026-10-24
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `sz-critical-source-first-variation-2026-10-18`; corpus Krein increments and critical Beta kernel.
- **Statement:** Every real compactly supported L² source has an extended-real critical first variation of the literal Suzuki arithmetic source, equal to its complete Weil energy, including value `+infinity` when its Lévy energy is infinite.

## Route and significance

WL still requires an arithmetic one-sided critical bound at every positive exponential slack.
This paper theorem concerns the analytic source domain, not that missing sign. It makes the
literal critical source available on the closed energy domain without a smoothness premise,
and would identify exactly what happens to sequences whose energy escapes to infinity.
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
- Formalize the primary weak convergence without finite-energy domination.
- Close the extended-real Fatou passage and the literal fixed-cutoff arithmetic assembly.
- Keep the ordinary finite-energy and infinite-energy branches separate in Lean so that the
  totalized real Bochner integral cannot silently turn an infinite energy into zero.

The paper proof is complete. `SuzukiCriticalExtendedEnergy.lean` passes its direct source
check. Its theorem `tendsto_suzukiCriticalCompensatedEnergy` proves the bounded-profile
limit in `ENNReal`, including the infinite-energy branch, without a finite-energy premise.
`SuzukiCriticalL2Energy.lean` also compiles. Its capstone
`tendsto_suzukiCriticalCompensatedEnergy_autocorr` discharges all profile conditions
for every real L² source, without compact support, smoothness, or finite energy.
Public-declaration axiom audits are in progress. The complete compact C² parent is
certified in stage 3; the full compact-L² extension remains unfinished in Lean.

`SuzukiCriticalL2Cusp.lean` now also compiles. Its theorem
`tendstoUniformly_suzukiCriticalPrimaryCusp_of_memLp` proves the weak primary limit
uniformly over every real translation for every real L² source. Its stability
estimate `abs_suzukiCriticalPrimaryCusp_sub_le_L2_norms` pays all translations by
one Hilbert-space approximation error. These three new leaves are wired into the
umbrella; no umbrella compilation was run. The signed pole, extended-real
quotient, and complete arithmetic assembly remain the active Lean obligations.

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
- [ ] Canonical Lean check and public-declaration axiom audit.

## Lean checkpoint

- Compiled canonical leaves: `SuzukiCriticalExtendedEnergy` (3 public declarations),
  `SuzukiCriticalL2Energy` (8), `SuzukiCriticalL2Cusp` (5), and
  `SuzukiCriticalL2PrimaryVariation` (4), and `SuzukiCriticalPolePointwise` (8). Their dependency oleans
  were created for actual downstream imports. Do not rebuild existing oleans.
- The first 28 declarations' `#print axioms` outputs contain only `propext`,
  `Classical.choice`, and `Quot.sound`; the combined final clean audit remains pending.
- `SuzukiCriticalL2PrimaryVariation.lean` proves the actual L² primary quotient
  in `EReal`. Its four declarations passed their imported axiom inspection.
- `SuzukiCriticalPolePointwise.lean` contains the full first-moment, pole
  measurability, pointwise bound, and pole-limit proof; its canonical source check
  and dependency olean creation both passed. Its eight declarations passed their
  imported axiom inspection.
- `SuzukiCriticalL2Pole.lean` contains compact L² pole testing, signed cusp
  convergence, and extended signed cusp variation. The scratch and first canonical checks found one
  composition/coercion simplification issue. An isolated extended-real scratch
  proof now passes: explicitly expose the sum-valued function before rewriting
  its limit, rather than simplifying casts beneath an inferred composition.
  That correction passed: the canonical file and its downstream dependency
  olean are now checked. All six public declarations are proved; their combined
  axiom audit remains pending. The normalization scratch check is active.
- `SuzukiCriticalL2Arithmetic.lean` extends the exact literal finite sum and its
  extended first variation. `SuzukiCriticalL2WeilNormalization.lean` identifies
  the existing extended `sourceLevyEnergy` by the finite exponential correction
  and Gamma recurrence. The normalization scratch check verified the required
  integral and EReal APIs; two elaboration issues were fixed by an explicit
  `IntegrableOn` type and exposing positive-ray membership. Its canonical source
  and dependency olean now pass. The arithmetic leaf also passed its canonical
  check and dependency olean creation. The capstone scratch check, including
  the complete 42-declaration axiom inspection, is active.
- `SuzukiCriticalL2FirstVariation.lean` contains the complete cutoff-free capstone
  and eventual strict deficit for infinite-energy compact L² sources. It awaits
  the arithmetic and normalization dependency checks.
- The concrete unsmoothed critical-family consequence has a complete paper proof
  in `sz-critical-family-literal-source-deficit-2026-10-24.md` and a pending draft
  `/tmp/sz-critical-family-literal-api.lean`; finish the L² capstone first.
- Remaining: check and canonicalize these drafts, extend the exact finite arithmetic
  assembly to L² sources, identify the compensated energy with the existing
  `ArithmeticPositivityTheory.sourceLevyEnergy` plus its finite exponential correction,
  and finish one dependency-closed canonical audit. The parent compact-C² card is
  already certified in stage 3 by shared work; preserve its completed leaves.

## Finalization scope

The user paused the broader RH goal and requested completion of the current
Lean work. Finish the compact-L² capstone, the direct literal compact-family
consequence, and the already written varying-primary Fatou draft. Complete
canonical checks, all public axiom inspections, umbrella imports, and cleanup.
Do not begin the untruncated-source formalization or the remaining full
moving-source Gamma-limit assembly in this finalization batch.

The capstone scratch check writes `/tmp/sz-critical-l2-source-check.log`.
Remaining drafts are `/tmp/sz-critical-family-literal-api.lean` and
`/tmp/sz-critical-moving-primary-api.lean`. Planned canonical leaves are
`SuzukiCriticalLiteralFamilyContraction` and `SuzukiCriticalMovingPrimaryEnergy`.
