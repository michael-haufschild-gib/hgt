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
The compact C² parent theorem must first be completed in Lean, including its arithmetic terms.

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

The paper proof is complete. Lean formalization remains pending. The compact C² parent
provides the currently compiled archimedean leaves; its arithmetic assembly is shared work.

## Gates

- [x] Precise source-domain conjecture and attack mechanism.
- [x] Dependency-closed paper proof with the L² and extended-limit dependencies checked.
- [ ] Canonical Lean check and public-declaration axiom audit.
