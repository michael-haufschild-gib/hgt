# WP06 proof register

## Candidate A: sharper arithmetic cost of spectral deficit

Conjecture: for every full-positive `λ`, integer `n ≥ 2` and `ε > 0`, eventually

`|λ(n) − Λ(n)| ≤ 4π√n (D(T)/T + ε)`.

The current corpus has `n` in place of `√n`. Mechanism: subtract the actual shared critical atoms; compare fixed-frequency Fourier averages of the remaining positive measure with those of the deficit divisor. The Poisson Fourier multiplier cancels the excess abscissa. No RH assumption is used.

**Status: paper argument below; Lean analytic dependencies remain open.** This is a proposed quantitative corollary of classical Fourier theory and the corpus's full-positive measure representation, not a claim of a new foundational theorem. The searches recorded in `EVIDENCE.md` have not located this precise improvement; they do not certify novelty.

### A1. Truncated Poisson transport

Write `P_b(x)=b/(b²+x²)`, with fixed `b>0`, and `μ=boundaryMeasure hW`. The corpus proves `μ([r−1,r+1])≤C log(|r|+3)`. For every fixed real `k` and `T≥2`,

`∫_0^T exp(ikt)(P_b*μ)(t) dt = π exp(−b|k|) ∫_(0,T] exp(ikr) dμ(r) + O_(μ,b)(log²(T+3)).` (A1)

Here the error bound can be chosen independently of `k`. The full-line Poisson transform is `∫_ℝ exp(ikx)P_b(x)dx=πexp(−b|k|)`. Subtract the full-line transform separately for each `r∈(0,T]`, leaving exactly the transport across the two endpoints. Absolute value of the remainder is bounded by

`∫ μ(dr) ∫ P_b(t−r) |1_(0,T](t)−1_(0,T](r)| dt`.

Tonelli applies because the integrand is nonnegative. On `−T≤r≤2T`, the inner integral is bounded by a constant times the sum of `(1+|r|)⁻¹` and `(1+|r−T|)⁻¹`. Cover by unit intervals. Each has mass `O(log(T+3))`, and summing the two reciprocal-distance bounds costs `O(log(T+3))`. For `r<−T` or `r>2T`, the inner integral is at most `C_b T/r²` after an absolute constant change in the positive tail. The unit-interval sum is bounded by `C_b T Σ_(j≥T) log(j+3)/j²=O_b(log(T+3))`. Endpoint atoms are covered by the adjacent bounded intervals. This proves the finite error estimate and also the absolute integrability needed for Fubini in (A1). The estimates apply to `k=0` as well.

### A1a. A less demanding formal route to the sufficient `o(T)` error

Lean status: interval mass, scalar leakage bounds, the finite four-region estimate and the full `o(T)` leakage limit are formalized in `WeilWorkDeficitMassBounds`, `WeilWorkDeficitPoissonLeakage` and `WeilWorkDeficitLeakageIntegral`. Direct audits and targeted builds passed; all eleven public theorem axiom audits use standard foundations only. The subsequent complex Fourier transport is still paper-only.

The coefficient argument needs only `o(T)`, so it need not formalize the sharper logarithmic-square error first. The following complete alternative uses the already proved integrability of `(1+r²)⁻¹` against the canonical measure.

First extend the unit-window bound to all `a≤b`:

`μ([a,b])≤C(b−a+1) log(max(|a|,|b|)+3)`. (A1a)

Cover `[a,b]` by the intervals of radius one centered at `a+j`, with `j=0,…,floor(b−a)`. Every point is covered by taking `j=floor(x−a)`. Every center belongs to `[a,b]`; there are at most `b−a+1` centers. Summing the existing unit-window estimate proves (A1a). This is a bridge, not a novelty claim.

For the leakage integral in (A1), take `H=√T` and `T≥1`. On the two endpoint neighborhoods `[-H,H]` and `[T−H,T+H]`, the leakage kernel is at most `π`. By (A1a), their contribution divided by `T` is `O(log(T+3)/√T)`. On the rest of `[-2T,2T]`, the distance to each relevant endpoint is at least `H`; integration of `b/x²` bounds the leakage by `2b/H`. By (A1a), this contribution divided by `T` is also `O(log(T+3)/√T)`.

For `|r|>2T`, the ordinate lies outside `(0,T]` and the leakage is at most `4bT/r²`. After division by `T`, it is bounded by `8b/(1+r²)` and vanishes eventually for each fixed `r`. Dominated convergence makes this last contribution tend to zero. Thus the full leakage divided by `T` tends to zero, with no tail-rate assumption. All bounds are independent of the Fourier frequency because the character has modulus one.

Formal sequence: arbitrary-interval mass bound; elementary leakage-kernel inequalities; integrable-tail limit; actual canonical Fourier transport. No additional hypothesis is to be added to the capstone.

For the fixed width `b=3/2`, write `L_T(r)=|K_T(r)−π1_(0,T](r)|` and
`Q(T)=∫_(|r|>2T) (1+r²)⁻¹ dμ(r)`. The explicit finite bound being formalized is, for `T≥1,H>0`,

`∫L_T dμ ≤ πμ([-H,H])+πμ([T−H,T+H])+(3/H)μ([-2T,2T])+12T Q(T)`.

Every point belongs to one of the two endpoint intervals, to the remainder of the bulk interval, or to its complement. The first two costs use `L_T≤π`. Outside the endpoint intervals both distances are at least `H`, so the arctangent tail inequality gives `L_T≤3/H`. Outside the bulk, `|r−t|≥|r|/2` for `0≤t≤T`; integrating the resulting bound on `P_(3/2)` gives `L_T≤12T/(1+r²)`. Indicator majorants for these four regions are integrable by (A1a) and Cauchy-weight integrability. This proves the displayed estimate without a prior integrability assumption on `L_T`. Dominated convergence gives `Q(T)→0`. At `H=√T`, (A1a) bounds the other three costs divided by `T` by `(6π+15)C log(2T+3)/√T`, which tends to zero.

The next exact Fourier transport bound follows pointwise before Fubini. Put `U=(0,T]`. For every bounded measurable complex `φ` with `|φ|≤1`,

`|∫_U φ(t)P_(3/2)(t−r)dt − 1_U(r)∫_ℝ φ(t)P_(3/2)(t−r)dt| ≤ L_T(r)`.

For `r∉U` this is the norm bound on the window integral. For `r∈U`, subtract the full integral and bound the integral over `Uᶜ`; its positive kernel mass is `π−K_T(r)`. Integrability of `K_T` follows from `K_T≤L_T+π1_U` and finiteness of `μ(U)`. This also pays absolute product integrability in Fubini, since the character has norm one. For `φ(t)=exp(ikt)`, translation and the corpus Cauchy Fourier identity identify the full integral as `πexp(-(3/2)|k|)exp(ikr)`. Integrate the pointwise bound against `μ`, use Fubini and the canonical Poisson representation. The resulting error is bounded by `∫L_T dμ` for every real `k`. Its normalization by `T` tends to zero even if `k` is chosen as a function of `T`. This uniformity is for the forward transport error; division by the vanishing Fourier multiplier does not give uniform recovery at unbounded frequencies.

### A2. The canonical measure's arithmetic Fourier coefficients

Use `b=3/2`, so `(P_b*μ)(t)=Re Φ(2+it)`. The arithmetic identity in the corpus gives

`Re Φ(2+it)=A(t)−Σ_(j≥2) λ(j)j⁻² cos(t log j)`.

The series is absolutely and uniformly convergent. The archimedean term satisfies `A(t)=½log(t/(2π))+O(1/t)` for `t≥2`; its bounded initial segment contributes `O(1)`. For fixed nonzero `k`, integration by parts of the logarithm shows `T⁻¹∫_0^T exp(ikt)A(t)dt→0`. At `k=log n`, elementary exponential averaging and dominated convergence for the absolutely summable series give

`T⁻¹∫_0^T exp(it log n)Re Φ(2+it)dt → −λ(n)/(2n²)`.

Divide (A1) by `T`; its error tends to zero. Since `exp(−(3/2)log n)=n⁻³ᐟ²`,

`T⁻¹∫_(0,T] exp(ir log n)dμ(r) → −λ(n)/(2π√n)`. (A2)

For `k=0`, (A1) and the already proved smoothed counting law give

`M(T):=μ((0,T]) = T/(2π)log(T/(2π))−T/(2π)+O_μ(log²(T+3))`.

The ordinary zero count `N(T)` has the same main term with error `O(log(T+3))`. Thus `M(T)−N(T)=o(T)`. The count comparison is used only for the surplus left after subtracting shared mass; it is not treated as evidence of overlap.

### A3. Actual zero ordinates

[Ford–Zaharescu, Theorem 1 and Corollary 2](https://arxiv.org/html/math/0405459v2) give an unconditional, multiplicity-counted ordinate limit normalized by `T`. Applying their result to the smooth first character at `α=log n/(2π)` and evaluating its coefficient in their density gives

`T⁻¹ Σ_(q:0<γ_q≤T) exp(iγ_q log n) → −Λ(n)/(2π√n)`. (A3)

For non-prime-powers the coefficient is zero; for `n=p^a` it is `−log p/(2πp^(a/2))`. This invokes neither their RH-dependent extension to rough tests nor their conjecture for interval indicators. Ordinary zero-count-normalized equidistribution would not suffice.

A route using only corpus ingredients is also available in principle: the Poisson Fourier identity for the actual divisor produces an extra factor `cosh((β−1/2)log n)` after reflection pairing. Its excess is bounded by a constant times `Σ(β−1/2)²`. `SelbergExponentialNearLineDensity` supplies a uniform moving-scale exponential density estimate. Transporting its admissible rectangles to multiplicity copies and summing the tails should prove this excess is `o(T)`. **This formal transport has not been completed.** The previously inspected weaker `SelbergNearLineZeroDensity` alone was not a justified replacement.

### A4. Exact shared mass and the comparison

Let `ν_T=Σ_(q:0<γ_q≤T) δ_(γ_q)`. At each actual critical divisor point `ρ=1/2+iγ` in the window, retain mass `min(m_ρ, μ({γ}))`; let `χ_T` be the resulting finite atomic measure. Distinct critical points have distinct ordinates. Hence `χ_T≤μ|_(0,T]` and `χ_T≤ν_T`, even when off-line zeros have those same ordinates. By the exact definition of the copy deficit,

`χ_T(ℝ)=N(T)−D(T)`.

Put `μ_T^+=μ|_(0,T]−χ_T` and `ν_T^−=ν_T−χ_T`. These are positive finite measures, with masses `M(T)−N(T)+D(T)` and `D(T)`. For every measurable `f` with `|f|≤1`, the exact decomposition and estimate are

`∫f dμ|_(0,T]−∫f dν_T = ∫f dμ_T^+−∫f dν_T^−`,

`|∫f dμ|_(0,T]−∫f dν_T| ≤ M(T)−N(T)+2D(T)`. (A4)

Taking the character from (A2)–(A3), dividing by `T`, and using `M(T)−N(T)=o(T)` proves the eventual bound in Candidate A for every positive `ε`. This improves the coefficient scale but gives no upper bound on `D(T)`.

### A5. Attack verdict and next formal obligation

- A possible diffuse part of `μ` remains in `μ_T^+`; no discreteness assumption enters.
- Multiplicities are retained in both `ν_T` and `χ_T`.
- Shared ordinates involving off-line zeros only make `χ_T≤ν_T` easier; they do not erase off-line deficit.
- All limits use fixed `n`; no uniformity in `n` is asserted.
- No atom is identified from a smoothed window.
- (A4) is now formalized for the actual canonical objects in `WeilWorkDeficitSharedMass.lean`, with direct Lean and standard-only axiom audits. The analytic transport and linear-scale Fourier limits must next be compiled, not inserted as premises of a claimed unconditional coefficient theorem.

## Bridge B: uniform recovery on every prefix of a bounded height window

This bridge is not claimed as novel science. It pays the passage from Poisson values to the exact atom deficits without inserting a uniform convergence assumption.

Lean status: `WeilWorkDeficitRecovery.lean` compiled, directly audited, umbrella-wired; all eight public theorem axiom lists contain only standard Lean foundations.

Fix a full-positive `λ`, with canonical measure `μ` and continuation `Φ`. For each actual zero copy `q`, write `m_q` for its positive multiplicity and `γ_q` for its ordinate. Define

`a_b(q) = b Re Φ(1/2+b+iγ_q)/m_q`,

and `d_b(q) = max(1-a_b(q),0)` at critical copies, `d_b(q)=1` elsewhere. Put

`D_b(T) = Σ_(0<γ_q≤T) d_b(q)`.

For each `M`, let `S_M` be the finite set of copies with `0<γ_q≤M`, and define the complete recovery remainder

`R_M(b) = Σ_(q∈S_M) |d_b(q)-d(q)|`.

Then, unconditionally for this `λ`,

1. `D(T) = D_b(T) + Σ_(0<γ_q≤T)(d(q)-d_b(q))` for every real `b,T`.
2. For every `T≤M`, `|D_b(T)-D(T)|≤R_M(b)`.
3. `R_M(b)→0` as `b→0+`.
4. Consequently, for every `M` and `ε>0`, some `δ>0` satisfies `|D_b(T)-D(T)|<ε` simultaneously for all `T≤M` and all `0<b<δ`.

Proof: `S_M` is finite because it is contained in the bounded ordinate band `|γ_q|≤|M|`, whose finiteness is `finite_xiZeroCopy_band`. For `T≤M`, every summand outside `S_M` vanishes. Thus every infinite sum in (1) and (2) is literally a finite sum over `S_M`. Subtraction and the finite triangle inequality prove (1) and (2). At each critical copy the existing theorem `tendsto_mul_re_weilContinuation_atom` gives `a_b(q)→μ({γ_q})/m_q`; continuity of subtraction, maximum and absolute value gives `|d_b(q)-d(q)|→0`. At off-line copies this difference is identically zero. The finite-sum limit proves (3); the definition of a right-hand limit gives (4). This includes all multiplicity copies and all prefixes, including empty negative-height prefixes. It supplies no rate for `δ(M,ε)` and no small-deficit bound.

## Rejected cycle: total count / surplus balance

Verdict: **REDISCOVERED / BRIDGE**. The earlier singular-deficit card, especially L127 and its cycle-222 addendum, already records surplus compensation, and `WeilFullConePoissonCountingIdentity` formalizes the smoothed balance. A restatement does not advance detection. The paper card's claim that logarithmic local mass alone yields an `O(log T)` unsmoothing error needs a separate audit: absolute Poisson tails generally accumulate a harmonic factor. No contradiction to the compiled smoothed identity is asserted.

## Main target

Still open: derive `∀ η>0, ∃ᶠ T→∞, D(T)/T≤η` from full Weil positivity. Neither Bridge B nor Candidate A supplies this estimate.

## Candidate A, internal subtraction route (2026-10-07)

This replaces the separate archimedean and Riemann–von Mangoldt asymptotics in A2–A3. Classification: **BRIDGE** to the sharper coefficient estimate; no small-deficit conclusion and no novelty claim for the auxiliary density argument.

### Exact arithmetic mean, with no new premise

Fix `hW : WeilPositiveFull λ`, a real `σ>1`, and `n≥2`. Set
`Fσ(t)=Re Φλ(σ+it)−Re ξ'/ξ(σ+it)` and
`a_j=(Λ(j)−λ(j))j^(−σ)` for `j≥2`, zero for `j=0,1`.
`WeilConeSingularDeficitEnvelope.summable_abs_deviationCoeff` proves absolute summability, and `re_weilFunction_sub_re_logDeriv_xi`, together with `weilContinuation_eq`, proves `Fσ=logCosSeries a`. The continuous cosine series is integrable on every bounded interval. The corpus's `tendsto_mean_logCosSeries_mul_cos` and `bohrLimit_eq_coeff` therefore give

`T⁻¹∫_0^T Fσ(t) cos(t log n)dt → (Λ(n)−λ(n))n^(−σ)/2`.

The cited mean starts at 8. Add the fixed finite integral from 0 to 8, divide by T, and use its limit zero. At frequency zero, use `bohrLimit_one_eq_zero` instead: `T⁻¹∫_0^T Fσ(t)dt→0`. This proof is dependency-closed before Lean; both identities are merely exact extraction from an already proved series, not a new rigidity claim.

### Horizontal square moment: paper derivation from the strong corpus estimate

Let `δ_q=|β_q−1/2|` and `Q(T)=Σ_(0<γ_q≤T) δ_q²`, retaining every Xi divisor copy. The theorem `exists_selberg_exponential_nearLine_zeroDensity` supplies constants A,K and common admissible heights `T₁∈(U/4,U/4+1)`, `T₂∈(U/2−1,U/2)` for all permitted scale parameters a. Put `L=log U` and `a=2400 log L`. Eventually `a≥1` and `2a+2≤L`, because `log L/L→0`. Its far-right count, divided by U, is bounded by

`A/(8πaL) + K L²/(2πaU)`.

Indeed the exponential is `exp(−a/1200)=L^(−2)`, and `T₂−T₁≤U/4`. The count is a sum of analytic orders. On these high rectangles zeta is analytic and the Xi and zeta orders agree; the rectangle zero set is finite by isolated zeros on a compact set. Thus it counts exactly the right-hand Xi copies. `xiZeroCopyLineConjEquiv`, with `xiZero_lineConj_eq`, preserves ordinate and multiplicity and exchanges the two sides of the critical line. It doubles this upper bound to control all copies with `δ_q≥2a/L`.

The remaining copies have squared displacement at most `(2a/L)²`. The exact uniform unit-window bound `ncard_xiOrdinateWindow_one_le_log`, summed over a unit cover, bounds the whole dyadic-band count by `O(U log U)`. Thus their contribution divided by U is `O(a²/L)→0`. Far copies have `δ_q²<1/4`, so their contribution divided by U also tends to zero. The two omitted endpoint strips have width at most one and `O(log U)` copies by the same unit-window bound; their contribution is negligible. This proves `Σ_(U/4<γ≤U/2)δ_q²=o(U)`.

For completeness, the passage to the full prefix does not assume a uniform number of dyadic bands. Given ε>0, choose V₀ so every band `(V,2V]`, V≥V₀, has square mass at most εV. For any large T, successively halve T until the lower endpoint lies below V₀. The sum of the band bounds is at most εT; all remaining copies lie in the fixed bounded window `(0,2V₀]`, of finite square mass. Divide by T. Since ε is arbitrary, `Q(T)/T→0`.

This is a complete paper reduction to the cited strong estimate and exact multiplicity transport. The Lean transports of rectangle analytic orders, endpoint strips, and the dyadic prefix sum remain unpaid; no theorem assuming `Q(T)=o(T)` may be reported as unconditional progress on Candidate A.

**Stronger corpus input found before implementation.** `ZetaCriticalScaleExponentialTailMoment.exists_offLineTailMoment_window_exponential_le` already proves, with the same admissible heights and every fixed `c≥4`,

`Σ_(δ≥c/L, right side) mδ ≤ A/(2π)(1+4800/c)exp(−c/4800) U + (2K/π)L²`.

Use this in place of the moving-cutoff calculation above. For each fixed c, near copies contribute `O(c²/L)` to `Q/U`; on the far set, `δ²≤δ/2`. Pairing the left side gives
`limsup Q_band(U)/U ≤ A/(2π)(1+4800/c)exp(−c/4800)`.
This bound holds for every `c≥4`; letting c tend to infinity proves the same zero limit. This removes all moving-parameter admissibility work and reuses an existing weighted result. `ZetaRightZeroWeightedCount.windowZeros` and `mem_windowZeros_iff` already construct the exact finite rectangle; do not reconstruct it. The remaining new Lean work is multiplicity-copy transport, interval endpoints, and the prefix assembly. No fresh scientific novelty is asserted for this consequence.

An even smaller sufficient input is already proved in `ZetaCriticalScaleTailMoment.exists_offLineTailMoment_window_le`: its tail bound is `(D/c)(T₂−T₁)+K L²` for every `c≥2`. The identical square-moment split gives `limsup Q_band(U)/U≤D/(4c)`, and c is arbitrary. Thus the exponential refinement is unnecessary for this fixed-frequency projection. The earlier warning about the weak count alone remains valid; the inspected, uniform **weighted tail theorem** supplies the additional inference. Prefer this smaller input when formalizing the projection.

### Exact finite-copy estimate to formalize

The preceding tail theorem implies the following unconditional statement. There are D,K≥0 such that, for every sufficiently large U, admissible T₁,T₂ exist and, for every c≥2 and every finite set F of actual Xi copies with ordinates in `[T₁,T₂]`,

`Σ_(q∈F)(β_q−1/2)² ≤ (c/log U)² #F + (D/c)(T₂−T₁)+K(log U)²`.

Here is the multiplicity audit. For any finite F and finite complex set Z containing all its support points, enlarge F to all copies above its support image S. For nonnegative f this gives `Σ_F f(ρ_q)≤Σ_(ρ∈S)m_ρ f(ρ)≤Σ_(z∈Z)ordζ(z)f(z)`, since Xi and zeta have equal analytic order in the open strip. Apply this to the right tail, with `f(z)=max(Re z−1/2,0)` and Z the corresponding filter of the existing `windowZeros T₁ T₂`. Each right tail sum is at most B=`(D/c)(T₂−T₁)+K(log U)²`.

For the left tail, send its copies through the injective `xiZeroCopyLineConjEquiv`. This preserves ordinates and changes the displacement to its negative. Its image is another finite set in the right tail, so its weighted sum is also at most B. No closure of F under conjugation is needed. Write v=`c/log U`>0 and δ=`β−1/2`, with `|δ|<1/2`. Pointwise,

`δ² ≤ v² + (1/2)1_(v≤δ)δ + (1/2)1_(v≤−δ)(−δ)`.

If neither tail condition holds, `|δ|<v`; in either tail use `δ²≤|δ|/2`. Summing proves the claimed estimate. This paper proof precedes the new Lean module. It is a precise corpus consequence and a bridge to the full prefix square-moment limit, not a fresh density conjecture.

### Endpoint and prefix assembly, exact quantifiers

For every ε>0, eventually in U, **every** finite set F of copies with `U/4<γ≤U/2` satisfies `Σ_F δ²≤εU`. To prove this, retain G with `T₁≤γ≤T₂`. The near contribution in the finite-copy estimate is bounded by `(c/log U)² #F`. `XiZeroCountLocalCeiling.exists_card_window_le`, applied at t=U/4 and H=U/4, gives `#F≤(U/(8π)+2C)log(U/2)`. Thus this contribution divided by U tends to zero for each fixed c. The remaining G terms divided by U are at most `D/(4c)+K(log U)²/U`.

Every copy in F outside G lies either in the unit window centered at U/4 or in the unit window centered at U/2. Since δ²≤1/4 and `ncard_xiOrdinateWindow_one_le_log` bounds each window by `16(C₀+log(|t|+4))`, the lost square mass is at most `8(C₀+log U)` for U≥16. Divide by U. Choose c≥2 with `D/(4c)<ε/2`, then choose U large enough that all terms tending to zero total less than ε/2. The choices are independent of F, giving the asserted uniform finite-set bound.

For the full prefix Q, first obtain `∀ ε>0, ∀ᶠ t→∞, Q(2t)−Q(t)≤εt` by substituting U=4t and applying the uniform band bound with tolerance ε/4. Q is nonnegative and monotone, since its finite sums have nonnegative weights. Choose V≥1 after the threshold for a given ε. Induction gives
`Q(2^n V)≤Q(V)+ε·2^n V` for all natural n: the next band contributes at most `ε·2^n V`. For T≥V choose n with `2^n≤T/V<2^(n+1)`. Monotonicity yields
`Q(T)≤Q(V)+2εT`.
Hence `Q(T)/T≤Q(V)/T+2ε`. First let T tend to infinity, then ε tend to zero; the nonnegative quotient converges to zero. This proof uses no unproved uniformity in the number of dyadic bands and no premise about critical support.

### Zero-side transport and cancellation

For each copy use `P_b(t−γ)` with `b=2−β∈(1,2)`. Its full Fourier transform is `π exp(−b|k|)exp(ikγ)`. The finite-window error is its omitted mass inside the window and its included mass outside. Pointwise, `P_b≤(3/2)P_(3/2)` for all `1≤b≤2`, so the error is bounded by `3/2` times the fixed-width leakage at the same ordinate. The zero-copy measure has logarithmic interval mass by `XiWindowZeroCount` and an integrable Cauchy weight by the existing weighted zero-copy summability. Hence the same endpoint-width `√T` and Cauchy-tail argument used for the canonical measure gives total zero-side error `o(T)`.

Pair copies by **line conjugation** `ρ↦1−conj ρ`, not reflection `ρ↦1−ρ` (the latter changes ordinate sign). The multiplier becomes `π exp(−(3/2)|k|) cosh((β−1/2)|k|)`. For fixed k, Taylor's theorem on `[-|k|/2,|k|/2]` gives `|cosh(kδ)−1|≤C_k δ²`; the square-moment result makes the summed multiplier error `o(T)`. At k=0 this replacement is exact and needs no density theorem.

Subtract the canonical and zero transport identities, take real parts at `k=log n`, and use the arithmetic mean at σ=2. This yields
`T⁻¹ Re(∫_(0,T]e^(ir log n)dμ−∫_(0,T]e^(ir log n)dν) → (Λ(n)−λ(n))/(2π√n)`.
At k=0 it yields `(M(T)−N(T))/T→0`. Applying the already compiled shared-mass inequality proves Candidate A. These final transports are a paper proof, not yet a compiled capstone.
