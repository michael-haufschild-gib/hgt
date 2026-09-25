# One-sided Bernstein-positive theta gauge with both anchors and an off-line zero

- **ID:** theta-one-sided-bernstein-two-anchor-offline-zero
- **Stage:** 2-fully-proven (paper)
- **Type:** exact sharp countermodel to unreflected flux-and-charge orientation
- **Routes:** STC, CSB, U, K-RVM, MPLF, RHist; source-side comparison with EDQ
- **Status:** [PROVED HERE ON PAPER] [LEAN FORMALIZATION OPEN] [NOT A ZERO OF THE ACTUAL XI]
- **Dependencies:** the theta Gaussian-rate flux in [theta-euler-critical-boundary-mass-escape.md](theta-euler-critical-boundary-mass-escape.md), the source atom formula there, and the Mellin translation law. No numerical computation is used.

## Exact construction

Let `k` be the completed even positive theta source and put

`r=1/√2`, `κ=2−√2`, `d=√2−1=κr=1−κ`.

Choose any real parameter

`1/2<α<1/√2`.                                                  (1)

Define the **one-sided** integer-shift gauge

`g_α(x)=(1−dα)k(x)+α k(x+log 2)−κα k(x+log 4)`.         (2)

The coefficients include a negative shift weight, and `g_α` is not reflection-even. Nevertheless:

1. Its normalized completed flux `b_(g_α)(t)=t^(−3/2)∫_[log(t)/2,∞)exp(y/2)g_α(y)dy` is **completely monotone**. Its Gaussian rate weight at `πn²` is `2πn² R_n`, where

   `R_n=1−dα+√2 α·1_(2∣n)−2κα·1_(4∣n)`

   equals `1−dα>0` for odd `n`, `1+α>0` when `2∣n` but `4∤n`, and `1−d²α>0` when `4∣n`.

2. Both exact theta anchors are preserved:

   `∫_ℝ g_α=∫_ℝ k`, and `∫_ℝ exp(x/2)g_α(x)dx=∫_ℝ exp(x/2)k(x)dx=1/2`. (3)

3. `g_α(x)>0` for every `x≥0`. Indeed its rate expansion is `g_α=∑_(n≥1)R_n φ_(πn²)`; every `R_n` is positive, and every Gaussian atom `φ_(πn²)(x)=2πn² exp(5x/2)(2πn² exp(2x)−3)exp(−πn²exp(2x))` is positive on `x≥0`.

4. The bilateral Mellin transform of `g_α` has a zero at some `w=σ+iπ/log 2` with `0<σ<1/2`. This is a genuine zero of the deformed transform, independent of whether the original Xi transform has a zero there.

## Proof of the anchors and the zero

For `L_w f=∫_ℝ exp(wx)f(x)dx`, translation gives `L_w[k(·+log n)]=n^(−w)L_wk`. Thus

`L_w g_α=M_α(w)L_wk`,

`M_α(w)=1−dα+α2^(−w)−κα4^(−w)`.                      (4)

Set `z=2^(−w)`. The elementary identities `κ(1+r)=1` and `κr=d` give the exact factorization

`M_α(w)=1−κα(z−1)(z−r)`.                               (5)

At `w=0`, `z=1`; at `w=1/2`, `z=r`. Equation (5) makes the multiplier exactly one at both anchors, proving (3). For real `z`,

`M_α(z)|_(z=−1)=1−2α<0`,

`M_α(z)|_(z=−r)=1−√2 α>0`.                              (6)

By continuity there is a root `z₀∈(−1,−r)`. Write `z₀=−2^(−σ)`; because `r<|z₀|<1`, one has `0<σ<1/2`. Then `2^(−(σ+iπ/log 2))=z₀`, so (4) has the asserted interior off-line zero. No numerical root location or RH assumption is involved.

The source cannot be even: `L_wk` is positive and even on the real `w`-axis, whereas `M_α(w)` is not even. Indeed `M_α(w)→1−dα` as `w→+∞`, while `M_α(w)→−∞` as `w→−∞` because the negative `4^(−w)` term dominates.

## Proof of flux positivity

The theta flux has the positive atomic expansion `b_k(t)=2π∑_(n≥1)n² exp(−πn²t)`. Under `k(x+log m)`, a rate `πn²` receives an extra coefficient `√m` precisely when `m∣n`. Applying this with `m=2,4` to (2) gives `R_n` above. The three possible divisibility cases are exhaustive. Their stated values follow from `√2−d=1` and `2κ−1=d²`. The last is positive because `0<α<r<1` and `0<d²<1`. Thus `b_(g_α)` is a positive sum of exponential functions and is completely monotone. The same grouped expansion differentiated back through the flux law proves the right-ray positivity in item 3.

## Positive survivor: the complete finite-sieve cone

The countermodel fails a stronger property of the literal completed source. For each finite prime set `S`, let `D_S=∏_(p∈S)(I−p^(−1/2)T_(log p))`, where `T_u f(x)=f(x+u)`. For a general one-sided gauge

`g=c₁k+∑_(m≥2)c_m T_(log m)k`, `∑_(m≥2)|c_m|√m<∞`,

the coefficient of Gaussian rate `πn²` in the normalized flux of `D_Sg`, after dividing out `2πn²`, is exactly

`R_(S,n)=∑_(m∣n, gcd(n/m,∏_(p∈S)p)=1)c_m√m`.             (7)

**All-sieve classification.** The flux of `D_Sg` is completely monotone for **every** finite prime set `S` if and only if `c_m≥0` for all `m≥1`. The forward direction chooses `S` to contain every prime divisor of a given `n`; then (7) reduces to `c_n√n`, whose nonnegativity follows from uniqueness of the positive Laplace measure. The reverse direction is immediate from (7). If in addition both source anchors equal those of `k`, then

`0=M₀−M₁/₂=∑_(m≥2)c_m(1−m^(−1/2))`

forces `c_m=0` for `m≥2`, and the mass anchor gives `c₁=1`. Thus **the all-sieve Bernstein cone plus both anchors rigidifies even one-sided integer-shift gauges**.

For (2), take `S={2}` and `n=4`. Equation (7) gives `R_({2},4)=c₄√4=−2κα<0`, so its first prime-deleted flux is not completely monotone. This is the exact property that detects the constructed off-line zero while the undeleted flux remains completely monotone.

## Interpretation and precise limit

The [symmetric divisor Bernstein theorem](theta-divisor-bernstein-gauge-rigidity.md) says complete flux monotonicity plus both anchors forces **every symmetric integer-shift gauge** to equal `k`. Construction (2) shows those same conditions without symmetry allow an off-line zero, despite exact Gaussian integer-rate assembly and right-ray source positivity. The two results identify a structural divide between reflected comparison gauges and one-sided chronological gauges; the all-sieve property below is an alternative discriminator. This is a source countermodel, **not** a counterexample to RH, since `g_α≠k` and is not even.

The actual Euler-deletion chronology is one-sided and gains its reflection only at singular completion, where the half-charge escapes through the negative cusp. A successful proof must transport arithmetic positivity through that reflection-creating completion in a way that controls the **complex** Mellin family. The present example proves that keeping the two scalar anchors and the undeleted positive rate measure before that transport does not suffice. The all-sieve classification in this card concerns only shifts `+log m` with integer `m`; the [seed-projector theorem](theta-all-sieve-seed-projector-translation-cone.md) classifies arbitrary real translation mixtures and gives a positive two-sided asymmetric source whose deleted fluxes are all completely monotone yet whose Mellin transform has an off-line zero. Literature novelty and Lean formalization remain open.
