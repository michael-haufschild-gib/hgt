# Divisor Bernstein cone rigidifies all symmetric integer-scale theta gauges

- **ID:** theta-divisor-bernstein-gauge-rigidity
- **Stage:** 3-formalized
- **Type:** exact arithmetic Laplace-measure classification and infinite gauge rigidity
- **Routes:** STC, CSB, U, K-RVM, MPLF, RHist; source-side comparison with EDQ
- **Status:** [PROVED HERE ON PAPER] [LEAN: `GaloisForLFunctions.RHTower.ThetaDivisorBernsteinGauge`, see `theta-divisor-bernstein-gauge-rigidity-formalized.md`] [NOT AN RH PROOF]
- **Dependencies:** the theta flux and boundary moment in [theta-euler-critical-boundary-mass-escape.md](theta-euler-critical-boundary-mass-escape.md); the finite Bernstein--Widder theorem in [BernsteinWidder.lean](../../../../formal/GaloisForLFunctions/HTGeometry/BernsteinWidder.lean); Laplace-measure uniqueness in [RepairedFrequencyDensityLaplace.lean](../../../../formal/GaloisForLFunctions/HTGeometry/RepairedFrequencyDensityLaplace.lean); elementary Möbius inversion and Euler totient identities. The prime-power special case and its quantitative complex bound are in [theta-prime-power-bernstein-gauge-rigidity.md](theta-prime-power-bernstein-gauge-rigidity.md). No numerical computation is used.

## The source class and exact Bernstein cone

Let `k` be the completed positive even theta source. With `t=exp(2x)`, its critical flux is

`b_k(t)=t^(−3/2)∫_[log(t)/2,∞) exp(y/2)k(y)dy`

`      =2π∑_(r≥1) r² exp(−πr²t)`.                         (1)

Let `(c_n)_(n≥1)` be real and assume

`∑_(n≥2)|c_n|√n<∞`.                                          (2)

Define the symmetric integer-scale gauge

`g(x)=c₁k(x)+∑_(n≥2)c_n[k(x+log n)+k(x−log n)]`.            (3)

This source is even; no sign condition is imposed on `g` or on individual coefficients. Write `b_g` for its flux, defined as in (1). For each denominator `b≥2`, put

`Q_b=∑_(n≥2, b∣n)c_n/√n`,                                    (4)

and for each integer `a≥1`, put

`R_a=c₁+Q₁+∑_(n≥2, n∣a)c_n√n`, where `Q₁=∑_(n≥2)c_n/√n`.   (5)

**Bernstein-cone theorem.** The flux `b_g` is completely monotone on `(0,∞)` **if and only if**

`Q_b≥0` for every `b≥2`, and `R_a≥0` for every `a≥1`.        (6)

In particular its positive Laplace measure has atomic weight

`2π(a/b)² Q_b` at the rate `π(a/b)²` when `a/b` is reduced and `b≥2`,

and weight `2πa² R_a` at the integer rate `πa²`.

## Charge-gap theorem

The ordinary and critical Mellin multipliers of (3) are

`M₀=c₁+2∑_(n≥2)c_n`,

`M₁/₂=c₁+∑_(n≥2)c_n(√n+1/√n)`.                           (7)

Set `Δ=M₁/₂−M₀` and `F(n)=(√n−1)²`. Let `μ` be the ordinary Möbius function and define the divisor Möbius transform

`β(d)=∑_(e∣d) μ(d/e)F(e)`.                                  (8)

Then `β(1)=0`, while for **every** `d>1`,

`β(d)=φ(d)−2 J_(1/2)(d)>0`,                                (9)

where `φ(d)=d∏_(p∣d)(1−1/p)` and `J_(1/2)(d)=√d∏_(p∣d)(1−1/√p)`. The exact divisor-Abel identity is

`Δ=∑_(d≥2) β(d)Q_d`.                                        (10)

Consequently (6) implies `M₁/₂≥M₀`, and equality forces `c_n=0` for every `n≥2`. If `g` has the same ordinary mass and critical half-density charge as `k`, then `M₀=M₁/₂=1`, hence `c₁=1` and **`g=k`**. This remains true for signed coefficients and infinitely many primes and composite scales. It is strictly broader than positive-convolution rigidity and the single-prime valuation law.

## Proof

For the shift `k(x+log n)`, the flux is `n^(−1/2)H_k(x+log n)`, so its normalized Laplace profile is `n^(5/2)b_k(n²t)`. The opposite shift gives `n^(−5/2)b_k(n^(−2)t)`. Thus

`b_g(t)=c₁b_k(t)+∑_(n≥2)c_n[n^(5/2)b_k(n²t)+n^(−5/2)b_k(n^(−2)t)]`. (11)

Because `H_k≤1/2`, `b_k(u)≤u^(−3/2)/2`. Equation (2) makes every sum in (3), (7), and (11) absolutely convergent and gives finite exponentially weighted total variation for the signed atomic measure of (11). Termwise Mellin transformation is valid for `|Re w|≤1/2`.

Collect the atoms of (11) at a positive rational rate `r=a/b` in lowest terms. If `b≥2`, neither the unshifted source nor a positive shift can contribute. A negative shift by `n` contributes exactly when `b∣n`; its rate weight is `2πr² c_n/√n`. Their sum is `2πr² Q_b`. For the integer rate `r=a`, the unshifted contribution is `c₁`, every negative shift contributes `c_n/√n`, and a positive shift by `n` contributes exactly when `n∣a`, with weight `c_n√n`. Their sum is `2πa²R_a`.

Nonnegative weights make (11) a completely monotone Laplace transform. Conversely, if `b_g` is completely monotone, fix `t₀>0` and apply finite Bernstein--Widder to `s↦b_g(t₀+s)`. Its positive representing measure must equal the signed atomic measure from (11) weighted by `exp(−t₀λ)`. To see uniqueness directly, push both finite measures under `λ↦exp(−λ)`: their integer Laplace samples, including the right limit at zero, are all polynomial moments on `[0,1]`, which determine the measure. Undo the strictly positive exponential weight. Every rational rate appears, so all `Q_b` and `R_a` are nonnegative, proving (6).

Put `v_n=c_n/√n`. From (7), `Δ=∑_(n≥2)v_nF(n)`. Möbius inversion of (8) gives `F(n)=∑_(d∣n)β(d)`. Because `β(d)>0` for `d>1` as shown below and `∑|v_n|F(n)<∞` by (2), the double sum is absolutely convergent; exchanging divisor and multiple sums gives (10).

For (9), `F(n)=n−2√n+1`; the divisor Möbius transforms of `n`, `√n`, and `1` are respectively `φ`, `J_(1/2)`, and the point mass at `1`. For `d>1`, factor

`φ(d)/J_(1/2)(d)=∏_(p^e∥d) p^((e−1)/2)(√p+1)>2`.      (12)

Every factor is at least `√2+1>2` for the first prime and greater than one thereafter, so `β(d)>0`.

If `Δ=0` under (6), (10) and (9) give `Q_d=0` for all `d≥2`. These multiple sums determine every `v_n`, `n≥2`. Indeed, absolute convergence follows from `∑n|v_n|<∞`, which is (2), since `τ(r)≤r`; then

`v_n=∑_(k≥1) μ(k)Q_(nk)`

`   =∑_(m: n∣m)v_m∑_(k∣m/n)μ(k)`.                         (13)

The inner divisor sum is one only for `m=n`, and zero otherwise. Thus `v_n=0`, completing the rigidity proof. Equality of the two source moments with those of `k` gives `M₀=M₁/₂=1` because both theta moments are positive.

## Meaning and limit

The source's complete monotonicity is not merely a generic shape property. Under exact Gaussian integer-rate assembly, every reduced rational denominator has one signed **multiple-sum** weight `Q_b`. Positivity of the entire Bernstein measure makes all these arithmetic tails nonnegative. The half-charge mismatch has a strictly positive divisor Möbius transform, so the scalar boundary charge pairs with every denominator tail at once. This converts one scalar equality into an infinite rigidity theorem. On a single prime-power chain, `β(p^j)=F(p^j)−F(p^(j−1))`, recovering the earlier Abel weights; that specialization also yields a uniform complex stability bound. For the full divisor lattice, exact rigidity holds, but a comparable quantitative inversion bound for small positive `Δ` has not been proved.

This theorem does **not** orient the zeros of the unmodified theta source and therefore does not prove RH. It rules out one broad way of inserting new zeros while preserving full flux positivity and both anchors. Dropping reflection while keeping these other conditions breaks this rigidity statement: the [one-sided three-term countermodel](theta-one-sided-bernstein-two-anchor-offline-zero.md) retains the positive Gaussian-rate measure and both anchors yet forces an off-line Mellin zero. Its complete finite-sieve flux positivity fails. Even restoring **all** finite-sieve flux positivity without reflection is insufficient for arbitrary translation gauges, as the positive [seed-projector countermodel](theta-all-sieve-seed-projector-translation-cone.md) shows. Literal finite Euler stages and prime deletion are also one-sided and exhibit boundary-mass escape; they do not satisfy (3). The next source question is whether an arithmetic Bernstein cone can be carried through those actual chronological completions into a complex connection estimate, rather than applied only to regular comparison gauges. Literature novelty remains open; the combined theorem is formalized in Lean.

## Log
- 2026-09-27 — Bernstein cone (6) with rate weights, flux (11), divisor Möbius weights (8)–(9), (12), the divisor-Abel identity (10), multiple-sum inversion (13), charge monotonicity, equality case and two-anchor rigidity formalized unconditionally; moved to 3-formalized.
