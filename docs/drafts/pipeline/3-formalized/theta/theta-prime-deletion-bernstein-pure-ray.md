# The completed theta source is a pure ray of the prime-deletion Bernstein cone

- **ID:** `theta-prime-deletion-bernstein-pure-ray`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean: `GaloisForLFunctions.RHTower.ThetaPrimeDeletionBernsteinPureRay`)
- **Routes:** STC, CSB, U, MPLF, RG-HF, RHist
- **Status:** `[PROVED HERE ON PAPER] [NOT AN RH PROOF]`
- **Dependencies:** literal Gaussian-rate expansion and prime deletion from [theta-prime-deletion-spectral-escape](theta-prime-deletion-spectral-escape.md); finite Bernstein--Widder and Laplace-measure uniqueness available in the Lean corpus. No numerical computation is used.

## The source cone and theorem

Let `b_f(t)=t^(−3/2)∫_[log(t)/2,∞)e^(x/2)f(x)dx`, whenever this tail is finite, and let `D_p f=f-p^(−1/2)f(·+log p)`. Consider the cone `C` of continuous real sources `f` for which `b_f` and **each single-prime-deleted flux** `b_(D_p f)` are completely monotone on `(0,∞)`. The literal completed theta source `k` belongs to `C`.

**Pure-ray theorem.** If `f₁,f₂∈C` and `k=f₁+f₂`, then for some `c∈[0,1]`,

```text
f₁=c k,                    f₂=(1−c)k.                     (1)
```

Thus `k` is an extreme ray of the entire source cone `C`, without assuming that either summand is a translation mixture of `k`, even, positive as a function, or has prescribed mass or critical charge. All finite-prime-deletion conditions are unnecessary for this result: the undeleted and individual-prime Bernstein conditions suffice.

## Proof

The literal source has Gaussian-rate representation

```text
b_k(t)=∫e^(−λt)dν_k(λ),
ν_k=2πΣ_(n≥1)n²δ_(πn²).                                   (2)
```

Bernstein--Widder gives positive Laplace measures `ν₁,ν₂` for `b_(f₁),b_(f₂)`. Although these measures need not have finite total mass, multiplying by `e^(−t₀λ)` for any `t₀>0` makes them finite. Since `b_(f₁)+b_(f₂)=b_k`, uniqueness of finite Laplace measures after that shift gives `ν₁+ν₂=ν_k`. In particular each `νᵢ` is supported on the rates `πn²`, with weights `a_n^i≥0` satisfying

```text
a_n^1+a_n^2=2πn².                                        (3)
```

The exact translation law is `b_(T_(log p) f)(t)=p^(5/2)b_f(p²t)`. Hence

```text
b_(D_p fᵢ)(t)=b_(fᵢ)(t)−p²b_(fᵢ)(p²t).                    (4)
```

Its signed Laplace measure is `νᵢ−p²(scale_(p²))_*νᵢ`; after a positive exponential weight it is finite. Positivity of `b_(D_p fᵢ)` and Laplace uniqueness make this measure positive. At the rate `πn²` with `p|n`, its coefficient is therefore

```text
a_n^i−p²a_(n/p)^i ≥ 0.                                   (5)
```

But adding (5) for `i=1,2` and using (3) gives **zero**, because
`2πn²−p²·2π(n/p)²=0`. Thus equality holds in (5) for each summand, every prime `p`, and every `n` divisible by `p`. Repeatedly divide `n` by its prime factors to obtain `a_n^i=n²a_1^i`. Put `c=a_1^1/(2π)∈[0,1]`. Then (2)--(3) imply `b_(f₁)=c b_k` and `b_(f₂)=(1−c)b_k`.

The flux determines its continuous source: differentiating the tail identity gives

```text
f(x)=−e^(−x/2) d/dx [e^(3x)b_f(e^(2x))].                (6)
```

Apply (6) to finish (1).

## Sharpness: every prime is needed

No finite set of deletion tests makes `k` extreme. Given a finite prime set `P`, choose a prime `q∉P` and put `T_q k(x)=k(x+log q)`. The two nonproportional sources

```text
f₁=(1/2)k+(1/(4√q))T_q k,
f₂=(1/2)k−(1/(4√q))T_q k                         (7)
```

sum to `k`. In their undeleted Gaussian-rate measures, each coefficient is positive: it is `1/2` of theta's at `q∤n`, and respectively `3/4` and `1/4` of theta's at `q|n`. For each `p∈P`, multiplication by `p` preserves whether `q` divides `n`, so deletion simply removes the `p`-divisible rates and leaves nonnegative coefficients. Both sources therefore pass all specified finite tests, but fail the full pure-ray conclusion. The full family of primes is logically essential.

## Reinterpretation and exact limit

At every rate divisible by `p`, the literal deleted rate measure has **zero** weight. Positivity of two proposed components and their sum makes both components saturate that same zero face. Repeating this complementary-slackness argument over all primes forces the original `n²` Euler weights. Thus prime deletion does more than recover a hidden seed: it makes the actual theta source *pure* in a natural arithmetic Bernstein cone.

The [Möbius rate-reconstruction theorem](theta-all-sieve-mobius-rate-reconstruction.md) classifies the stronger all-finite-deletion cone under a rate gap or strict inverse-rate moment. The present extreme-ray proof needs only individual-prime tests and no such assumption on arbitrary summands: domination by `k` supplies their rate gap automatically.

This purity is not RH. A Fourier zero, whether on or off the critical line, does not by itself split `k` into two members of `C`. The [causal rate-tomography theorem](../../2-fully-proven/theta/theta-sieve-zero-division-rate-tomography.md) shows the opposite for finite rational zero-division directions: their Gaussian-rate densities change sign and leave `C` at deep prime deletions. A proof using this cone must derive a genuinely new off-line-only positive decomposition or a separate source law prohibiting positive exponential type; purity alone supplies neither.

## Formalization gate

- [x] Paper proof of positive rate-measure domination from a cone decomposition.
- [x] Paper proof that the prime-divisible zero faces force every Euler coefficient.
- [x] Paper proof that the normalized tail flux is source-injective.
- [x] Paper counterexample showing no finite list of prime tests suffices.
- [x] Formalized: atomic measure argument, source injectivity, pure ray and finite-test sharpness (certificate `theta-prime-deletion-bernstein-pure-ray-formalized.md`).

## Log
- 2026-09-27 — formalized unconditionally (`ThetaCriticalFluxBernstein`, `ThetaPrimeDeletionBernsteinPureRay`); moved to 3-formalized.
