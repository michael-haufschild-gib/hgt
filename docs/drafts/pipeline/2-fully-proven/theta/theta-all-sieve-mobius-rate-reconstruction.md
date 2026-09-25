# Möbius reconstruction of the all-sieve theta rate cone

- **ID:** `theta-all-sieve-mobius-rate-reconstruction`
- **Stage:** 2-fully-proven (paper)
- **Type:** THEOREM (paper); Lean formalization pending
- **Routes:** STC, CSB, U, MPLF, RG-HF, RHist
- **Status:** `[PROVED HERE ON PAPER] [NOT AN RH PROOF]`
- **Dependencies:** the exact theta Gaussian-rate flux and prime-shift law in [theta-prime-deletion-spectral-escape](theta-prime-deletion-spectral-escape.md), and finite Bernstein--Widder/Laplace uniqueness in the Lean corpus. No numerical computation is used.

## Exact rate-measure classification

For a positive Borel measure `ν` on `(0,∞)`, define prime-scale transport

```text
A_n ν = n² · (λ ↦ n²λ)_*ν,
D_S ν = ∏_(p∈S)(I−A_p)ν                         (S finite).     (1)
```

Assume `ν` has a **positive rate gap**: its support is contained in `[λ₀,∞)` for some `λ₀>0`, and `∫e^(−tλ)dν(λ)<∞` for every `t>0`. Then the following are equivalent:

1. `D_Sν` is positive for every finite prime set `S`.
2. There is a **unique positive** rate measure `ξ`, supported in `[λ₀,∞)`, such that

   ```text
   ν = Σ_(n≥1) A_n ξ.                                      (2)
   ```

The sum is locally finite in the rate variable. The seed is recovered *exactly on each bounded rate window* by cofinal deletion: for `R≥λ₀`, once `S` contains every prime at most `sqrt(R/λ₀)`,

```text
(D_Sν)|_[λ₀,R] = ξ|_[λ₀,R].                               (3)
```

In particular there is no residual at rate zero or noncompact harmonic component in this gapped class. Positivity along one increasing cofinal prime exhaustion suffices for (1), because every bounded rate window stabilizes at finite depth.

## Proof

Prime dilations commute and `A_mA_n=A_(mn)`. The rate gap makes all sums below locally finite: on `[λ₀,R]`, `A_nν` vanishes for `n>sqrt(R/λ₀)`. Define the *local Möbius inverse*

```text
ξ = Σ_(n≥1) μ(n)A_nν,                                     (4)
```

where `μ` is the ordinary Möbius function. Fix `R` and let `S` contain all primes not exceeding `sqrt(R/λ₀)`. On `[λ₀,R]`, every nonzero term of (4) is squarefree and has all its prime factors in `S`; hence (4) equals the finite inclusion--exclusion measure `D_Sν` there. Assumption (1) makes `ξ` positive on every bounded rate window, therefore globally positive. The same identity proves (3), including for larger `S`, since no newly deleted prime can land inside the fixed window.

Dirichlet convolution now gives, as an identity of locally finite measures,

```text
Σ_(m≥1) A_mξ
 = Σ_(k≥1) A_kν · Σ_(n|k) μ(n)
 = ν.                                                       (5)
```

This proves existence. Conversely, substitute (2) in `D_Sν` and cancel indices divisible by a prime in `S`:

```text
D_Sν = Σ_(n≥1, gcd(n,∏S)=1) A_nξ ≥ 0.                    (6)
```

Equation (3) recovers `ξ` from `ν`, proving uniqueness. The Laplace integrals of (2) converge: because `λ≥λ₀`, the Gaussian factor `e^(−tn²λ)` dominates `n²` uniformly after reserving half of `e^(−tλ)` for integrability of `ξ`; also `ξ≤ν` follows locally from (3).

## Beyond a rate gap: the strict critical-moment wall

The same equivalence and uniqueness hold **without a gap** if, for some `q>3/2`,

```text
M_q(ν):=∫_(0,∞) λ^(−q)dν(λ)<∞.                          (W1)
```

In this class the series (2) and (4) converge absolutely on every compact rate window, rather than being locally finite. For `E⊆[a,b]`, `0<a≤b<∞`, positivity gives the bound

```text
(A_nν)(E) ≤ n²ν((0,b/n²]) ≤ b^q M_q(ν)n^(2−2q).       (W2)
```

Because `2q−2>1`, the right side is summable in `n`. Thus the finite-deletion inclusion--exclusion measures converge on every compact window to the signed Möbius series `ξ` in (4). If all `D_Sν` are positive, their limit `ξ` is positive. Double-series inversion is also absolutely justified: by (W2), the total variation on `E` of its terms is bounded by

```text
b^q M_q(ν)·(Σ_(m≥1)m^(2−2q))·(Σ_(n≥1)|μ(n)|n^(2−2q))<∞.
```

Hence the divisor identity still proves (5). Conversely, for any positive `ξ` satisfying (W1), the Euler sum (2) has

```text
M_q(ν)=(Σ_(n≥1)n^(2−2q))M_q(ξ)<∞,                    (W3)
```

and (6) proves every deletion positive. The cofinal deleted measures converge to `ξ` on compact rate windows, so it is unique. A finite `M_q` also makes every Laplace transform finite, since `e^(−tλ)≤C_(t,q)λ^(−q)` on `(0,∞)`.

The exponent `3/2` is the exact summability boundary of the Euler dilation weights `n²`: at `q=3/2`, their `q`-mass is the harmonic series. This is a statement about this reconstruction method, not a claim that every measure lacking (W1) has an obstruction. The rate-gap theorem above covers the literal theta rate measure even at orders where its weighted total mass diverges.
For the literal rate measure (2) with seed `ξ=2πδ_π`, `M_q(ν_k)=2π·π^(−q)Σ_(n≥1)n^(2−2q)<∞` for every `q>3/2`, so both reconstruction mechanisms apply to the actual source.

## Source-level consequence

Let `f` be a continuous real source with finite normalized tail flux

```text
b_f(t)=t^(−3/2)∫_[log(t)/2,∞)e^(x/2)f(x)dx.
```

Suppose `b_f` and every finite-prime-deleted flux `b_(D_Sf)` are completely monotone, and the positive Bernstein measure of `b_f` has either a positive rate gap or finite `M_q` for some `q>3/2`. Then `f` is automatically a **positive mixture of translates of the literal completed theta source** `k`:

```text
f(x)=∫_ℝ k(x+s)dη(s),                                    (7)
```

for a unique positive measure `η`; its support is bounded below in the rate-gap case. No translation-mixture premise is imposed on `f`. To see this, Bernstein--Widder and Laplace uniqueness turn the complete-monotonicity tests into (1). Let `ξ` be its unique seed. Under `λ=πe^(2s)`, define `η` as the pushforward of `(2πe^(5s/2))^(−1)dξ(λ)`. The exact theta flux

```text
b_k(t)=2πΣ_(n≥1)n²e^(−πn²t)
```

and the shift law `b_(k(·+s))(t)=e^(5s/2)b_k(e^(2s)t)` turn (2) into the flux of (7). The mixture is pointwise finite and continuous: on compact `s` intervals this follows from local finiteness of `ξ`; as `s→∞` the right Gaussian tail dominates every polynomial in `λ=πe^(2s)`, and as `s→−∞` evenness of `k` gives a left Gaussian tail dominating every inverse power of `λ`. Both tails are controlled by (W1), or by the lower support bound in the gapped case, uniformly on compact `x` intervals. Tonelli gives its flux, and the identity

```text
f(x)=−e^(−x/2) d/dx[e^(3x)b_f(e^(2x))]               (8)
```

shows that the flux determines a continuous source, yielding (7).

If in addition `f` has the same ordinary mass and **both** reflected half-density charges as `k`, then `η=δ₀` and `f=k`. Indeed, positivity and equality of ordinary mass make `η` a probability measure. The two charge equalities give

```text
∫e^(−s/2)dη(s)=∫e^(s/2)dη(s)=1.
```

Their average is `∫cosh(s/2)dη=1`, forcing support at `s=0`. Evenness of `f` plus equality of the positive half-charge supplies the reflected charge automatically. This extends the [all-sieve translation-gauge theorem](theta-all-sieve-seed-projector-translation-cone.md): the translation representation and positivity of its measure are conclusions rather than assumptions.

## Meaning and boundary

The positive rate gap makes prime dilation **proper**: only finitely many arithmetic ancestors can reach a bounded rate window. The strict negative-moment condition (W1) replaces local finiteness by absolute summability. In either case Möbius inversion is a positive-measure reconstruction, not a formal alternating series. Cofinal deletion reads a unique Gaussian seed, and the corresponding all-sieve cone is exactly the positive cone of Euler reconstructions of seeds. The [single-prime pure-ray theorem](theta-prime-deletion-bernstein-pure-ray.md) is a sharper extremality statement for `k` under weaker tests; the present theorem classifies the full finite-sieve cone under either control condition.

This is intrinsically an **all-prime completion** property. A finite smooth-number stage `ν_P=2πΣ_(n:P-smooth)n²δ_(πn²)` has a positive rate gap and survives deletion by primes in `P`, but for any prime `q∉P`, `D_qν_P` has coefficient `−2πq²` at rate `πq²`. Thus no proper finite-prime Euler stage belongs to the all-sieve cone; the full `k` enters it only at the infinite arithmetic completion. The classification does not replace that singular passage by a finite positive approximation.

Some rate-zero control matters. Without a gap or an adequate negative moment, infinitely many dilations of mass near zero can reach the same bounded window, so Möbius inversion need not converge and a harmonic component may remain. The elementary positive rate measure `dλ` illustrates the boundary: `A_p(dλ)=dλ`, so every nonempty deletion is zero although the measure itself is nonzero; its Laplace profile is `1/t` and satisfies neither control condition. This is a rate-space obstruction, not a theta-like finite-mass source.

There is also a **critical-scaling ghost** at precisely the theta flux exponent. For `dν_crit(λ)=λ^(1/2)dλ`, one has `A_pν_crit=p^(−1)ν_crit`, hence

```text
D_Sν_crit = (∏_(p∈S)(1−1/p))ν_crit ≥ 0,
∫e^(−tλ)dν_crit(λ)=Γ(3/2)t^(−3/2).                (9)
```

Along a cofinal prime exhaustion the product tends to zero, so the cofinal deleted measure is zero on every bounded rate window although `ν_crit` is nonzero. Its lack of a rate gap and of (W1) is essential. It is a measure-level model of the critical completion defect, not a finite-tail positive theta source. This shows why the strict `q>3/2` wall is meaningful: at the boundary, all finite deletions can stay positive while seed reconstruction loses the entire measure.

The last qualification is exact. Applying the source-recovery expression (8) to `b(t)=Γ(3/2)t^(−3/2)` gives zero, since `e^(3x)b(e^(2x))` is constant. But a genuine tail flux also requires `e^(3x)b(e^(2x))→0` as `x→+∞`; the ghost has a nonzero constant instead. It is precisely a homogeneous boundary constant of the flux-to-source differential equation, removed by the physical tail condition. No claim is made here that this condition alone classifies every ungapped all-sieve measure.

This classification still does not orient Xi zeros. The literal `k` is a member of the classified cone regardless of where its zeros lie. A proof of RH needs an additional source law that forces off-line zeros to violate a property of `k` itself, rather than only showing that alternative sources leave this cone.

## Formalization gate

- [x] Paper proof of local finite Möbius inversion, positivity and unique Euler reconstruction.
- [x] Paper proof of the absolute weighted reconstruction for every `q>3/2`.
- [x] Paper proof of the positive theta-translation representation and charge rigidity.
- [x] Paper proof that every proper finite smooth-number stage fails an undeclared-prime deletion test.
- [x] Paper counterexample showing why a rate-zero boundary hypothesis cannot simply be dropped.
- [x] Paper critical-scaling ghost with positive finite deletions and zero cofinal seed.
- [ ] Formalize the locally finite and weighted measure incidence theorems and source-flux transfer with targeted Lean checks.
