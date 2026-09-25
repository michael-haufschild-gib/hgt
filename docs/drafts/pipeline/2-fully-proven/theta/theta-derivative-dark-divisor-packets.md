# Positive theta deformations with an exact invisible off-line divisor packet

- **ID:** `theta-derivative-dark-divisor-packets`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper); Lean formalization pending
- **Route:** source-side boundary for STC, CSB, U, K-RVM, and MPLF
- **Status:** `[PROVED HERE ON PAPER] [NOT AN RH PROOF]`

## Theorem

Let `k(x) = thetaCuspFullSource(x)` in the corpus normalization, so that
`F(z) = ∫_ℝ exp(−izx) k(x) dx = XiC(z)`. For every integer `m ≥ 1`, put `r = 4m` and

```text
k_t(x) = k(x) + t k⁽ʳ⁾(x),                  t > 0.
```

There is `ε_m > 0` such that, for every `0 < t < ε_m`:

1. `k_t` is strictly positive, even, globally strongly log-concave, Schwartz, and has every
   exponential moment. Moreover `k_t → k` in Schwartz topology as `t ↓ 0`, and every fixed
   exponentially weighted derivative seminorm of `k_t−k` tends to zero.
2. `∫_ℝ x^j k_t(x) dx = ∫_ℝ x^j k(x) dx` for every integer `0 ≤ j < r`, whereas
   `∫_ℝ x^r(k_t−k)(x) dx = t r! ∫_ℝ k(x) dx > 0`.
3. For every `z ∈ ℂ`, `F_t(z) = ∫_ℝ exp(−izx) k_t(x) dx = XiC(z)(1+t z^r)`.
4. For every real `z`, `1+t z^r > 0`: `F_t` and `XiC` have the same real zeros, with the
   same multiplicities and sign pattern. Yet `F_t` has the additional nonreal zero packet
   `t^(−1/r) exp((2j+1)πi/r)`, `j=0,…,r−1`, counted with multiplicity. These roots avoid
   both real and imaginary axes, respect conjugation and sign symmetries, and escape to
   infinity as `t ↓ 0`. The total zero counts of `F_t` and `XiC` differ by at most
   `r`, so every leading zero-count asymptotic is unchanged.
5. The perturbation is large in the first-atom *relative* tail coordinate:
   `(k_t(x)−k(x))/k(x) ~ t(2π exp(2x))^r → +∞` as `x→+∞` for fixed `t>0`.

Consequently, for every prescribed finite moment depth `J` and every Schwartz neighborhood
of the literal theta source, a strictly positive even source in that neighborhood has the
same moments through `J` and the same complete real-zero divisor, but has nonreal zeros.
The assertion holds whether or not RH itself is true.

## Compact-tail strengthening

For every `J` and every Schwartz neighborhood of `k`, there is a strictly positive,
even, globally strongly log-concave smooth source `g` in that neighborhood such that

```text
g(x) = k(x) outside a compact interval,
∫ x^j g(x) dx = ∫ x^j k(x) dx     (0 ≤ j ≤ J),
the entire Fourier transform of g has a nonreal zero.
```

Thus even **exact equality with the literal theta source on both tails**,
combined with strong log-concavity and any finite set of moment identities,
cannot force a real divisor. This strengthening does not assert preservation
of the complete real-zero divisor.

To prove it, choose `r=4m>J` and `t>0` small enough for the theorem above.
Choose an even smooth cutoff `χ_R` equal to one on `[-R,R]`, zero outside
`[-R−1,R+1]`, and between zero and one everywhere, with uniformly bounded
derivatives of each fixed order. Interpolate *log densities*:

```text
b_R = exp((1−χ_R)log k + χ_R log k_t).
```

Thus `b_R=k_t` inside `[-R,R]` and `b_R=k` outside `[-R−1,R+1]`. On each
transition interval, put `L=log k_t−log k`. The first-atom expansions in the
proof below give, for fixed `t>0` and `x→+∞`,
`L(x)=2r x+O_t(1)`, `L'(x)=2r+o(1)`, `L''(x)=o(1)`, whereas both
`(log k)''` and `(log k_t)''` equal `−4π exp(2x)+O_t(1)`.
Consequently

```text
(log b_R)'' = (1−χ_R)(log k)'' + χ_R(log k_t)''
               + 2χ_R'L' + χ_R''L
             = −4π exp(2x) + O_t(R)
```

on the positive transition interval. The negative one follows by evenness.
For large `R` the curvature is uniformly negative; inside and outside the
transition it inherits the strong log-concavity of `k_t` and `k`.
The same first-atom bounds give `b_R→k_t` in every Schwartz seminorm and in
every exponentially weighted `L¹` norm: on the moving transition the
first-atom formulas and product differentiation bound each fixed derivative by
`C_{s,t}(1+R)^{N_s}(1+q)^{N_{s,r}}exp(−q/2)`, with `q=πexp(2|x|)` and fixed
integers `N_s,N_{s,r}`. This dominates every polynomial or exponential weight
as `R→∞`; elsewhere the difference is a tail of `k_t−k`. Hence the moments
through `J` of `b_R−k` tend to zero, but need not vanish exactly.

Fix a nonnegative even `C∞` bump `ψ`, supported in a fixed small central
interval and positive on an open interval. Let `N=⌊J/2⌋` and
`ψ_ℓ(x)=x^(2ℓ)ψ(x)` for `0≤ℓ≤N`. The matrix
`H_{iℓ}=∫x^(2(i+ℓ))ψ(x)dx` is positive definite: its quadratic form is
`∫(Σ_i v_i x^(2i))²ψ(x)dx>0` for every nonzero vector `v`, because a
nonzero polynomial cannot vanish on that open interval. Hence it is
invertible. Write `d_i(R)=∫x^(2i)(b_R−k)(x)dx` and choose the unique coefficients
`c(R)=−H⁻¹d(R)`, which tend to zero. Then

```text
g_R = b_R + Σ_{ℓ=0}^N c_ℓ(R) ψ_ℓ
```

has all even moments through `J` exactly equal to those of `k`; odd moments
agree by evenness. Outside `[-R−1,R+1]`, `g_R=k`. On the fixed bump support,
`b_R=k_t` for large `R`; because `c(R)→0`, the correction tends to zero in
`C²` there. Strict positivity and the uniform negative logarithmic curvature
of `k_t` therefore persist on that support. Elsewhere `g_R=b_R`, whose
positivity and global strong log-concavity were established above.

The entire Fourier transforms of `g_R` converge uniformly on each compact
complex set to `F_t=XiC(1+t z^r)`, by the exponential `L¹` convergence.
Take a small closed disk around one nonreal root of `1+t z^r`, disjoint from
the real axis and with no `F_t` zero on its boundary. Rouché's theorem gives
a nonreal zero of the transform of `g_R` in that disk for all sufficiently
large `R`. Finally choose `t` small to enter the prescribed Schwartz
neighborhood, then `R` large enough for the stated properties. This completes
the strengthening without a numerical experiment.

## Proof

The corpus proves `k(x)>0` on all of `ℝ` (`thetaCuspFullSource_pos_all`), its evenness
(`thetaCuspFullSource_neg`), its Schwartz regularity (`thetaCuspSchwartz`), and an
exponential bound for *every* derivative at *every* real rate
(`thetaCuspFullSource_derivative_exp_bound`). In particular `k⁽ʳ⁾` is even and Schwartz,
and both terms have every exponential moment.

It remains to prove positivity uniformly over the noncompact line. On the positive ray,
write the first atom as

```text
f₁(x) = exp(x/2) P₀(exp x) exp(−π exp(2x)),
P₀(y) = 4π²y⁴ − 6πy².
```

The exact source polynomial recursion is

```text
Pₙ₊₁(y) = (1/2)Pₙ(y) + yPₙ'(y) − 2πy²Pₙ(y).
```

Induction gives `deg Pₙ = 4+2n` and leading coefficient
`4π²(−2π)^n`. For `r=4m`, `P_r(y)>0` for all sufficiently large `y`, and
`f₁⁽ʳ⁾(x)/f₁(x) ~ (2π)^r exp(2rx) → +∞`. The corpus's all-order first-atom theorem
`thetaCuspFullSource_derivative_relative_error_scaled_tendsto_zero` at scale power zero
says `(k⁽ʳ⁾−f₁⁽ʳ⁾)/f₁ → 0`. Hence `k⁽ʳ⁾(x)>0` for all sufficiently large positive `x`.
Evenness gives the same on the negative tail. On the remaining compact interval, `k`
has a positive minimum and `k⁽ʳ⁾` is bounded; choosing `t>0` small makes
`k+t k⁽ʳ⁾>0` there too. Schwartz and exponentially weighted derivative convergence
follow by linearity and the all-rate bounds.

Here is the stronger curvature assertion in (1). Put `q=π exp(2x)` and, on the
positive tail, `a=k⁽ʳ⁾/k`. The polynomial formula and the all-order first-atom
error for derivatives through `r+2` give, with the same asymptotics after two
logarithmic derivatives,

```text
a = (2q)^r(1+O(q⁻¹)),     a''/a = (2r)²+O(q⁻¹),
(log k)'' = −4q+O(q⁻¹).                                  (†)
```

To see that the error control in `(†)` includes derivatives, express `a'` and
`a''` rationally in `k,…,k⁽ʳ⁺²⁾`; each `k⁽ʲ⁾/k` differs from the corresponding
first-atom rational function `P_j(exp x)/P₀(exp x)` by less than any prescribed
negative power of `q`, after choosing the scale in the corpus's theorem large
enough. The leading rational term is `(2q)^r`, whose first two logarithmic
derivatives yield `2r` and `(2r)²`. Likewise
`log f₁ = x/2+log P₀(exp x)−q`, with `P₀(exp x)=4q²(1−3/(2q))`,
gives its displayed curvature. (The harmless constant in `P₀=4q²(1−3/(2q))`
uses `q=πexp(2x)`.)

For all sufficiently large `x`, `a>0`, `a''/a` has a fixed upper bound `C_r`,
and `(log k)''<−C_r−1`. Since

```text
(log k_t)'' = (log k)'' + t a''/(1+t a) − (t a')²/(1+t a)²
              ≤ (log k)'' + max(0,a''/a) < −1,
```

the positive-tail curvature bound holds uniformly for every `t>0`. Evenness
handles the negative tail. On the intervening compact interval, the corpus's
strict global log-concavity numerator theorem
`thetaCuspLogConcavityNumerator_neg_all` and `k>0` give a uniform negative
curvature bound for `k`; continuity in `(x,t)` transfers a negative bound to
`k_t` when `t` is sufficiently small. Combining the compact and tail bounds
gives `(log k_t)''≤−δ_m<0` on all of `ℝ`.

For (2), integrate by parts `r` times. Every boundary term vanishes because the
corpus's exponential derivative bounds dominate every polynomial:

```text
∫ x^j k⁽ʳ⁾(x) dx = (−1)^r ∫ (d^r/dx^r)x^j · k(x) dx.
```

This is zero for `j<r`, and equals `r!∫k` for `j=r` since `r` is even. For (3),
the same integration by parts works for every complex `z`, since every derivative
has exponential decay faster than `exp(|Im z|·|x|)`:

```text
∫ exp(−izx) k⁽ʳ⁾(x) dx = (iz)^r F(z) = z^r F(z).
```

The corpus's real Fourier identity `fourier_thetaCuspSchwartz_scaled` and the
entire continuation identify `F=XiC` on `ℂ`. Finally `1+t z^{4m}` is strictly
positive on `ℝ`, and its listed roots solve `z^{4m}=−1/t`. None is real or
purely imaginary because an odd multiple of `π/(4m)` cannot be an integer multiple
of `π/2`. Multiplication by this polynomial adds its zeros, even if a root is
already a Xi zero. This proves (4) and the neighborhood assertion.

## Exact information loss and surviving route

The added packet has reciprocal power sums

```text
Σ α⁻ℓ = 0                  (1 ≤ ℓ < r),
Σ α⁻ʳ = −r t.
```

There is also an exact detection scale: on `|z|≤R`, the relative transform
factor obeys `|F_t(z)/XiC(z)−1|≤tR^r` wherever `XiC(z)≠0`, whereas each added
root has `|z|=t^(−1/r)`. Fixed compact spectral tests therefore see a vanishing
perturbation as `t↓0`; order-one detection must move to radius comparable to
`t^(−1/r)`.

Equivalently, `log(F_t/F)=log(1+t z^r)` has a zero Taylor jet through degree
`r−1`. In the squared spectral coordinate `w=z²`, its factor is `1+t w^{2m}`.
Thus every fixed finite source-moment or local logarithmic-divisor test misses
an *exact* off-line packet, even when the tested source is arbitrarily close to
the literal positive, strongly log-concave theta source and the entire real zero
divisor is supplied.
This rules out only arguments that use those data alone. The deformed source
does **not** satisfy the literal modular/Euler identity. A surviving RH proof
must use an all-scale arithmetic coherence condition that distinguishes `k`
from these differential deformations; merely increasing a fixed moment depth
cannot do so. Point (5), proved by the same first-atom asymptotic used above,
shows that first-atom relative normalization detects the **exact differential
packet**. The compact-tail strengthening proves that tail normalization by
itself is still insufficient: one can keep the literal tails unchanged and
implant a nonreal zero. The surviving producer must link those tails to the
interior through an exact global arithmetic law. The packet's escape to
infinity explains why compact spectral convergence sees no contradiction.

The companion [tail-capacity theorem](theta-tail-divisor-capacity-threshold.md)
sharpens this distinction: a nonzero perturbation preserving the *complete*
Xi divisor cannot decay as `exp(−a exp(b|x|))` for any `b>2`, while these
derivative packets attain the boundary `b=2`. The critical exponent follows
from angular Jensen growth and the full Riemann–von Mangoldt zero density;
it is independent of whether those zeros lie on the critical line.

## Spectral-infinity boundary theorem

Let `𝓔` be the real even smooth functions whose derivatives have every
exponential decay rate, with seminorms
`p_{A,n}(f)=sup_x exp(A|x|)|f⁽ⁿ⁾(x)|` for `A,n≥0`. Let `𝓗` be the
members of `𝓔` whose entire Fourier transforms have only real zeros.
The theorem gives `k_t∈𝓔\𝓗` for every sufficiently small `t>0`, while

```text
p_{A,n}(k_t−k) = t p_{A,n}(k⁽ʳ⁾) → 0
```

for every fixed seminorm. Thus `k` belongs to the closure of `𝓔\𝓗`;
if RH is true, it lies on the boundary of `𝓗` in this source topology.
The same statement holds relative to the positive, even, globally strongly
log-concave source class because every `k_t` stays in that class.

More operationally, if finitely many real-valued source statistics `C_i`
are continuous at `k` in this topology and satisfy strict inequalities
`C_i(k)>0`, then all those inequalities also hold for some `k_t∉𝓗`.
No collection of such **strict, continuous ambient-source margins alone**
can certify real-rootedness of the literal source. A surviving producer must
use a boundary equality, a nonuniform/cofinal or singular observation, or
an exact arithmetic membership law that excludes the deformations. This is
only a necessary design constraint; it supplies none of those producers.

The elementary Fourier and polynomial steps are classical. The source-specific
positive deformation and exact preserved real divisor were not found in the
current corpus search; that does not establish external publication novelty.

## Formalization gate

- [x] Dependency-closed paper proof using named corpus inputs.
- [x] Formalize all-order derivative-polynomial degree, leading coefficient, and
      positive fourth-multiple ratio at infinity in `RHTower.ThetaCuspDerivativeLeadingSign`.
- [x] Formalize eventual positivity of the full `k⁽⁴ᵐ⁾` on both tails from the
      first-atom error theorem in `RHTower.ThetaCuspDerivativeTailPositivity`.
- [ ] Formalize global small-`t` positivity and strong log-concavity, moment cancellation,
      and entire Fourier factor.
- [ ] Formalize the additional divisor packet as one closed Lean theorem; audit only new modules.
- [ ] Formalize the compact-tail strengthening and its finite-moment correction.

Both new leaf files pass direct `lake env lean` checks and are wired into the umbrella.
The leading-sign leaf's targeted build passed. A targeted build of the tail-positivity
leaf is pending: its dependency graph launched many stale module rebuilds concurrently,
so it was interrupted to avoid memory exhaustion; no Lean process was left running.
