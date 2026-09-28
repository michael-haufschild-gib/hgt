# RH as endpoint harmonic completeness for the literal theta measure

- **ID:** `theta-endpoint-harmonic-completeness`
- **Stage:** 2-fully-proven (paper)
- **Type:** THEOREM (paper); Lean formalization pending
- **Routes:** STC, CSB, U, RG, K-RVM, MPLF, RG-HF, RHist; source-side reinterpretation
- **Status:** `[PROVED HERE ON PAPER] [NOT AN RH PROOF]`

## Statement

Let `k=thetaCuspFullSource>0`, `F=XiC=Fourier(k)` with convention
`F(z)=∫ exp(−izx)k(x)dx`, and let `dμ(x)=k(x)dx`. For each positive real
zero `γ` of `F`, write `m(γ)` for its multiplicity. Define the even real
functions

```text
φ_{γ,j}(x) = (∂/∂t)^j cos(tx) |_{t=γ},    0≤j<m(γ),
```

and let `V` be their real linear span. Every `φ_{γ,j}` belongs to
`L^p_even(μ)` for every finite `p≥1`, because `k` has every exponential
moment. Each also has zero `μ`-mean, since its mean is `F⁽ʲ⁾(γ)=0`.

Then the following are equivalent:

```text
(i)  RH: every zero of F is real;
(ii) closure_{L¹_even(μ)} span({1}∪V) = L¹_even(μ);
(iii) closure_{L¹_even(μ)} V = {h∈L¹_even(μ): ∫h dμ=0}.
```

The Banach endpoint is sharp. **Unconditionally**, for each finite
`p>1`, the closure of `span({1}∪V)` has **infinite codimension** in
`L^p_even(μ)`, even if RH is true. Explicit linearly independent
annihilators work simultaneously for all such `p`:

```text
f_{4m}(x)=k⁽⁴ᵐ⁾(x)/k(x) ∈ ⋂_{1≤q<∞} L^q_even(μ),   m≥1,
∫ f_{4m} dμ=0,
∫ f_{4m} φ_{γ,j} dμ=0       for every γ and 0≤j<m(γ).
```

This is a weighted real-frequency spectral-synthesis formulation. The
`L¹` norm is essential: replacing it by a Hilbert norm creates an
unconditional infinite-dimensional annihilator, regardless of where
Xi's zeros lie.

There is an exact defect index. Let `M` be the sum of multiplicities
of zeros `α` of `F` in the open first quadrant
`Re α>0, Im α>0`, counting one representative per symmetry quartet.
Then, with `∞` allowed,

```text
codim_{L¹_even(μ)} closure(span({1}∪V)) = 2M.       (1)
```

Thus RH is the zero-defect case. A finite collection of off-line
quartets contributes exactly two real bounded source directions per
copy; infinitely many quartets give infinite codimension. The factor
two is the real and imaginary part of a complex zero-division source.

## Proof of the `L¹` equivalence

The dual of real `L¹_even(μ)` is real `L∞_even(μ)`; use the bounded
projection `f(x)↦(f(x)+f(−x))/2` to identify the even dual. If a bounded
even `f` annihilates `V`, put `u=kf` and
`H(z)=∫ exp(−izx)u(x)dx`. Then `u` is real and even, `|u|≤Ck`, and

```text
H⁽ʲ⁾(γ)=∫ f(x)φ_{γ,j}(x)dμ(x)=0.
```

Indeed, since `u` is even,
`H(t)=∫u(x)cos(tx)dx` for real `t`, and differentiating this real
identity gives the displayed equality exactly. Thus `H` contains every
real zero of `F` to at least its full multiplicity. Under RH these are
all zeros of `F`. The
[relative-source rigidity theorem](theta-tail-divisor-capacity-threshold.md)
then gives `u=ck`, hence `f=c` almost everywhere. Therefore the
annihilator of `V` in `L∞_even(μ)` is exactly the constants, proving
`(i)⇒(iii)` by Hahn–Banach. Adding `1` kills that constant, giving
`(i)⇒(ii)`.

For the converse, suppose `F(α)=0` at a nonreal `α`. Define the complex
one-sided zero-division source

```text
g_α(x)=α∫₀∞ sin(αt)k(|x|+t)dt.
```

The proof of the
[real zero-division formula](../../3-formalized/theta/theta-positive-real-zero-division.md)
extends to complex `α`: absolute convergence follows from theta's
double-exponential tail, and the even join is smooth because
`g_α'(0+) = −α²F(α)/2=0`. The global equation
`g_α''+α²g_α=α²k` implies its entire Fourier transform is

```text
G_α(z)=F(z)/(1−z²/α²).
```

This source is bounded relative to `k`. Indeed, on the positive tail,
the literal first-atom slope gives
`k(x+t)≤k(x) exp(−c exp(2x)t)`. Since
`|sin(αt)|≤exp(|Im α|t)`, the ratio `|g_α(x)|/k(x)` is
`O(exp(−2x))`; evenness handles the negative tail, and continuity
handles the compact middle.

Set `u=Re(g_α)−k` and `f=u/k`. Then `f` is real, even, bounded,
and nonzero, while its transform is

```text
H(z)=F(z) [ ½/(1−z²/α²) + ½/(1−z²/conj(α)²) − 1 ].
```

All apparent poles are removable because `F` vanishes at their
locations. The bracket is a nonconstant rational function, so `u≠0`.
At every real zero it is holomorphic, so `H` retains that zero with
full multiplicity. Also `H(0)=0`, since each division factor is `1`
there. Therefore `f` annihilates `V` and `1`, contradicting either
`(ii)` or `(iii)`. This proves both converses.

The same argument works if an off-line zero has multiplicity greater
than one: division removes only one copy at its conjugate-symmetric
pair, and every real zero remains untouched.

## Exact finite-defect classification

Suppose the off-line quartets are finite, with total first-quadrant
multiplicity `M`. Positivity of `k` implies `F(iy)>0` for every real
`y`, so there are no zeros on the imaginary axis. Let `P` be the real
even polynomial normalized by `P(0)=1` whose zeros, with full
multiplicity, are exactly the off-line zeros of `F`. Thus `deg P=4M`.

Let `u=kf` for a real even `f∈L∞(μ)` annihilating `V`, and put
`H=Fourier(u)`. Since `H` contains the full real divisor of `F`,

```text
E(z)=P(z)H(z)/F(z)
```

is entire, even and real on the real axis. The proof of
[relative-source rigidity](theta-tail-divisor-capacity-threshold.md)
applies to `E` with only polynomial changes: the angular Jensen
`R log R` terms for `H` and `F` cancel, so `E` has `O(R)` zeros and
finite exponential type. On the imaginary axis,
`|E(iy)|≤C|P(iy)|`. On rays tending to that axis through the
right zeta half-plane, completed-gamma/Stirling comparison gives

```text
h_E(−π/2+δ) ≤ ½[cosδ log(cosδ)+δ sinδ] = O(δ²).
```

The indicator diagram of even finite-type `E` is centrally symmetric.
Its polynomial growth on both imaginary rays pins that diagram to the
real axis; the quadratic angular upper bound then collapses its real
segment to `{0}`. Thus `E` has minimal exponential type. Rotate the
plane so that the imaginary axis becomes real. Dividing in the upper
half-plane by `(w+i)^{4M}` and in the lower half-plane by
`(w−i)^{4M}` makes bounded boundary functions. The minimal-type
Phragmén–Lindelöf principle bounds each quotient in its half-plane.
Hence `E(z)=O((1+|z|)^{4M})` globally, and generalized Liouville
shows `E` is a real even polynomial of degree at most `4M`.

Conversely, every such polynomial `E` occurs. The proper-part
decomposition of `E/P` is a real combination of the fractions

```text
1/(1−z²/α²)^j  and  1/(1−z²/conj(α)²)^j,
       1≤j≤m(α),
```

plus a real constant. Repeated application of the one-sided operator
`T_α h(x)=α∫₀∞sin(αt)h(|x|+t)dt` to `k` gives a source for
`F(z)/(1−z²/α²)^j`. At step `j`, the remaining zero of the Fourier
transform at `α` makes the even join smooth. The first-atom tail
bound and `|sin(αt)|≤exp(|Im α|t)` keep every source bounded by `Ck`.
Conjugate fractions combine to real even sources. Thus the bounded
annihilator of `V` has real dimension `2M+1`, represented exactly by
the real even polynomials `E` of degree at most `4M`. Annihilating
`1` imposes `E(0)=0` and leaves dimension `2M`. Duality gives (1).

If there are infinitely many off-line quartets, the finite-subset
zero-division sources give arbitrarily many linearly independent
bounded annihilators of `V` and `1`: their rational Fourier quotients
have poles at distinct quartets. Thus the codimension is infinite.

## Sharp moment filtration and positive local moduli

The finite-defect classification has a stronger consequence than (1).
Suppose `M<∞`, and let `W` be the real vector space of real even sources
`u` with `|u|≤C_u k` whose Fourier transforms retain every real zero of
`F` through its full multiplicity. For `N≥0`, put

```text
W_N={u∈W : ∫x^(2j)u(x)dx=0 for 0≤j≤N}.
```

Then the exact dimension is

```text
dim_R W_N=max(2M−N,0).                                    (2)
```

Indeed, write `Fourier(u)=F E/P` using the classification above, with
`E` real even and `deg E≤4M`. Since `F(0)>0` and `P(0)=1`, vanishing of
the displayed moments is equivalent to `E` having a zero of order at
least `2N+2` at the origin. Its possible monomials are precisely
`z^(2N+2),z^(2N+4),…,z^(4M)`, giving (2). Conversely, the partial-fraction
source construction realizes every such polynomial, so this is an exact
dimension, not an upper bound. If infinitely many off-line quartets
exist, `W_N` is infinite-dimensional for every fixed `N`, by applying
the same construction to arbitrarily large finite subsets.

Every direction in `W_N` gives a *positive* local source deformation
with the **same complete real-zero divisor and first `N+1` even
moments**. For `u∈W_N`, both `u/k` and `E/P` are bounded on their real
axes. Hence for sufficiently small real `ε`, the source `k+εu` is
strictly positive and the real multiplier `1+εE(x)/P(x)` is strictly
positive for every real spectral `x`. The Fourier transform therefore
has exactly the original real zeros, with the same multiplicities;
there are neither lost nor new real zeros. The moment equalities follow
from `u∈W_N`.

There is one further exact filtration by the first-atom tail. Each
proper zero-division source has ratio to `k` tending to zero on both
tails, while the polynomial quotient's constant part at infinity is
the coefficient of `k` in its partial fractions. Consequently

```text
lim_(|x|→∞) u(x)/k(x) = lim_(|z|→∞) E(z)/P(z).
```

Within `W_N`, requiring this limit to be zero removes precisely the
top coefficient of `E`, so the dimension becomes
`max(2M−N−1,0)`. In particular, a **single hypothetical simple
off-line quartet** admits a nonzero real even source with zero mass,
unchanged leading theta tail, and the complete same real-zero divisor:
take `Fourier(u)=z²F/P`. Small perturbations `k+εu` remain positive.
The second moment detects this direction. Thus mass, first-atom tail
normalization, source positivity and all real-zero data together still
do not identify the literal source if one off-line quartet exists.

The last surviving direction is explicit. If `0<M<∞`, set

```text
Fourier(u_*)(z)=z^(4M) F(z)/P(z).
```

This is a real even source bounded by `Ck`, assembled from repeated
off-line zero divisions. Its first `2M` even moments, of orders
`0,2,…,4M−2`, vanish, while its moment of order `4M` is nonzero
because the coefficient of `z^(4M)` in its transform is `F(0)>0`.
For small `t>0`, `k+t u_*` is positive and has transform

```text
F(z) [P(z)+t z^(4M)]/P(z).
```

For real `x`, `P(x)>0` (it is a product of conjugate squared factors),
so this multiplier is positive. At every original off-line zero the
quotient `F/P` is nonzero; that zero is moved into the zeros of
`P+t z^(4M)`. Thus an entire off-line divisor can move inside a
positive theta-dominated family while **all** real zeros and the first
`2M` even moments stay fixed. One additional even moment kills the
last direction by (2).

This is a conditional deformation theorem, not a new route to RH.
It falsifies the conjecture that positivity, relative theta domination,
complete real-zero data and any fixed finite moment list determine the
literal source without an independent bound on the off-line defect.
The sharp dimension identifies the missing information as one real
degree of freedom per even-moment constraint, ending only after the
whole hypothetical off-line divisor has been paid for.

## Proof of sharp `L^p` failure

For every `m≥1`, the corpus's exact theta derivative polynomials and
first-atom tail give, for some `C_m`,

```text
|k⁽⁴ᵐ⁾(x)|/k(x) ≤ C_m exp(8m|x|)              (|x|≫1).
```

The `4m`-th derivative polynomial has degree `8m` more than the
positive seed polynomial in `exp(x)`; the higher integer atoms are
exponentially smaller than the first. The source has every exponential
moment, so `f_{4m}=k⁽⁴ᵐ⁾/k` belongs to `L^q(μ)` for every finite `q`.
Its first-atom tail has a nonzero leading term of degree `8m` in
`exp(x)`, so the functions `f_{4m}` are linearly independent.

Repeated integration by parts yields
`Fourier(k⁽⁴ᵐ⁾)(z)=z⁴ᵐF(z)`. Hence each transform contains every zero
of `F` with at least its multiplicity and vanishes at `0`. Thus every
`f_{4m}` annihilates `1` and every real-zero jet. For any `1<p<∞`,
choose the finite Hölder conjugate `q`; integration against the
linearly independent `f_{4m}` gives an infinite-dimensional space of
bounded functionals on `L^p_even(μ)` that kill the proposed span.
Hahn–Banach proves infinite codimension. No RH assumption enters.

## Why this changes the problem space, and its limit

The real Xi zeros are an exact complete system at the **nonreflexive
`L¹` endpoint** if and only if they are the whole Xi divisor. At every
reflexive `L^p` scale, including the natural Hilbert space, the same
system is incomplete for an explicit source-derived reason. This is
not just a different expression for a positivity receiver: it identifies
the topology in which real-zero data can determine the literal source,
and an exact derivative direction invisible in all softer topologies.

The equivalence is theta-specific, not a formal consequence of a
positive source with real transform zeros. The Gaussian-mixture control
in the relative-source rigidity card has all-real zeros and admits a
nonconstant bounded-relative source with the same complete divisor;
its real-zero modes therefore fail the analogous weighted `L¹`
completeness test.

It does **not** prove density. A producer would need an arithmetic
construction of `L¹` density, or a direct exclusion of bounded
real-zero annihilators, from the simultaneous modular/Euler source law.
Moving an `L²` argument to `L¹` by continuity is impossible because
`f₄` is already an `L²` annihilator. The off-line source above shows
that a proof based only on the count or asymptotic density of real
zeros is also insufficient: one missing conjugate pair supplies a
bounded annihilator even if its omission has zero density.

This differs from established completeness results for *all* zeta
zeros in Sonine spaces; see
[Burnol, “Two complete and minimal systems associated with the zeros of the Riemann zeta function,” §3 and §6](https://www.numdam.org/item/10.5802/jtnb.434.pdf).
The present weighted-`L¹`/real-zero endpoint and its `L^p` contrast
were not found in the current corpus or the limited literature search;
external novelty is not asserted.

## Formalization gate

- [x] Dependency-closed paper proof of the endpoint equivalence and
      exact defect index using relative-source rigidity, complex zero
      division, finite-type indicator collapse, Fourier jets and
      Hahn–Banach; all-order first-atom derivative asymptotics and
      Hölder duality give the infinite `L^p` defect.
- [ ] Formalize the complex one-sided division source and its
      relative bound, including repeated division through a multiple
      off-line zero. The real case is paper-proved separately.
- [ ] Formalize the weighted even `L¹` annihilator equivalence and
      the exact finite-defect dimension and moment filtration;
      formalize the all-order `L^p` derivative witnesses.
- [ ] Formalize relative-source rigidity, which remains the largest
      analytic prerequisite, before claiming the forward RH direction
      in Lean.
