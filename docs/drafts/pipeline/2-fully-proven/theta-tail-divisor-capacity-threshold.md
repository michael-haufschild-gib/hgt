# Sharp theta-tail capacity for preserving the complete Xi divisor

- **ID:** `theta-tail-divisor-capacity-threshold`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper); Lean formalization pending
- **Route:** source-side boundary for STC, CSB, U, K-RVM, MPLF, and RG-HF
- **Status:** `[PROVED HERE ON PAPER] [NOT AN RH PROOF]`

## Theorem

Let `k=thetaCuspFullSource`, `F=XiC` in the corpus's Fourier normalization, and
let `u∈L¹(ℝ)` satisfy, for some `a,b,C>0`,

```text
|u(x)| ≤ C exp(−a exp(b|x|))                 (all x).
```

Write `H(z)=∫ℝ exp(−izx)u(x)dx`. If `H` vanishes at **every** zero of `F`
to at least that zero's multiplicity and `b>2`, then `u=0` almost everywhere.
For continuous `u`, the conclusion is pointwise. Equivalently: if `g=k+u`
has the complete Xi divisor as a sub-divisor of its Fourier transform, then
no nonzero difference `g−k` can obey such a tail bound with `b>2`.

The exponent `2` is sharp. For every `m≥1` and sufficiently small `t>0`,
the nonzero perturbation `u=t k⁽⁴ᵐ⁾` has `H(z)=t z⁴ᵐF(z)`, hence preserves
the complete Xi divisor with multiplicities. For every `0<a<π`, it obeys
`|u(x)|≤C_{a,m,t} exp(−a exp(2|x|))`; it cannot obey any bound of the
displayed form with `b>2`. The accompanying source `g=k+u` is positive,
even, globally strongly log-concave, and arbitrarily close to `k` in every
exponentially weighted derivative seminorm, as proved in the companion
[derivative-packet card](theta-derivative-dark-divisor-packets.md).

This is a uniqueness theorem **at the exact tail exponent of the literal
theta source**, rather than only for compactly supported perturbations.
It does not establish that the complete Xi divisor is real.

## Proof: source decay sets angular growth capacity

Put `y=|Im z|`. Absorb the factor `exp(−a exp(b|x|)/2)` into an integrable
majorant. The remaining exponent satisfies, for `v≥0`,

```text
y v − (a/2) exp(bv)
 ≤ (y/b)(log(2y/(ab))−1)       if y≥ab/2,
 ≤ 0                              if y<ab/2.
```

This follows by maximizing the strictly concave function on the left;
when its stationary point is negative, its maximum on `[0,∞)` is at `0`
and is negative. Consequently, with a constant independent of `z`,

```text
log |H(z)| ≤ (y/b) log(2+y) + O_{a,b,C}(1+y).
```

In particular `H` is entire. If `H` is not identically zero, choose `c∈ℂ`
with `H(c)≠0`. On `z=c+Re^{iθ}`, `y≤R|sin θ|+|Im c|`, uniformly in `θ`,
and the preceding bound gives

```text
(1/2π)∫₀²π log|H(c+Re^{iθ})| dθ
 ≤ [2/(πb)+o(1)] R log R,                         (1)
```

because `(1/2π)∫₀²π|sin θ|dθ=2/π`. This angular average is essential:
the cruder maximum-modulus bound loses the sharp exponent `2`.

Let `n_H(c,R)` count zeros of `H` in the disk with multiplicity. The
Riemann–von Mangoldt formula, transported to the `XiC` coordinate, gives

```text
n_F(c,R) = [1/π+o(1)] R log R.                      (2)
```

Indeed the positive ordinates contribute
`[1/(2π)+o(1)]R log R`, their negative reflections contribute the same,
and the imaginary coordinates of all `XiC` zeros are bounded by `1/2`.
A fixed center `c` changes the radius by only `O_c(1)`, hence not the
leading term. Divisor containment gives `n_H(c,R)≥n_F(c,R)`.

Jensen's formula, in counting-function form, says

```text
∫₀ᴿ n_H(c,r) dr/r
  = (1/2π)∫₀²π log|H(c+Re^{iθ})| dθ − log|H(c)|.
```

Using (2) on the left gives `[1/π+o(1)]R log R`; using (1) on the right
gives at most `[2/(πb)+o(1)]R log R`. Thus `1≤2/b`, contrary to `b>2`.
So `H=0`, and Fourier injectivity on `L¹` gives `u=0` almost everywhere.

For sharpness, the corpus's first-atom derivative asymptotic gives, on
both tails,

```text
k⁽⁴ᵐ⁾(x) = exp(−π exp(2|x|) + O_m(|x|)).
```

The leading coefficient is nonzero. Thus every `a<π` supplies the stated
`b=2` upper bound, while any `b>2` upper bound fails. Integration by parts
gives `H=t z⁴ᵐF` and completes the sharpness claim.

## A second, real-divisor-only threshold

If `u` is even and `H` vanishes at every **simple critical-line** Xi zero,
then the same proof, with only those real zeros, yields `b≤3` whenever
`u≠0`. The unconditional Alpöge–Furman theorem supplies at least two
thirds of the positive-ordinate zeros as distinct simple critical zeros:
their two real reflections give `[2/(3π)+o(1)]R log R` zeros of `H`.
Comparison with (1) gives `2/(3π)≤2/(πb)`, hence `b≤3`.
This weaker threshold uses only the known real divisor; the sharp `b=2`
theorem uses the complete divisor, including any hypothetical off-line zeros.

## Relative-source rigidity at the critical tail scale

There is a stronger, exact uniqueness theorem when the perturbation is
bounded *relative* to the literal source:

> **Relative-source rigidity.** Suppose `u` is real, even and measurable,
> `|u(x)|≤C k(x)`, and its entire Fourier transform `H` contains every
> zero of `F` with at least the same multiplicity. Then `u=c k` almost
> everywhere for a real constant `c`. If `u` is continuous, equality is
> pointwise.

Divisor containment gives an entire quotient `Q=H/F`. First `Q` has at
most `O(R)` zeros, counted with multiplicity, in `|z|≤R` and finite
exponential type. Then theta's *quadratic angular gap* forces its type to
be zero, and boundedness on the imaginary axis forces `Q` to be constant.

For the first claim, positivity and evenness of `k` give
`|H(z)|≤C F(i Im z)`. The first-atom tail, or the completed-gamma
formula on the imaginary axis, implies uniformly on a radius-`R` circle

```text
(1/2π)∫ log|H(c+Re^{iθ})|dθ ≤ (R/π)log R + O_c(R).
```

On the other hand, the Riemann–von Mangoldt count and Jensen give
`(1/2π)∫log|F(c+Re^{iθ})|dθ=(R/π)log R+O_c(R)` for any fixed
`c` where `F(c)Q(c)≠0`. Subtracting yields Jensen mass
`∫₀ᴿ n_Q(c,r)dr/r=O_c(R)`, and doubling the radius gives
`n_Q(c,R)=O_c(R)`. The `O(R)` conclusion is sharper than the mere
`o(R log R)` one gets from leading-order capacity alone.

For the second claim, `F` and `H` have order at most one (their maximum
log modulus is `O(R log R)`); Hadamard factorization makes their entire
quotient order at most one. Because `u` and `k` are even, `Q` is even.
Its nonzero roots occur in pairs `±α`, and the linear zero-count bound
implies `Σ_{α/±}|α|⁻²<∞`. Pairing genus-one factors gives
`Q(z)=C z^{2j}∏_{α/±}(1−z²/α²)`; the possible exponential linear
factor vanishes by evenness. Splitting the product at `|α|=2R` and
using `n_Q(R)=O(R)` bounds `log max_{|z|=R}|Q(z)|=O(R)`, so `Q` is of
finite exponential type.

Here is the decisive second step. For `|δ|<π/2`, put
`z_R=R(sin δ−i cos δ)` and `s_R=1/2+i z_R
=1/2+R cos δ+iR sin δ`. The relative source bound and positivity of
`k` give, for every complex `z`,

```text
|Q(z)| ≤ C F(i Im z)/|F(z)|
```

wherever `F(z)≠0`. On the chosen rays `Re s_R→+∞`, so `ζ(s_R)→1`
uniformly for fixed `δ`, and the completed-gamma formula plus sectorial
Stirling expansion gives

```text
limsup_{R→∞} R⁻¹ log|Q(z_R)|
 ≤ D(δ) := ½[cos δ log(cos δ) + δ sin δ].          (3)
```

The polynomial factors of `xi` contribute `O(log R)`; the `π^{-s/2}`
factors cancel because the two compared arguments have the same real
part. In particular `D(δ)=δ²/4+O(δ⁴)` near zero. There are no Xi zeros
on these rays for large `R`, since `Re s_R>1`.

For any nonzero entire function of finite exponential type, the
Phragmén–Lindelöf indicator
`h_Q(θ)=limsup_{R→∞}R⁻¹log|Q(Re^{iθ})|` is the support function of a
compact convex indicator diagram. The bound `|Q(iy)|≤C` for all real
`y` follows directly from `|u|≤Ck` and `F(iy)>0`. Evenness of `u` and
`k` makes `Q` even, so its indicator diagram is centrally symmetric.
The bounds on both imaginary rays force this diagram to lie on the real
axis, hence it is a segment `[-A,A]`, `A≥0`. Its indicator near the
negative imaginary ray is `A|sin δ|`. Comparing with (3) for positive
and negative `δ` gives `A|sin δ|≤D(δ)=O(δ²)`, so `A=0`.

Thus `Q` is of minimal exponential type. Rotate the plane by `π/2`:
`q(w)=Q(iw)` is an entire function of minimal type bounded on the real
axis. The Bernstein/Phragmén–Lindelöf bound for such a function gives
`|q(x+iy)|≤sup_{t∈ℝ}|q(t)|` throughout the plane; Liouville makes `q`
constant. Consequently `H=cF`, and Fourier injectivity gives `u=ck`.
Reality of `u` and positivity of `k` force `c∈ℝ`. The derivative packets
do not contradict this rigidity because `k⁽⁴ᵐ⁾/k→+∞` on both tails.

The indicator-diagram step is classical Pólya theory. Its finite-type
form and supporting-function identity are summarized in
[Beauduin, arXiv:2605.25400, introduction](https://arxiv.org/abs/2605.25400).
The proof uses only that classical finite-type case, not the paper's
new maximal-type extension.

This rigidity is source-specific. As a control, take
`k_G(x)=[exp(−(x−a)²)+exp(−(x+a)²)]/2`, `a>0`, and
`u_G(x)=k_G(x) cos(ωx)` with `aω=2π`. Then `k_G>0` is even,
`|u_G|≤k_G`, and exact Gaussian Fourier translation gives

```text
F_G(z)=√π exp(−z²/4) cos(az),
H_G(z)=exp(−ω²/4) F_G(z) cosh(ωz/2).
```

So a nonconstant even finite-type quotient occurs for a positive source
with periodic zeros. Its indicator has the linear angular cusp forbidden
by the completed theta/gamma comparison (3). This failed generic
conjecture isolates precisely where the literal source matters.

## Meaning and limit

The double-exponential exponent of the literal theta source is not an
incidental analytic estimate. Its value `2` is exactly the angular Jensen
capacity needed to carry the full Riemann–von Mangoldt zero density.
The differential packets preserve that divisor at the capacity boundary.
Compact-tail perturbations and all faster-tail perturbations have too little
capacity to preserve it. Therefore a source-side argument that keeps the
entire divisor must control behavior **at** the theta tail scale, not merely
on compact sets or in a strictly faster tail class.

Capacity is a radial counting constraint. Xi zeros, on or off the critical
line, stay within bounded distance of the real axis in this coordinate.
Their horizontal displacement does not change the leading `R log R`
count or angular growth. A further arithmetic law is needed to resolve
that bounded displacement; the theorem does not supply one.

## Formalization gate

- [x] Dependency-closed paper proof from Riemann–von Mangoldt, Jensen,
      Fourier injectivity, literal first-atom asymptotic, sectorial
      Stirling, classical Pólya indicator diagrams, and the bounded
      minimal-type Phragmén–Lindelöf theorem.
- [x] Existing corpus: `XiZeroCountRVMRemainder`,
      `XiZeroCountJensenBound`, `Zeta23SimpleCriticalDensity`, and
      `ThetaCuspDerivativeLeadingSign` supply relevant ingredients.
- [ ] Formalize the uniform Fourier growth bound and angular Jensen
      coefficient `2/(πb)` for double-exponential source tails.
- [ ] Formalize the complete-divisor containment and sharp `b>2`
      contradiction; link the derivative packet after its remaining
      Fourier-factor formalization.
- [ ] Formalize the relative-source quotient's linear extra zero count
      and finite exponential type, then the sectorial gamma/Stirling
      bound, indicator collapse and bounded minimal-type Liouville step.

The Jensen and Legendre-transform ingredients are classical. The exact
theta-source/divisor capacity statement was not found in the current
corpus search; no external publication novelty is claimed without an
independent literature audit.

Reference for the unconditional two-thirds input in the real-divisor-only
corollary: L. Alpöge and R. Furman,
[More than two thirds of the zeta zeros are simple and on the critical line](https://arxiv.org/abs/2608.13637)
(2026), already imported into the Lean corpus as `Zeta23`.
