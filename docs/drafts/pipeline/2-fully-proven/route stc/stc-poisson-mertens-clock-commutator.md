# Poisson prime history has a noncompact Mertens-clock seam and a physical-clock domain wall

- **ID:** `stc-poisson-mertens-clock-commutator`
- **Stage:** 2-fully-proven (paper)
- **Type:** THEOREM (paper)
- **Routes:** STC, RHist, U, Sonin/Gamma source transport
- **Status:** `[PROVED HERE ON PAPER] [PHYSICAL-CLOCK DOMAIN WALL PROVED IN LEAN] [FULL OPERATOR THEOREM OPEN IN LEAN] [NOT AN RH PROOF]`
- **Source:** The literal depth-zero prime amplitude in `STCEulerPrimeBoundaryTangentGram.lean`, the full Poisson history in `PoissonScaleHistoryFrame.lean`, and Mertens' second theorem in `MertensSecondPrimeRecipSum.lean`.

## Source kernel and the proposed reinterpretation

Let `P` be the primes, `t_p=log p>0`, `x_p=log t_p`, and `H=ℓ²(P)`.
The literal critical-boundary Gamma–Euler amplitude at positive aperture `u` is

```text
b_u(p) = t_p p^(-1/2) exp(-u t_p/2).
```

Aggregate *all* positive apertures using the Poisson history's actual half-density:

```text
K(p,q) = ∫_0^∞ u b_u(p)b_u(q) du
       = 4 t_p t_q / [sqrt(pq)(t_p+t_q)²]
       = (pq)^(-1/2) h(x_p-x_q),
h(z)   = sech²(z/2).
```

Indeed `ψ_t(a)=2t sqrt(a) exp(-ta)` from `PoissonScaleHistoryFrame.lean` satisfies
`K(p,q)=(pq)^(-1/2)∫_0^∞ ψ_(t_p)(a)ψ_(t_q)(a) da` after `a=u/2`.
Thus the aperture weight is the already formalized Poisson half-density; the
choice to aggregate this particular Gamma–Euler source over all apertures is
an additional source architecture, **not** a consequence of a Xi zero.

The change from physical prime clock `t_p=log p` to the Mertens clock
`x_p=log log p` is the central proposed reinterpretation. In `x`, the full
history is a translation-invariant kernel; prime reciprocal measure is
asymptotically Lebesgue. This changes the operator domain and compactness
behavior of the all-prime source.

## Theorem

1. `K` defines a bounded positive self-adjoint operator on `H`. It is
   noncompact. More exactly, its essential spectrum is `[0,4]` and its
   essential norm is `4`.
2. Multiplication `X` by `x_p` is unbounded, but `K` maps finitely supported
   vectors into `Dom X`. The commutator `XK-KX` on that core has a bounded
   skew-adjoint extension `C`, with matrix
   `C(p,q)=(x_p-x_q)K(p,q)`. The extension is noncompact and its essential
   norm is at least `h(3)>0`.
3. Multiplication `T` by the physical clock `t_p` has a sharply different
   domain: for **every** prime `q`, `K δ_q ∉ Dom T`. Thus the ordinary
   commutator `TK-KT` is not defined on even one prime basis vector.
4. More sharply, for the physical-clock powers `T^β`, the commutator has
   an exact regularity phase diagram:

   - `β<0`: `T^β` is compact, so `[T^β,K]` is compact.
   - `β=0`: `[T^0,K]=0`, but its coefficientwise derivative in `β` is
     `[log T,K]=C`, bounded and noncompact.
   - `0<β<1`: `K` maps the finite-support core into `Dom T^β`;
     `[T^β,K]` is densely defined there but has no bounded extension.
   - `β≥1`: `Kδ_q∉Dom T^β` for every prime `q`.

5. For every fixed real grade `g≠0`, each fixed column of both reflected
   kernels

   ```text
   K_even,g(p,q)=K(p,q) cosh(g(t_p+t_q)/2),
   K_odd,g(p,q) =K(p,q) sinh(g(t_p+t_q)/2)
   ```

   lies outside `H`. At `g=0`, `K_even,0=K` is bounded noncompact, whereas
   `K_odd,0=0`. This is a universal source admission wall, independent of
   Xi zeros.

## Proof

The displayed kernel identity follows from
`∫_0^∞ u exp(-cu)du=c^(-2)` with `c=(t_p+t_q)/2>0`.
Finite quadratic forms are nonnegative because they equal
`∫_0^∞ u(∑_p c_p b_u(p))²du` for real finite packets; complex positivity
uses the modulus square.

Set `S_n={p∈P:n≤x_p<n+1}` for integers `n≥0` and
`m_n=∑_(p∈S_n)1/p`. Mertens' second theorem
`∑_(p≤y)1/p=log log y+B+o(1)` gives `m_n→1`: use the real cutoffs
`exp(exp n)` and `exp(exp(n+1))`; endpoint choices change at most one
term tending to zero. Each shell is finite and `M=sup_n m_n<∞`.
Prime `2`, for which `x_2<0`, is a finite exceptional row.

Since `h(z)≤4 exp(-|z|)`, for `p∈S_i`,

```text
∑_q K(p,q)/sqrt(q) · sqrt(p)
  = ∑_q h(x_p-x_q)/q
  ≤ finite exceptional term + 4e M ∑_(j≥0) exp(-|i-j|)
  ≤ A < ∞,
```

uniformly in `p`; the exceptional `p=2` row also obeys a finite bound.
The weighted Schur test with weight `p^(-1/2)` gives a bounded operator.
The finite Gram formula then gives positivity and self-adjointness.

For large `n`, define the unit vector
`e_n(p)=1_(S_n)(p)/sqrt(m_n p)`. Their supports are disjoint, so
`e_n ⇀ 0`. Since `|x_p-x_q|<1` on `S_n×S_n`,

```text
⟨K e_n,e_n⟩
  = m_n^(-1) ∑_(p,q∈S_n) h(x_p-x_q)/(pq)
  ≥ h(1)m_n → h(1)>0.
```

Every compact operator sends this weakly null sequence to a norm-null
sequence, proving the stated essential-norm lower bound.

For the compressed commutator, `|z|h(z)≤A₁ exp(-|z|/2)`.
The same weighted Schur argument bounds the matrix `C` on `H`.
For each fixed `q`, the shell estimate with the stronger squared kernel
shows `∑_p x_p² K(p,q)²<∞`; hence `Kδ_q∈Dom X` and the matrix is the
actual core commutator. Its transpose is `-C`, so its bounded extension
is skew-adjoint. If `p∈S_n` and `q∈S_(n+2)`, then
`-3<x_p-x_q≤-1` and `-(x_p-x_q)h(x_p-x_q)≥h(3)`.
Consequently

```text
|⟨e_n,C e_(n+2)⟩| ≥ h(3) sqrt(m_n m_(n+2)) → h(3)>0.
```

Since `e_(n+2) ⇀ 0`, `C` is noncompact and has the stated lower bound.

For physical `T`, fix `q`. If `t_p≥2t_q`, then

```text
t_p² |K(p,q)|²
  = [16 t_p⁴ t_q²/(t_p+t_q)⁴] / (pq)
  ≥ [16 t_q²/((3/2)⁴q)] / p.
```

The constant can be weakened arbitrarily; its positivity matters.
Euler's divergent prime harmonic sum `∑_p1/p=∞` gives
`∑_p t_p²|K(p,q)|²=∞`. (The displayed numeric bound follows from
`t_p+t_q≤(3/2)t_p`.) Thus `Kδ_q∉Dom T`.

For the power classification, `t_p²β|K(p,q)|²` is comparable on each
fixed `q` tail to `1/[p (log p)^(2-2β)]`. The established prime
reciprocal-log tail theorem gives summability exactly when `β<1`;
for `β≥1`, a fixed positive multiple of `1/p` is a lower bound for
large primes. For `β<0`, the diagonal multiplier `t_p^β` is compact
because `t_p→∞`, so its commutator with bounded `K` is compact.
At `β=0`, differentiating `t_p^β-t_q^β` on each fixed pair gives
`x_p-x_q`.

For `0<β<1`, the core commutator exists. On `S_n×S_(n+2)`,

```text
t_q^β-t_p^β ≥ exp(βn)(exp(2β)-exp(β)).
```

The same positive cross-shell pairing used for `C` then gives

```text
|⟨e_n,[T^β,K]e_(n+2)⟩|
  ≥ h(3) sqrt(m_n m_(n+2)) exp(βn)(exp(2β)-exp(β)) → ∞.
```

Hence no bounded extension exists for any `β>0` in the core-admitted
range. The logarithmic clock is the singular first variation at the
boundary between compact negative powers and unbounded positive-power
commutators.

Finally, for fixed `q` and large `p`, `h(x_p-x_q)` is comparable from
below to `t_q/t_p`. For `g≠0`, each hyperbolic factor has magnitude
at least a positive `q,g` constant times `p^(|g|/2)` once `p` is
large. Hence each squared column dominates a positive multiple of
`p^(|g|-1)/(log p)²`. Because `p^|g|/(log p)²→∞`, that tail dominates
`c/p`; the prime harmonic divergence proves item 5.

## Exact universal Calkin model and essential spectrum

The lower bound above understates the operator result. Enumerate primes
`p_1<p_2<⋯`, set `μ_n=1/p_n`, `y_n=∑_(j<n) μ_j`, and partition the
half-line into `I_n=[y_n,y_n+μ_n)`. Euler's prime-harmonic divergence
makes these intervals cover `[0,∞)` up to endpoints. The map

```text
U : H → L²(0,∞),   Uδ_(p_n)=μ_n^(-1/2) 1_(I_n)
```

is an isometry onto the closed step-function subspace `S`. The
extension `A=UKU*` acts by the step kernel
`h(x_(p_n)-x_(p_m))` on `I_n×I_m`, and vanishes on `S⊥`.
Let `W` be the Wiener–Hopf convolution operator with kernel `h(y-z)`
on `L²(0,∞)`.

Mertens' second theorem gives a **single** constant `B` with
`y_n=x_(p_n)+B+o(1)`. Also `μ_n→0`. Therefore, uniformly for
`y∈I_n,z∈I_m` with both `n,m` in a sufficiently late tail,

```text
|(x_(p_n)-x_(p_m))-(y-z)| ≤ ε_N,   ε_N→0.
```

The function `h` and its derivative decay exponentially. By the mean
value theorem the two kernels differ on the late-tail square by at most
`C ε_N exp(-|y-z|/2)`. The Schur test makes that late-tail difference
have norm `O(ε_N)`. On the complement, one variable lies in a bounded
union of initial cells; exponential decay makes the difference kernel
square-integrable, hence Hilbert–Schmidt. Thus

```text
UKU* - W is compact.                                      (†)
```

In fact (†) is **Hilbert–Schmidt**. The existing sharp Mertens bound
`|∑_(p≤N)1/p-log log N-B|≤C/log N` gives
`|y_n-x_(p_n)-B|≤C'/t_(p_n)`. Since a cell has width `1/p_n`,
there is a global constant `D` such that, for `y∈I_n`,
`|x_(p_n)-y+B|≤D exp(-y)`. After increasing `D` to absorb the finite
initial cells, the mean value theorem and exponential decay of `h'`
give the global kernel estimate

```text
|h(x_(p_n)-x_(p_m))-h(y-z)|
  ≤ D' (exp(-y)+exp(-z)) exp(-|y-z|/2).
```

Its square is integrable on `[0,∞)²`: split into `y≥z` and `z≥y`,
then integrate the exponentially decaying minimum coordinate and
coordinate gap. The same argument applies to `j(z)=z h(z)`, whose
derivative also decays exponentially. Therefore the embedded
compressed-clock commutator `UCU*` differs by a Hilbert–Schmidt
operator from the Wiener–Hopf operator with kernel `(y-z)h(y-z)`.
This identifies the
**whole Calkin class** of the bounded source seam, not merely one
noncompact test sequence.

For completeness, `h` is positive definite: its values are Gram
coefficients of the translated full Poisson histories. Hence `W≥0`.
Young's inequality and `∫_ℝ h(z) dz=4` give `‖W‖≤4`. Let
`ĥ(ξ)=∫_ℝ h(z)e^(-iξz)dz`. It is continuous,
`ĥ(0)=4`, and `ĥ(ξ)→0` as `|ξ|→∞` by the Riemann–Lebesgue lemma.
Long normalized plane-wave packets `e^(iξy)` supported in intervals
moving far to the right are weakly null Weyl sequences for `W` at
`ĥ(ξ)`. Thus the essential spectrum of `W` contains the whole
interval `[0,4]`; positivity and the norm bound give the reverse
inclusion.

Compact equivalence (†) gives
`σ_ess(K)∪{0}=σ_ess(W)=[0,4]`. Finally `0∈σ_ess(K)`:
the prime basis vectors are weakly null and
`‖Kδ_p‖²≤A/p→0`, by the same reciprocal-weight row bound used above
(`h²≤h`). Therefore `σ_ess(K)=[0,4]` and `‖K‖_ess=4`.

This is an unconditional **universality theorem**. The bulk Calkin
image of the source is the fixed Wiener–Hopf convolution model;
arithmetical information beyond Mertens' second theorem resides in
the compact difference. A direct RH criterion using only this source
Calkin class cannot acquire a Xi-zero-specific signal from prime
fluctuations; a successful route must couple in a separate zero
condition or retain information discarded by the quotient.

A zero ordinate inserted only as a prime phase does not provide that
condition. For every real `τ`, the diagonal unitary
`D_τδ_p=exp(iτ log p)δ_p` commutes with both clock multipliers.
The phase-twisted kernel is `K_τ=D_τ K D_τ*`, so its essential spectrum,
commutator class, and physical-column domain failure are identical for
all `τ`, including ordinates of actual Xi zeros. This kills the
phase-only conjecture. A remaining transport must use the zero equation
through signed arithmetic or completion data, rather than its height
as a unitary gauge alone.

There is an exact Xi-divisor Hilbert–Schmidt determinant elsewhere in the
corpus: `thetaSourceEntireDet2_eq_zero_iff_XiC_eq_zero` in
`HedenmalmThetaSourceSpectrumExact.lean`. A first conjecture was to
identify its compact source inverse `B` unitarily with `UKU*−W`.
In the corpus convention `XiC(z)=xi(1/2+i z)`, this would make the
determinant zeros real and prove RH. It fails before any spectral
estimate: `UKU*−W` is self-adjoint, while the exact theta kernel is

```text
B(t,u)=i q(t)(1_(u≤t)−t),   0<t,u<1,   q(t)>0.
```

On `t<u`, self-adjointness would require
`q(t)t=q(u)(1−u)`. Apply this relation to almost every triple
`t₁<t₂<t₃`. The `(t₁,t₂)` and `(t₁,t₃)` pairs, together with the
`(t₂,t₃)` pair, force `q(t₂)(1−t₂)=q(t₂)t₂`. Since `q(t₂)>0`, this
would force almost every `t₂` to equal `1/2`, a contradiction.
Hilbert–Schmidt kernel uniqueness justifies the almost-everywhere
comparison. Thus no direct unitary identification with the arithmetic
Hilbert–Schmidt defect exists. The corpus already has a singular
source-selected theta metric: `HedenmalmThetaMetricCommutator.lean`
proves its exact rank-two boundary Green identity, and
`HedenmalmThetaFredholmEigenmodeGreenIsotropy.lean` proves that
neutrality of that boundary form on every nonzero source eigenmode is
equivalent to RH. The missing theorem is **not** metric existence or
another equivalent criterion. It is an independent arithmetic reason
that actual Xi eigenmodes have balanced incoming and outgoing boundary
ports. No source-derived map from the prime Hilbert–Schmidt defect to
those two ports is established here.

## What this changes, and what remains open

The full source history supplies a genuine all-prime Calkin survivor:
`C=[log log p,K]` is bounded and noncompact. Every positive physical-clock
power produces an unbounded commutator, and powers at least one fail even
at the basis-vector domain. This separates two clocks that fixed-regulator
STC estimates treated together. Any proposed
source-to-Sonin transport must explain how its physical prime-height
seam is obtained from this compressed-clock object, including the
unbounded change of domain. A bounded entrywise calibration does not
do that.

The theorem is universal in the prime source and does not use a Xi
zero. It therefore cannot by itself prove RH. The hard remaining gate
is a **Xi-zero-specific** source-to-Sonin statement: an actual zero
would have to force an admitted physical-clock transport or an
operator relation that contradicts the domain wall off the critical
line. Neither implication is established here.

This card's paper proof depends only on the existing Mertens theorem,
Euler prime-harmonic divergence, the Poisson Gram identity, and the
weighted Schur test. `STCPoissonPrimePhysicalClockWall.lean` proves the
exact source-kernel square identity and the unsummable physical-clock
column for every fixed prime. It also identifies the kernel with the
normalized full Poisson-history Gram. Direct `lake env lean` passed.
A leaf-only Lake audit expanded into unrelated dependency rebuilds and
was stopped; no leaf `.olean` audit is claimed. The bounded
noncompact operator and full power phase diagram remain paper-only.
Corpus search found their ingredients but no exact full-history prime
operator or two-clock commutator classification; deep search was
partial, and external novelty is unverified.

The arithmetic difference `UKU*−W` has since been strengthened from
Hilbert–Schmidt to nonzero trace class with zero trace and a signed
spectrum. Its precise determinant-class obstruction and relative
Fredholm survivor are proved in
[the Mertens trace-class barrier](stc-mertens-trace-class-xi-divisor-barrier.md).
