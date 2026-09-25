# Center integration turns finite theta heads into a pair-singularity problem

- **Stage:** In progress. Fixed-cutoff asymptotic has a dependency-closed paper proof below; Lean closure and external priority audit pending.
- **Routes:** CLG/TTF, S6F, TCD.
- **Status:** Fixed-cutoff positive tail proved on paper; joint cutoff/order source law still open. Not RH.

## Literal carrier and the change of arena

For `N≥1`, put `h_N(z)=Σ_(1≤n≤N) thetaCuspComplexSourceTerm(z,n)` and, for
`0<a<1/2`, let

```text
J_(N,a)(z) = ∫_(r>0) r sinh(a r) h_N(r/2+z) h_N(r/2−z) dr.
```

This is the finite-head version of the native center-mixed density in
`HedenmalmCenterMixedLocalThreePoint.lean`. It is a holomorphic germ on
`|Im z|<π/4`, not an entire function. The finite head *before* integration
is entire and imaginary-periodic; the unbounded center integral changes its
analytic category. For `N=1`, the exact positive boundary blow-up is proved
on paper in `theta-finite-atom-order-escape.md`.

## Exact pair geometry

After `y=e^r`, the ordered `(n,m)` product has Gaussian factor

```text
exp(−c_(n,m)(z)y),
c_(n,m)(z)=π(n² exp(2z)+m² exp(−2z)).
```

Its polynomial prefactor has leading term `(2π)^4 n⁴m⁴ y⁴` times
`y^(1/2)`, and the center weight contributes
`(log y)(y^a−y^(−a))dy/(2y)`. The zero set of `c_(n,m)` is

```text
z = (1/2) log(m/n) + (2k+1)πi/4,      k∈ℤ.
```

This follows by multiplying the zero equation by `exp(2z)` and taking
modulus/argument of `exp(4z)=−m²/n²`. Every pair is regular in the central
strip. **Only diagonal pairs `n=m` meet its nearest wall at `z=±πi/4`**;
off-diagonal pair zeros have strictly larger distance from the origin.
For `N≥2`, the closest off-diagonal pair zeros have distance

```text
R_N = sqrt((π/4)² + (log(N/(N−1))/2)²) > R:=π/4.
```

Thus `R_N−R` is of order `N^(−2)`. At Taylor order `j`, the geometric
suppression of those closest off-diagonal singularities is
`(R/R_N)^j`, so the first joint cutoff/order scale is `j≈N²`.
This is a location law, not a bound on their total coefficients.

## Diagonal boundary charge

For `n=m`, `c_(n,n)(z)=2πn² cosh(2z)`. Write `α=9/2+a` and
`v↑R=π/4`. The highest polynomial term and the `y^a` side of the
center weight give

```text
J_(N,a)(iv) ~ A_(N,a) (1−v/R)^(−α) log(1/(1−v/R)),
A_(N,a) = (2π)^4 Γ(α) π^(−2α) / 2 · Σ_(n≤N) n^(−1−2a) > 0.
```

Here `~` has the fixed-`N` paper proof below. The exponent and the arithmetic weight are exact
from the displayed integrand: `y^(α−1)log y` has Laplace singularity
`Γ(α)c^(−α)log(1/c)`, while `n⁸(n²)^(−α)=n^(−1−2a)`.
The diagonal charge remains finite as `N→∞` for fixed `a>0`, but that
does not control the accumulating off-diagonal pairs.

## Fixed-cutoff theorem (paper)

For each fixed `N≥1` and `0<a<1/2`, the Fourier-signed even Taylor jets
of the **integrated** finite head are eventually strictly positive:

```text
∃ j₀, ∀ j≥j₀,  (−1)^j J_(N,a)⁽²ʲ⁾(0) > 0.
```

More precisely, the fixed-`N` coefficient asymptotic is

```text
(−1)^j J_(N,a)⁽²ʲ⁾(0)/(2j)!
 ~ (2π)^4 π^(−2α) (Σ_(n≤N)n^(−1−2a))
    · R^(−2j) (2j)^(α−1) log(2j).
```

The two nearest singularities add, rather than cancel, in the even
Taylor subsequence. This is source-specific and not yet proved in Lean.

### Paper proof of the asymptotic

Put `v=−iz` and write `F(v)=J_(N,a)(iv)`. In `y=e^r` coordinates,
expand the two literal seed polynomials. Every ordered `(n,m)` summand
is a finite linear combination, with coefficients entire in `v`, of

```text
L_β(c_(n,m)(iv)) = ∫₁∞ y^(β−1) log y exp(−c_(n,m)(iv)y)dy,
β=d+1/2±a,    d∈{2,3,4}.
```

All these `β` are positive. On `Re c>0`, differentiation of the Gamma
integral in `β` gives the exact continuation formula

```text
L_β(c)=Γ'(β)c^(−β)−Γ(β)c^(−β)log c−E_β(c),
E_β(c)=∫₀¹ y^(β−1)log y exp(−cy)dy.
```

`E_β` is entire. Therefore a pair summand continues analytically on
any simply connected zero-free domain of `c_(n,m)(iv)`, with the log
branch selected from `c_(n,m)(0)>0`. For fixed `N`, all off-diagonal
pairs are holomorphic in a disc of radius strictly larger than `R`:
their nearest zeros have modulus at least `R_N>R`. Cauchy's estimate
makes their Taylor coefficients exponentially smaller than `R^(−j)`.

For `n=m`, the nearest singularities are `v=±R`; the next ones are
`±3R`. Near `v=R`,

```text
c_(n,n)(iv)=2πn²cos(2v)
            =π²n²(1−v/R)(1+O(1−v/R)).
```

The unique largest singular order comes from `d=4` and the `+a` part
of `sinh(a log y)`. Its coefficient is positive and independent of
`v`: `(2π)^4 n⁸/2`. It contributes
`((2π)^4/2) Γ(α)π^(−2α)n^(−1−2a)` times
`(1−v/R)^(−α)log(1/(1−v/R))`. Every other diagonal term has
singular order `<α` (`α−2a`, `α−1`, etc.), so is lower order.
The same leading coefficient occurs at `v=−R` by evenness.

Finally, generalized binomial coefficients give
`[w^k](1−w)^(−α)=Γ(k+α)/(Γ(α)Γ(k+1))~k^(α−1)/Γ(α)`.
Differentiating in `α` gives the additional leading `log k` for
`[w^k](1−w)^(−α)log(1/(1−w))`. Analytic nonzero factors in the
local coordinate contribute only a lower power of `k`; Cauchy bounds
handle the off-diagonal gap. Taking `k=2j`, the two singularities
`±R` add and the `Γ(α)` factors cancel, yielding the stated
coefficient asymptotic and eventual strict positivity.

## Whole-route consequence and next hard test

The fixed-`N` tail, even if positive, does **not** prove RH: the threshold
may escape with `N`, and the near-diagonal off-diagonal singularities
condense at the same wall on the `j≈N²` scale. The RH-equivalent full
integrated signed cone takes `N→∞` at each fixed jet order. Its hard
source theorem is therefore a joint arithmetic–analytic control of
this condensation, not pointwise finite-head positivity or a fixed-`N`
large-order asymptotic. First prove or falsify the frozen prediction,
then derive a source-faithful uniform double-scaling law; do not infer
the latter from fixed-cutoff singularity geometry.

External priority is unaudited. Route map remains read-only.

## Full-source wall diffraction: paper theorem

The fixed-cutoff singularity calculation has a source-faithful full-sum limit, but
not a uniform holomorphic continuation across the wall. Let
`h(z)=Σ_(n≥1) thetaCuspComplexSourceTerm(z,n)` in `|Im z|<π/4`, and define
`J_a(z)` by the same radial integral with `h` in place of `h_N`. Put
`R=π/4`, `δ(v)=cos(2v)`, and `α=9/2+a`. For each fixed real `b`, the
following **paper theorem** holds for `0<a<1/2`:

```text
lim_(v↑R) δ(v)^α / log(1/δ(v)) · J_a(b+iv)
  = K_a · ζ(1+2a) · T_a(exp(2b)),
K_a = (2π)^4 Γ(α) / (2(2π)^α),
T_a(p/q) = (pq)^(-1/2-a)  (p,q positive coprime),
T_a(t) = 0               (t positive irrational).
```

This is a pointwise limit in the real variable `b`; the discontinuous
rational/irrational readout is compatible with analyticity of every interior
`J_a(b+iv)`. At `b=0`, converting `δ(v)~(π/2)(1-v/R)` recovers the finite-head
constant above with `Σ n^(-1-2a)` replaced by `ζ(1+2a)`. The result is
not a positivity theorem for the full Fourier current and does not imply RH.

### Proof and the infinite-tail issue

For a fixed ordered pair `(n,m)`, the oscillatory Laplace rate at `b+iv` is

```text
c_(n,m)(b+iv) = πδ(v)(n²e^(2b)+m²e^(-2b))
                 + iπsin(2v)(n²e^(2b)-m²e^(-2b)).
```

Only exact resonance `ne^b=me^(-b)`, equivalently `e^(2b)=m/n`, produces
the top-order wall divergence. If `e^(2b)=p/q` in lowest terms, resonant
pairs are exactly `(n,m)=(qk,pk)`. The top polynomial term contributes
`(2π)^4 n⁴m⁴/2` times the Laplace log-moment with exponent `α` and rate
`2πpq k²δ`. After multiplying by `δ^α/log(1/δ)`, its limit is
`K_a(pq)^(-1/2-a)k^(-1-2a)`. Every fixed nonresonant pair has zero
normalized limit, by integration by parts or its analytic Abel boundary
value. Lower polynomial orders and the `y^(-a)` side of `sinh` have zero
normalized limit.

The nontrivial step is passing from finite pairs to the full source without
assuming uniform pointwise convergence at the wall. Regard
`h(r/2+b+iv)` as a vector in the positive Hilbert weight
`r sinh(ar)dr`. Its top-polynomial norm square has diagonal terms whose
normalized limit is a fixed positive constant times
`e^(-(1+2a)b) Σ_(n≥1)n^(-1-2a)`; the lower-polynomial norm is lower order.
For the tail `n>N`, the same bound has the sum restricted to `n>N`.

Here is the uniform off-diagonal estimate that licenses this assertion.
For each `β` in the finite list `d+1/2±a`, `d∈{2,3,4}`, repeated
integration by parts (`k>β` times) yields, for `ε>0` and `|λ|≥c>0`,

```text
|∫₁∞ y^(β-1) log(y) exp(-(ε+iλ)y)dy|
    ≤ C_(β,c) exp(-ε/4) / |λ|².
```

The first boundary term vanishes because `log 1=0`; higher boundary terms
and the `k`th-derivative remainder are uniformly controlled in `ε`.
For a single shifted norm, `|λ|` is a fixed positive multiple of
`|n²-m²|` near the wall. The top-order off-diagonal sum is therefore at
most a constant (depending on `b,a`) times

```text
Σ_(n≠m) n⁴m⁴ exp(-cδ(n²+m²))/(n²-m²)² = O(δ^(-7/2)).
```

Indeed, for `n>m` write `k=n-m`; the summand is bounded by
`n⁶ exp(-cδ n²)/k²`, and sum over `k` then `n`. Since
`α=9/2+a>7/2`, this is negligible after wall normalization. The
lower-order norm has an analogous smaller bound. For diagonal top terms,
the scaled Laplace moments are dominated by `C n^(-1-2a)` and converge
termwise; this is summable because `a>0`. The `y^(-a)` terms are lower
order even though their unscaled diagonal weights are not summable.

Finally, Cauchy–Schwarz in the positive radial weight bounds the normalized
full-minus-finite cross current by the geometric mean of the corresponding
shifted tail norms. Its limsup tends to zero as `N→∞` because
`Σ_(n>N)n^(-1-2a)→0`. Thus finite-head resonance limits pass to the
actual infinite theta source, proving the displayed formula for every
fixed `b`, including Liouville-irrational scales; no Diophantine condition
is needed.

## Fixed-aperture wall is phase-retrieval data, not zero-orientation data

For a finite positive-coefficient theta source
`h_c(z)=Σ_n c_n thetaCuspComplexSourceTerm(z,n)`, the same fixed-pair
calculation gives, at aperture `a` and `s=1/2+a`, the rational wall profile

```text
W_(c,s)(r)=Σ_(m/n=r) c_n c_m (nm)^(-s),
```

up to the same positive aperture-dependent scalar; the profile is zero at
nonrealizable ratios. This is the multiplicative autocorrelation of
`w_n=c_n n^(-s)`. It measures intensity and discards phase of the Mellin
Dirichlet polynomial.

The loss persists after fixing the first source coefficient to `1` and
requiring all coefficients to be positive integers. Take support
`n=1,64,64²,64³`, aperture `a=1/6` (`s=2/3`), and coefficient vectors

```text
c_A=(1,68,1280,4096),       c_B=(1,80,1088,4096).
```

Since `64^(2/3)=16`, their weighted vectors are exact reversals:

```text
w_A=(1,17/4,5,1),           w_B=(1,5,17/4,1).
```

Hence `W_(A,2/3)(r)=W_(B,2/3)(r)` for **every** ratio `r`, including the
zero values away from powers of `64`; reversal preserves every lag
autocorrelation. Their Mellin transforms in `Re z>0` are respectively
`archFactor(z) P_A(16·64^(-z))` and
`archFactor(z) P_B(16·64^(-z))`, where

```text
P_A(X)=(1+2X)²(1+X/4),
P_B(X)=(2+X)²(1/4+X).
```

At `z_A=1/3+iπ/log 64`, the polynomial argument is `-4`. Thus A has a
Mellin zero strictly off the critical line and B does not vanish there;
the archimedean factor is nonzero in the open strip. Indeed, all B zeros
in that strip lie on the critical line: its polynomial roots require
`16·64^(-z)=-2` (forcing `Re z=1/2`) or `=-1/4` (forcing `Re z=1`, outside
the open strip). This is a finite-source countermodel, **not** a
counterexample to RH: neither finite source is the modularly completed
arithmetic theta source.

The classical one-dimensional phase-retrieval zero-flip mechanism is known;
the claim here is its exact source-normalized manifestation for this
theta-wall reporter. The Lean companion proves the finite weighted
autocorrelation equality and the differing Mellin value at `z_A`. It does
not yet formalize the analytic wall limit or B's complete strip-zero
classification. The positive survivor is precise: a second aperture
breaks this particular ambiguity. With `x=64^(-2s)`, the difference of
diagonal wall charges is

```text
Σ_i c_A(i)² x^i − Σ_i c_B(i)² x^i = 1776 x (256x−1),
```

so for real `s>0` it vanishes only at `s=2/3`. Multi-aperture or signed
pre-scalar data may retain phase, but recovering the known coefficients is
not itself RH-bearing. The hard source theorem remains signed control for
the literal completed arithmetic source before intensity projection.

## The wall changes topology: a multiplicative Thomae--Bohr profile

The full-source coefficient just proved on paper has a sharper structural
interpretation. For `s=1/2+a>1/2`, remove the positive analytic scalar and
write

```text
W_s(b)=Σ_(n,m≥1; m/n=exp(2b)) (nm)^(-s).
```

If `exp(2b)=p/q` in lowest terms, grouping `(n,m)=(qk,pk)` gives
`W_s(b)=ζ(2s)(pq)^(-s)`; otherwise `W_s(b)=0`. This is a multiplicative
Thomae function: positive on the countable dense log-ratio subgroup and
zero Lebesgue-almost-everywhere. At every irrational-ratio point it is
continuous, while at every rational-ratio point it is discontinuous. For
the latter assertion, any distinct reduced ratios tending to a fixed
`p/q` have numerator-denominator product tending to infinity, so their
charges tend to zero. In particular `W_s(0)=ζ(2s)>0` but every ordinary
Lebesgue test reads zero from `W_s`.

**Positive-definiteness survives in a different topology.** On the
discrete additive group of real log scales, put `v_s(log n)=n^(-s)` for
positive integers `n`, and zero elsewhere. Since `2s>1`, `v_s∈ℓ²`.
Translation gives `W_s(b)=⟨v_s,U_(2b)v_s⟩`, hence every finite matrix
`[W_s(b_j−b_i)]` is positive semidefinite. But this coefficient is not
continuous in the Euclidean topology. Its GNS translation is therefore
not a strongly continuous real-time unitary group, and `W_s` cannot be
the Fourier--Stieltjes transform of a finite ordinary Borel measure on
the real frequency line. The appropriate abstract dual belongs to the
discrete log-scale group (Bohr-type compactification); the ordinary
Lebesgue/Fourier image of the pointwise profile is zero.

This is a precise source-to-spectrum **topology obstruction**, not a new
proof of RH: pointwise wall positivity cannot be transported to the
physical Fourier current. The missing producer must keep the wall and
frequency limits coupled, or retain signed pre-scalar phase before the
discrete-group projection. The analytic current-to-profile limit above
remains paper-only. `ThetaCuspWallBohrTopology.lean` unconditionally
formalizes the exact ordered-pair arithmetic coefficient at `s=2/3`,
its almost-everywhere zero law, annihilation by every Lebesgue test,
its positive diagonal value, and noncontinuity. Positive-definiteness,
the continuity-locus classification, and the Bohr dual interpretation
are paper proofs; external priority of this theta-wall application is
not audited.

**The atomic-measure repair has a sharp threshold.** Instead of treating
`W_s` as a Lebesgue function, form the positive ratio-atom object

```text
μ_s = Σ_(n,m≥1) (nm)^(-s) δ_((log(m/n))/2).
```

For `s>1`, this is a finite measure of total mass `ζ(s)^2`. With Fourier
character `exp(-itb)`, its transform is
`ζ(s+it/2)ζ(s-it/2)=|ζ(s+it/2)|²`, so positivity is automatic and
cannot orient an Xi zero. At the physical apertures `s=1/2+a∈(1/2,1)`,
every individual rational-ratio atom is finite, but `μ_s` has **infinite
mass on every nonempty real interval**. For the fixed interval
`[0,(log 2)/2]`,
take disjoint dyadic blocks `N≤n<2N`, `n≤m<2N`: the ratios lie in
`[1,2]`, there are at least a constant times `N²` pairs, and each weight
is at least `(4N²)^(-s)`. Each block therefore contributes at least
`c_s N^(2-2s)`, bounded below as `N→∞` when `s≤1`. For an arbitrary
interval, take `m/n` in a smaller positive ratio interval and the same
dyadic count. For `s≤1/2`, even a single rational-ratio atom diverges,
because its scaling fibre is `Σ_k k^(-2s)`. Hence the three regimes are:
finite positive measure (`s>1`), finite individual spikes but no locally
finite atomic measure (`1/2<s≤1`), and infinite rational spikes
(`s≤1/2`).

There is a sharper cancellation consequence: a locally finite
Lebesgue-absolutely-continuous counterterm cannot turn physical `μ_s`
into a locally finite signed measure. The countable ratio atoms carry
infinite mass on every interval, while any such counterterm assigns zero
to that countable support and finite total variation on compact sets.
Renormalization must therefore act on the dense atomic component itself
or exist only distributionally, before separating a positive wall from
its polar/Gamma completion. This does not show that the actual completed
counterterm is absolutely continuous at the wall.

The safe-chamber factorization and its nonnegative real part are proved
unconditionally in `ThetaCuspWallRatioSpectralFactor.lean` and imported
into the RHTower umbrella. The local-infinite-mass threshold is a
dependency-closed paper proof, not yet Lean-closed. Meromorphically
continuing the *spectral formula* gives a nonnegative square at real
`s<1` away from the pole, but does not continue the positive atomic
measure as a locally finite measure. Thus neither pointwise positivity
nor naive atomic positivity supplies the missing signed completed-current
law. The viable object would have to retain prime--polar--Gamma finite
parts and an oriented aperture derivative before taking a scalar shadow;
that source-level construction remains open. This is a route-class
obstruction for the leading wall observable, not a no-go for CLG/TTF as
a whole or an RH theorem. External priority of the exact theta-wall
application remains unaudited.

The same proof gives a **boundary-layer law** rather than only a pointwise
Thomae readout. Fix a reduced rational `e^(2b₀)=p/q` and real `x`. Along
`b(v)=b₀+δ(v)x`, each resonant pair has

```text
c_(qk,pk)(b(v)+iv)
   = 2πpq k² δ(v) (1+2ix+o(1)).
```

The shifted-norm tail bound is uniform for `b` in a compact neighborhood of
`b₀`, so finite-pair passage yields

```text
lim_(v↑R) δ(v)^α/log(1/δ(v)) · J_a(b₀+δ(v)x+iv)
  = K_a ζ(1+2a) (pq)^(-1/2-a) (1+2ix)^(-α).
```

This is a genuinely scale-dependent profile: the pointwise rational spikes
have width `δ`, and their universal complex shape is the Laplace transform
of a positive Gamma density. It predicts a specific positive one-sided
Fourier shape for each isolated leading resonance. It does **not** assert
positivity of their overlapping finite-`δ` interference or of the
RH-equivalent Fourier current.

There is also a sharp weak-limit contrast. The same shifted-norm estimates
bound `δ^α J_a(b+iv)/log(1/δ)` uniformly on every compact real `b`-set.
The displayed pointwise limit is zero outside the countable set
`{(log(p/q))/2 : p,q∈ℕ₊}`. Dominated convergence therefore gives, for
every bounded compactly supported test `φ`,

```text
lim_(v↑R) ∫_ℝ φ(b) · δ(v)^α J_a(b+iv)/log(1/δ(v)) db = 0.
```

The rational spike law is nonzero pointwise at each rational scale but
**zero as a local distribution**. Hence no fixed-frequency Fourier test
supported in a bounded `b`-region can recover its positive pointwise
charge. A Fourier argument has to resolve the shrinking `δ`-wide layers
or exploit a different, subleading quantity.

### Natural-boundary consequence (paper)

The wall is not merely a boundary of this integral representation. The
points `b_(p/q)=(log(p/q))/2` are dense on the real axis. At every one of
them the full-source limit above is a strictly positive real constant,
so `|J_a(b_(p/q)+iv)|→∞` as `v↑π/4`. If the holomorphic germ `J_a`
extended through any point of the upper wall, its extension would be
locally bounded on a disc containing some such rational-ratio wall point,
contradiction. Thus `Im z=π/4` is a natural boundary for the **actual
center-integrated theta current**; evenness/conjugation gives the lower
wall. This inference depends on the full-source tail theorem: finite
heads have only finitely many pair singularities and do not establish a
dense boundary. It rules out contour transport of this current across
the theta strip, but not analytic continuation of `Xi` or other
representations.

### Meaning for the whole route

The wall is a **scale-ratio diffraction readout**: after singular
normalization, only exactly matched quadratic frequencies survive. This
explains why a positive wall charge at `b=0` cannot be the RH producer:
the leading charge is a generic diagonal correlation, while the
RH-equivalent full Fourier sign requires all real `b` and depends on
subleading nonresonant cancellation. The exact source-specific wall law
is stronger than the fixed-cutoff theorem, but it points *away* from
using leading wall positivity to solve RH. The next hard test is whether
the renormalized connected current has a source-derived sign or rigidity
law that survives Fourier transformation. Since each leading rational
spike has width `δ`, the discriminating Fourier experiment is a joint
wall/frequency scaling `δ|ξ|≈1`, not a pointwise wall limit followed by a
Fourier transform; these limits need not commute. A leading asymptotic
alone cannot supply the RH-bearing sign.

There is an immediate obstruction to treating the positive local profiles
as an independently summable partition: their rational amplitudes are
`(pq)^(-s)` with `s=1/2+a<1`, and even the subfamily `q=1` has divergent
total amplitude `Σ_(p≥1)p^(-s)`. Thus isolated-spike Fourier positivity
cannot simply be added over rational ratios. Dense overlap and the
completed source's cancellation are mathematically essential in the
joint scaling. This rejects the first naive attempt to turn the wall
diffraction law into RH.

The full-source theorem is paper-level only; its oscillatory-integral and
tail estimates, and then its limit, remain to formalize in Lean. An initial
external search found adjacent rational/irrational decorrelation work on
the divisor problem, not this literal theta current; priority remains
unaudited. Do not promote to stage 2 until proof and priority audits.

## Coefficient-autocorrelation extension and a hostile countermodel

The same argument does not use the special coefficient `1` until the last
resonance sum. For any bounded **real** sequence `c_n`, let
`h_c(z)=Σ_(n≥1)c_n thetaCuspComplexSourceTerm(z,n)` and form its center
current `J_(c,a)` in the same way. At a reduced rational scale
`e^(2b)=p/q`, the wall limit is

```text
lim_(v↑R) δ(v)^α/log(1/δ(v)) · J_(c,a)(b+iv)
  = K_a (pq)^(-1/2-a) Σ_(k≥1)c_(qk)c_(pk)k^(-1-2a).
```

At irrational scale it is zero. Boundedness of `c_n` preserves the
uniform off-diagonal estimate and the weighted-ℓ² tail passage. Thus
the wall's primitive is a *multiplicative autocorrelation of source
coefficients*, sampled at rational dilation ratios. The actual theta
source is the constant sequence `c_n=1` and gives the preceding zeta
factor. This extension is paper-level, not yet Lean-formalized.

Hostile test: take the positive two-atom source
`h_1+2^(3/4)h_2`. Every nonzero leading wall charge is nonnegative, since
the displayed autocorrelation has nonnegative summands. But the exact
atom scaling law is `h_n(x)=n^(-1/2)h_1(x+log n)`. Hence its Mellin
transform in the convention
`H(s)=∫_ℝ h(x)exp((s-1/2)x)dx` factors as

```text
H(s)=H_1(s)·(1+2^(3/4)2^(-s)).
```

The second factor vanishes at `s₀=3/4+iπ/log 2`, strictly inside
`0<Re s<1` and off `Re s=1/2`. The first-atom archimedean factor is
nonzero there, so this is a genuine new zero introduced by the scale-two
coefficient, not an identically zero transform. Therefore **leading
wall-charge positivity by itself cannot imply critical-line zeros**,
even for positive combinations of the same literal Gaussian-theta
atoms. This does not rule out a theorem using modular completion or
the fully coupled Fourier current: the two-atom source lacks the
functional equation. Its purpose is to falsify the stronger claim that
the new wall law, unaided, is an RH producer.

The Mellin factorization, off-line zero, and nonvanishing first-atom
comparison are unconditional Lean theorems in
`ThetaCuspTwoAtomMellinOffLineCountermodel.lean`, scratch-checked,
direct-file checked, target-built with Lake's `--old` cache, and wired into
`RHTower.lean`. The generalized wall-charge claim remains paper-only.

## All-aperture leading-wall profile is a tail invariant, not a zero invariant

The fixed-aperture four-atom phase-retrieval model leaves open the hope that
**all** apertures and the full boundary-layer shapes recover the needed
zero orientation. A stronger falsifier comes from the real-analytic
zero-engineering theorem in
`../2-fully-proven/theta-compact-critical-strip-zero-engineering.md`.
Write the literal holomorphic theta source as `h` and its real-analytic
perturbation as `g_u=h(1+q_u)`. For each fixed sufficiently large `u`,
`q_u` is entire, is bounded on `|Im z|≤π/4`, and tends to zero
super-Gaussianly as `Re z→+∞`, uniformly on that closed imaginary strip.
The Fourier transform of `g_u` has a prescribed zero `u+iv` with
`0<v<1/2`; `g_u` remains real even, positive and strongly log-concave
on the real axis and preserves the specified finite anchors. It does
not preserve exact Euler coefficients or modular assembly.

Define `J_(g,a)(z)=∫₀∞r sinh(ar)g(r/2+z)g(r/2−z)dr` in the source strip.
**Tail-invariance theorem (paper).** For every `0<a<1/2` and every compact
`B⊂ℝ`, with `α=9/2+a` and `δ(w)=cos(2w)`, the center-mixed currents obey

```text
lim_(w↑π/4) sup_(b∈B)
  |δ(w)^α/log(1/δ(w)) · (J_(g_u,a)(b+iw)−J_(h,a)(b+iw))| = 0.
```

Consequently `g_u` and the actual theta source have **identical leading
wall profiles at every aperture**, including all rational charges,
irrational zero values, and every `b=b₀+δ(w)x` boundary-layer profile,
although one has an off-line Fourier zero. This is a countermodel to any
RH criterion based only on the complete leading wall family and those
real-axis source-shape/finite-anchor properties. It does not refute a
criterion using exact Euler/modular assembly, subleading singular germs,
or the interior signed current.

### Proof of tail invariance

Put `A(w)=δ(w)^α/log(1/δ(w))`, `W_a(r)=r sinh(ar)`, and

```text
N_(b,w)=∫₀∞ W_a(r)|h(r/2+b+iw)|²dr,
N^L_(b,w)=∫₀ᴸ W_a(r)|h(r/2+b+iw)|²dr.
```

The shifted-norm argument in the full-source wall theorem above gives
`sup_(b∈B,w near π/4) A(w)N_(b,w)<∞`. Its additional local consequence is

```text
A(w) · sup_(b∈B)N^L_(b,w) → 0     for each fixed L.
```

Here is the needed bound, without assuming pointwise wall convergence of
the theta series. Expand the two source sums in the bounded `r`-interval.
The top polynomial factor in the diagonal `n=m` is `O(n⁸)`, and Gaussian
damping gives `Σ_n n⁸ exp(−cδ n²)=O(δ^(−9/2))`, uniformly for `b∈B`.
For `n≠m`, the oscillatory phase derivative in `r` is a nonzero fixed
multiple of `(n²−m²)e^r` near the wall. One integration by parts,
including its finite upper boundary term, bounds the pair integral by

```text
C_(B,L) n⁴m⁴ exp(−cδ(n²+m²)) / |n²−m²|.
```

The differentiated damping factor `δ(n²+m²)` is absorbed by weakening
`c`; lower source-polynomial orders have smaller powers. For `n>m≥n/2`,
write `k=n−m`, use `|n²−m²|≥nk` and sum `n⁷/k` over `k≤n`;
for `m<n/2`, sum `m⁴` against the denominator `≳n²`. The result is
`O_(B,L)(δ^(−4)log(1/δ))`. Thus

```text
sup_(b∈B)N^L_(b,w)
  = O_(B,L)(δ^(−9/2)+δ^(−4)log(1/δ)),
```

which becomes `o(A(w)^(-1))` because `a>0`. The same estimates apply at
`-b` and after conjugating the imaginary shift.

Expand `g_u(r/2±z)=h(r/2±z)(1+q_u(r/2±z))`. On `0≤r≤L`, the two
`q_u` factors are bounded; Cauchy--Schwarz makes the normalized
`J_g−J_h` contribution at most a constant times
`√(A N^L_(b,w))√(A N^L_(-b,w))→0`, uniformly for `b∈B`.
On `r>L`, the supremum of
`|q_u(r/2±b±iw)|` tends to zero as `L→∞`, uniformly for `b∈B` and
`w` near the wall. The global shifted-norm bound makes this tail
contribution at most `o_L(1)·O_B(1)`. First let `w↑π/4`, then `L→∞`.
This proves the displayed uniform theorem.

The analytic zero-engineering construction is dependency-closed on paper,
but its zero-placement theorem and the present local shifted-norm escape
are not yet Lean-closed. The full-source analytic wall identification is
also paper-level. External novelty priority is unaudited. The route-level
conclusion is precise: leading wall data classify a tail equivalence
class, while off-line zero placement can change inside that class.

### Positive survivor: an explicit relative core response at the next scale

The leading-wall no-go does not erase the entire singular germ. Suppose
more generally that `q` is entire, respects real conjugation, and `q`
and its first real derivative decay faster than `exp(−c|Re z|)` for
every fixed `c>0`, uniformly on `|Im z|≤π/4`; put `g=h(1+q)`.
At the zero ratio `b=0`, the relative current has the following
source-specific subleading limit (paper proof):

```text
lim_(w↑π/4) δ(w)^(9/2) [J_(g,a)(iw)−J_(h,a)(iw)]
 = C_core ∫₀∞ r sinh(ar)
       (|1+q(r/2+iπ/4)|²−1) dr,
C_core = Γ(9/2)/(2√(2π)) > 0.
```

The integral is finite under the stated decay. No sign is asserted for
the core response; it is an oriented relative observable, not an RH
criterion. In particular the all-aperture leading profile can agree
while the next singular scale reads information the leading tail misses.

For the proof, at `b=0` real conjugation gives
`J_(g,a)(iw)−J_(h,a)(iw)=∫W_a(r)|h(r/2+iw)|²M_q(r,w)dr`, where
`M_q=|1+q|²−1`. Expand the literal theta source into ordered atoms.
The leading diagonal term is

```text
(2π)^4 e^(9r/2) Σ_(n≥1) n⁸ exp(−2πδ e^r n²) · M_q(r,w).
```

The standard Gaussian Riemann-sum limit
`t^(9/2)Σ_(n≥1)n⁸e^(−tn²)→Γ(9/2)/2` makes
`δ^(9/2)` times this expression converge pointwise to
`C_core M_q(r,π/4)`; the powers of `e^r` cancel exactly. The scaled
diagonal is uniformly bounded in `r`, so the rapid decay of `M_q`
licenses dominated convergence against `r sinh(ar)dr`. Lower-degree
source-polynomial terms vanish at this scale. For `n≠m`, the same
one-integration-by-parts bound above is now global because `M_q` and
its derivative suppress the large-`r` tail; summing it gives
`O(δ^(−4)log(1/δ))=o(δ^(−9/2))`. Hence no off-diagonal contribution
survives. The formula is a relative subtraction and does not assert
that the unperturbed current has a standalone `δ^(−9/2)` coefficient.

This identifies a concrete next experiment: determine whether the
literal completed source supplies a canonical relative comparator and
a sign law for such core-sensitive finite parts. The present formula
does not construct either. It and the preceding tail-invariance theorem
are paper-only; source-specific Lean estimates and external priority
audit remain open.
