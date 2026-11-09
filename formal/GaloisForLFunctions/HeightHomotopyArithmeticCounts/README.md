# Height and homotopy theory of arithmetic counts

This programme seeks arithmetic nonnegativity from local heights and cancellation
from topology. It asks for the structures supplied by a variety over a finite
field: an addition law, a fixed-point formula, and a polarization. Its motivating
specification is §2.11 of
[the second obstacles report](../../../docs/reports/review-0711/obstacles-summary.md).

The namespace is `GaloisForLFunctions.HeightHomotopyArithmeticCounts`;
the programme umbrella is `HeightHomotopyArithmeticCounts.lean`.

## Motivation and position

The shared quantitative target is **signed cancellation of the actual local
indices at the square-root scale**. [RIAC](../RenormalizedIntersectionArithmeticCounts/README.md)
constructs their sum `Σ_p index_p(N)=1−M(N)`. Sections, heights and topology
must provide a mechanism controlling that sum; the localization identity
and the size of individual contributions do not provide the cancellation.

An integer probe should carry local contributions whose product formula yields
a nonnegative height. An addition law should make its asymptotic height
quadratic. Independently, the reduced Euler characteristic of the nerve of prime stars
is `−M(N)`: its small expected size concerns cancellation among linearly many
homology classes. A fixed-point construction could explain that cancellation
without pretending those classes disappear.

[Arithmetic orientation geometry](../ArithmeticOrientationGeometry/README.md)
provides arithmetic correspondences and orientation;
[arithmetic effectivity theory](../ArithmeticEffectivityTheory/README.md)
provides Tate limits, height principles and the torsion-energy model;
[Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md) provides
polar surfaces and primitive-sign receivers. This programme seeks the arithmetic
objects needed by those principles. Its companion
[effective scaling geometry](../EffectiveScalingGeometry/README.md) seeks
sections, divisors and geometric effectivity. Horocycle and counting-holography
programmes provide geometric comparison targets, not a presumed positive count.

## Objects and language

| Object | Intended role |
|---|---|
| Integer probe or window correspondence | Argument of the arithmetic height |
| Local height `λ_v`, `deg p = log p` | Contribution of each place |
| Naive height and Tate limit | Finite arithmetic count and its quadratic limit |
| Torsion cycle and resultant | Finite-radius self-energy with arithmetic normalization |
| Arakelov bundle `⊕𝒪(½ log m)` and theta `h⁰` | Existing arithmetic section-count models |
| Prime complex and nerve of prime stars | Simplicial models for Möbius cancellation |
| Farey points and closed horocycles | Candidate realization in cusp geometry |
| Polar surface and Hecke similitude | Signature and scaling of a quadratic refinement |

A local height must come from arithmetic data, not a decomposition of `Q`
chosen after its sign is known. A Tate limit requires a proved growth law and
proved error control. “Homotopic to the identity” must be realized by an actual
map or chain homotopy. Control of the signed local-index sum must come from an independent geometric
or arithmetic argument; the desired Euler-characteristic bound is not an input.

## Foundational pillars

The reports identify these existing foundations; they are not new claims here.

1. Manin's construction gives the elliptic calibration from heights; Stepanov
   supplies a hyperelliptic calibration by a different arithmetic mechanism.
2. The nerve Euler characteristic reads the Möbius sum, while the prime complex
   has Betti mass of order `N`. A homotopy reduction cannot remove that mass.
3. The expected square-root cancellation has a matching square-root lower
   obstruction infinitely often. Any localization estimate must respect it.
4. Golden, complex fakes, and graph models distinguish counts from spectral
   or functional-equation data.

New pillars sought are an actual arithmetic addition law, finite-radius
self-energy regularization, a controlled approximate parallelogram, a
fixed-point localization theorem for a natural nerve action, and a quadratic
refinement with arithmetic polarization. Their existence is not assumed.

RIAC's [integral section theory](../RenormalizedIntersectionArithmeticCounts/IntegralSectionHeight.lean)
now supplies an actual quotient addition law and minimum-section height.
For squarefree count `q` and charge `k=qa+r`, its minimum is
`k²/q+r(q−r)/q`; an exact nonpositive parallelogram defect yields Tate
height `k²/q`. On the original arithmetic gluing class this is squared
transverse distance. The actual minimizer count is `binomial(q,r)`, whose
logarithm has zero Tate limit. RIAC's
[full Gaussian section sum](../RenormalizedIntersectionArithmeticCounts/GaussianSectionHeight.lean)
supplies a genuine log-count height. Its
[finite-height comparison](../RenormalizedIntersectionArithmeticCounts/GaussianSectionPositivity.lean)
is `tk²/q≤H_N(c,t)≤tE_N(c)`, with error at most `tq/4` and actual addition
defect in `[-tq,tq/2]`. Poisson summation and paired integral sections
prove both signs without a height assumption. Its Tate limit is `tk²/q`;
the full real-parameter limit `H_N(c,t)/t` as `t→∞` recovers `E_N(c)`.
On the original gluing class these yield `tD_N²` and `|1−M(N)|`.
The [uniform finite-rate theorem](../RenormalizedIntersectionArithmeticCounts/GaussianSectionUniformity.lean)
chooses `a_N=π+2log(4(N+1))` and `t_N=π²/(2a_N)` using only the conductor.
Every class satisfies `0≤H_N(c,t_N)−t_N k²/q≤2/(N+1)`; on the gluing class,
`0≤H_N([b],t_N)/t_N−D_N²≤4a_N/(π²(N+1))`. Integer coding of the dual lattice
and a quantitative Poisson bound prove this directly from actual counts.
The domain is the rank-one divisor quotient. A full Hecke comparison and
the independent conductor-height bound needed for signed cancellation
remain open.

### Finite-radius torsion energy and arithmetic spacing

For a unit complex number `w`, the actual radial chord identity is

`|1−rw|² = r|1−w|²+(1−r)²`.

It separates the logarithmic kernel into its boundary value, the universal
correction `−log(r)/2`, and a nonnegative remainder. For primitive torsion
orbits of orders `m,n`, let `T°_r` exclude coincident pairs, let `c(m,n)` count
distinct ordered pairs, and put `C(m,n)=Σ_{z≠w}|z−w|⁻²`. Then

`T°_r(m,n)+c(m,n)log(r)/2 = −I(m,n)−R_r(m,n)`,

`0≤R_r(m,n)≤(1−r)² C(m,n)/(2r)`.

For a self-orbit, the removed energy is exactly `−φ(n)log|1−r|`.
[FiniteRadiusTorsionEnergy.lean](FiniteRadiusTorsionEnergy.lean) proves the
identity and its bound for arbitrary signed finite pairings. This isolates
self-energy; it supplies no sign after subtraction and no payment for that term.

The geometric cost has an exact full-root calibration:

`Σ_{u^L=1, u≠1}|1−u|⁻²=(L²−1)/12`, for `L≥1`.

The proof uses two logarithmic derivatives of `1+X+⋯+X^(L−1)` at one.
Distinct ratios in each primitive-orbit row embed in the nontrivial roots of
order `lcm(m,n)`. Thus

`C(m,n)≤min(φ(m),φ(n))(lcm(m,n)²−1)/12`.

[SharpTorsionChordBounds.lean](SharpTorsionChordBounds.lean) proves this bound
for the original orbit sum. It improves the direct separation estimate
`C(m,n)≤(mn)²c(m,n)` and exposes cancellation of conductor factors at an
arithmetic spacing scale.

The existing spacing radius is `rε(m,n)=exp(−ε(1/m+1/n))`.
On the diagonal, `rε(n,n)=exp(−2ε/n)` and the remainder satisfies

`R_r(n,n)≤φ(n)ε²exp(2ε)/6`.

For the actual gcd-twisted energy and scalar counterterm,
[UniformSpacingDiagonal.lean](UniformSpacingDiagonal.lean) proves

`|twistedEnergy(r,n,n)+log(2ε)−tameDifferent(n)|`
`≤max(3ε,ε²exp(2ε)/6)`.

The same modulus bounds every finite diagonal quadratic form by its squared
coefficient norm, independently of the conductors. Uniform diagonal convergence
does not imply uniform control of mixed entries.

For arbitrary positive conductors, the remainder also has an exact arithmetic
representation. Put `F(u)=log u−log(1−exp(−u))`. Double Möbius inversion of
full groups of roots gives

`T_exp(−t)(m,n)+[m=n]φ(n)log t+I(m,n)`
`=Σ_{d|m,e|n} μ(m/d)μ(n/e)gcd(d,e)F(t lcm(d,e))`.

[PrimitiveTorsionDivisorFormula.lean](PrimitiveTorsionDivisorFormula.lean)
proves this identity for the original energy. Its logarithmic divergence is
exactly the common primitive-root multiplicity; the constant term is the
existing orbit intersection. The formula reduces mixed-conductor control to
an explicit finite arithmetic remainder.
[PrimitiveSpacingRemainder.lean](PrimitiveSpacingRemainder.lean) controls it by

`|R(t,m,n)|≤(1+1/α)τ(m)τ(n)gcd(m,n)(t lcm(m,n))^α`, for `0<α≤1`.

The scalar input is `0≤F(u)≤log(1+u)` and hence
`F(u)≤(1+1/α)u^α`. The bound retains the gcd factor needed for summing mixed
entries. The arithmetic summation mechanism is now formalized in
[WeightedGcdForm.lean](WeightedGcdForm.lean): for every `δ>0`,

`Σ_{m,n∈S} gcd(m,n)x_m x_n/√(mn) ≤ Cδ Σ_{n∈S} n^δ x_n²`

on every finite positive support. The totient divisor-square identity,
Cauchy–Schwarz on multiples and subpolynomial divisor growth prove the bound.
Write the actual entrywise error as

`Bε(m,n)=twistedEnergy(rε(m,n),m,n)+weilPrimeKernel(m,n)`
`+[m=n](log(2ε)−tameDifferent(n))`.

[SpacingErrorIdentity.lean](SpacingErrorIdentity.lean) identifies the actual
entrywise error with `gcdTwist(m,n)R(ε(1/m+1/n),m,n)/√(mn)` and proves its
finite quadratic-form identity. For `0<α≤1` and every `κ>0`,
[SpacingKernelMajorant.lean](SpacingKernelMajorant.lean) proves

`|Bε(m,n)|≤Cα,κ ε^α gcd(m,n)(mn)^(α+2κ)/√(mn)`.

The gcd twist costs at most `τ(gcd(m,n))`; subpolynomial divisor growth
absorbs all three divisor counts. Combining this envelope with the gcd estimate
gives the full comparison in
[WeightedSpacingConvergence.lean](WeightedSpacingConvergence.lean). For every
`0<α≤1` and `δ>2α`, one constant satisfies

`Σ_{m,n∈S}|x_m x_n Bε(m,n)|≤Cδ,α ε^α Σ_{n∈S} n^δ x_n²`.

Consequently the actual scalar-renormalized spacing form converges uniformly
on finite positively weighted unit balls. Every `δ>0` is admitted, for example
with `α=min(δ/8,1)`. The error bound holds on arbitrary finite positive supports
and retains the original product spacing radius. It supplies no sign for the
limiting form.

[InfiniteSpacingConvergence.lean](InfiniteSpacingConvergence.lean) passes this
estimate to infinite probes satisfying `Σ n^δ x_n²<∞`. The entire absolute
mixed-error series is summable, satisfies the same power bound, and tends to
zero as `ε→0+`. This controls the error independently of a truncation.
The limiting kernel has a separate uniform bound in
[WeightedTorsionLimit.lean](WeightedTorsionLimit.lean). For positive conductors,

`P(m,n)≤log(mn)gcd(m,n)/√(mn)`.

Absorbing the logarithm into an arbitrarily small positive power and applying
the weighted gcd estimate yields

`Σ_{m,n∈S}|x_m x_n L(m,n)|≤Cδ Σ_{n∈S}n^δ x_n²`,

where `L(m,n)=−P(m,n)+[m=n]tameDifferent(n)`. The diagonal uses
`0≤tameDifferent(n)≤log n`. [InfiniteTorsionForms.lean](InfiniteTorsionForms.lean) passes this bound to the
full absolutely convergent series. It also proves absolute convergence of the
original scalar-renormalized series and the exact identity

`Rε(x,x)−L(x,x)=Σ_{m,n}x_m x_n Bε(m,n)`.

For `0<α≤1`, `2α<δ`, the same bound
`|Rε(x,x)−L(x,x)|≤Cδ,α ε^α Σ n^δ x_n²` holds on every infinite probe of finite
weighted square mass. Mixed-probe absolute summability follows by comparison
with `|x|+|y|`. [WeightedProbeSpace.lean](WeightedProbeSpace.lean) constructs the Hilbert carrier
through coordinates `u_k=(k+1)^(δ/2)x_(k+1)`. Every finite-mass arithmetic sequence
has a unique representative; its norm squared is exactly `Σ n^δx_n²`.
Finite conductor truncations converge, and the normalized conductor atoms form
an infinite orthonormal family. [KernelHilbertCompletion.lean](KernelHilbertCompletion.lean) converts a proved
finite absolute kernel bound `CΣ n^δx_n²` into a continuous bilinear form with
bound `4C‖x‖δ‖y‖δ`, retaining the original series and kernel symmetry.
[WeightedTorsionOperators.lean](WeightedTorsionOperators.lean) constructs the
three actual continuous symmetric forms on this common infinite-dimensional
space. Their original pair series are absolutely summable, the raw form obeys
`Tε(x,x)≥0`, and the normalization is exactly

`Rε(x,y)=Tε(x,y)+log(2ε)Σ_n x_ny_n`.

For `0<α≤1` and `2α<δ`,

`‖Rε−L‖op≤Cδ,α ε^α`.

Thus the scalar-renormalized forms converge in operator norm as `ε→0+`.
The counterterm uses the ordinary coefficient pairing; the weighted norm
controls convergence. This coefficient addition law supplies neither the
required arithmetic product formula nor a nonnegative renormalized height.

### The mixed prime row and its sharp conductor weight

For a prime `p`, put `r=rε(1,p)` and let `Eε(p)` be the difference between the
actual twisted energy at `(1,p)` and its limit. The cyclotomic polynomial gives

`Eε(p)=(log p−log(1+r+⋯+r^(p−1)))/√p`.

The geometric sum lies between one and `p`, and is at most
`1/(1−exp(−ε))`. Consequently

`0≤Eε(p)≤log(p)/√p`,
`Eε(p)≥(log p−log(1/(1−exp(−ε))))/√p`.

For every fixed `ε>0`, the exact square-summability threshold is

`Σ_p Eε(p)² p^(−δ)<∞ ⇔ δ>0`.

At zero weight, finite prime-row square sums are unbounded: eventually the
summands dominate `1/p`. For every positive weight, the logarithmic majorant
is summable and dominated convergence gives

`lim_{ε→0+} Σ_p Eε(p)² p^(−δ)=0`.

[PrimeSpacingRow.lean](PrimeSpacingRow.lean) proves the identity, sharp threshold
and weighted convergence for the actual energy. Together with the full weighted
estimate above, this distinguishes fixed-conductor
convergence from uniform control on arithmetic probe spaces. Positive conductor
weights control the full mixed error; nonnegative renormalized heights still
require a separate arithmetic mechanism.

### Isolated components, the connected core and signed localization

Every prime `N/2<p≤N` is an isolated vertex of the actual prime complex, fixed
individually by every self-map homotopic to the identity. Eventually at least
`N/(4 log N)` such points are forced; their count divided by `√N` tends to
infinity. [PrimeFixedPointObstruction.lean](PrimeFixedPointObstruction.lean)
therefore rules out the proposed literal fixed set of square-root cardinality,
even without naturality of the maps. Signed fixed-point cancellation remains
a separate possibility.

The obstruction has an exact positive replacement. At `N≥4`, all other points
form one connected core containing prime two, preserved by identity-homotopic
maps. It consists of faces with vertices satisfying `2p≤N`. Its reduced Euler
characteristic is

`−M(N)−#{p prime : N/2<p≤N}`.

[PrimeCoreEuler.lean](PrimeCoreEuler.lean) proves the component classification
and correction. [PrimeCoreBouquet.lean](PrimeCoreBouquet.lean) identifies the
core as the bouquet of positive-dimensional spheres labelled by odd squarefree
composite integers `m`, in dimension `ω(m)−1`. Only the prime-labelled
zero-spheres disappear. The sought square-root estimate concerns cancellation
between this core and the isolated-prime contribution.

The companion [effective scaling geometry programme](../EffectiveScalingGeometry/README.md)
constructs actual prime-height homology and its inclusion maps. Complex
Dirichlet weights preserve that persistence by a natural chain gauge. Integral
prime weights instead produce explicit free-to-parity transitions with no
natural splitting. These structures refine the arithmetic object but supply
no signed Euler bound. Analytic completion, integral relations and signed
actions require their own comparison estimates.

## Mechanisms and tools

The height mechanism is

`local arithmetic data → product formula → nonnegative naive height
→ controlled parallelogram defect → quadratic Tate limit`.

The topology mechanism is

`prime-star nerve → isolated-prime/core decomposition → natural action
→ signed local indices → cancellation against the component contribution`.

The two mechanisms should meet in a quadratic refinement whose signature reads
primitive geometry. Geodesic renormalization of horocycles may compare this
refinement with modular cusp counts; that comparison itself requires proof.

Tools to build are a nonnegative arithmetic function on correspondences,
regularized torsion self-energy at finite radius, an approximate parallelogram
for a log-count, an action with controlled signed fixed-point contributions,
a cusp realization of the nerve, and its polarized quadratic refinement.

### Compactness of the actual torsion limit

For `0<β<δ`, the coefficient-preserving inclusion `Hδ→Hβ` multiplies normalized
conductor coordinates by `n^((β−δ)/2)` and is compact. The original pair series
factors through this inclusion in both variables. Consequently its Riesz
representative is a compact self-adjoint operator on every `Hδ`, `δ>0`.
[WeightedTorsionCompactness.lean](WeightedTorsionCompactness.lean) retains the
actual arithmetic series in this representation. The normalized basis has
coefficient `n^(−δ/2)` at conductor `n`; rescaled conductor atoms recover exact
original kernel entries by [WeightedProbeAtoms.lean](WeightedProbeAtoms.lean).
[SpacingFiniteConstraints.lean](SpacingFiniteConstraints.lean) constructs definite
subspaces of both signs in every finite dimension. Every finite family of linear
constraints leaves both signs, so no finite-rank bilinear correction makes this
form semidefinite.

[TorsionHilbertSchmidtBoundary.lean](TorsionHilbertSchmidtBoundary.lean) proves
that this operator is Hilbert–Schmidt exactly for `δ>1/2`, with squared norm

`2(Σ_(m≥1) m^(−2δ))(Σ_(t≥1) Λ(t)²/t^(1+δ)) + Σ_(n≥1) d(n)²/n^(2δ)`.

Divisor-pair reindexing gives the exact square mass; even-conductor diagonals
force the sharp converse.

## Questions and open research topics

1. What group carries the probes, or what replaces a group?
2. What arithmetic addition law produces a quasi-parallelogram over `ℤ`?
3. Which local term absorbs torsion self-energy, with what normalization?
4. The literal square-root-sized fixed set is impossible for maps homotopic
   to the identity. Which signed or relative localization replaces it and
   accounts for the isolated-prime contribution?
5. How can linear Betti mass coexist with square-root Euler cancellation,
   and which differential or action explains that cancellation?
6. Can the nerve be realized in the modular surface with the required modular
   action on cells?
7. Do Hecke correspondences generate the ample cone of the refinement?

The negative answer to the literal version of question 4 is proved; its
replacement and the other construction problems remain open. No square-root
upper bound for `M(N)`, global arithmetic height, or signed nerve localization
is asserted here.

## Calibration and traps

The height construction must recover Hasse–Weil for curves without taking a
positive form as input. It must fail on Golden and on shifted data with
nonnegative Tate coefficients. The prime complex over `𝔽_q[T]` tests the
fixed-point language; elliptic and hyperelliptic curves test arithmetic heights;
the complex fake and genus-two graph test false positivity mechanisms.

RIAC's [integral discriminant cover](../../../docs/drafts/pipeline/3-formalized/riac-integral-discriminant-cover.md)
supplies an actual coefficient family over `ℤ`, with independent finite-field
counts and a pointwise identification of signed arithmetic fibres. This
calibrates the counting language; it does not bound the integer gluing height
or the local-index sum.

The integer construction must use torsion through `ℤ ⊂ ℝ`, detect a source
beyond its two degrees, and have infinite rank in the limit. A finite-dimensional
norm realization on a window cannot supply it. Ordinary matchings cannot
explain away genuine homology. Natural Frobenius candidates and connected-link
arguments have existing obstructions. A modular-surface analogy must account
for the distinction between cuspidal and Eisenstein contributions.

## Success and contribution criteria

Success means resolving all six named tools, answering the seven questions,
and verifying the curve and countermodel calibrations. It includes the stated
Betti and square-root lower laws, not only an Euler-characteristic identity.
A replacement for the refuted literal fixed-set tool must retain the exact
component correction and prove the required cancellation estimate.
A height defined through `Q`, a conditional height principle, or a reformulation
of RH is not completion.

Contributions must prove unconditional statements about explicitly constructed
arithmetic or topological objects, improve a named foundation or resolve an
open mechanism, and survive Lean's kernel and transitive axiom audit. A no-go
must extract its strongest nontrivial positive statement. Paper proofs and
conjectures must remain distinguishable from formalized theorems.
