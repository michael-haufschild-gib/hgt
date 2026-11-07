# Height and homotopy theory of arithmetic counts

This programme seeks arithmetic nonnegativity from local heights and cancellation
from topology. It asks for the structures supplied by a variety over a finite
field: an addition law, a fixed-point formula, and a polarization. Its motivating
specification is §2.11 of
[the second obstacles report](../../../docs/reports/review-0711/obstacles-summary.md).

The namespace is `GaloisForLFunctions.HeightHomotopyArithmeticCounts`;
the programme umbrella is `HeightHomotopyArithmeticCounts.lean`.

## Motivation and position

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
map or chain homotopy. Fixed-point indices must be bounded by a geometric
argument, not by the desired bound on the Euler characteristic.

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

The first proved analytic pillar is the radial chord identity. For a unit
complex number `w`,

`|1−rw|² = r|1−w|²+(1−r)²`.

Consequently the logarithmic kernel has a universal first-order correction
`−log(r)/2` and a nonnegative remainder
`R = log(1+(1−r)²/(r|1−w|²))/2`, bounded by
`(1−r)²/(2r|1−w|²)` for `r>0`, `w≠1`.
[`RadialLogarithmicKernel.lean`](RadialLogarithmicKernel.lean) proves the
identity and bound. These are estimates on the actual circle kernel,
independent of the Weil form. They isolate the geometric cost of regularizing
distinct torsion points; coincident points require a separate diagonal term.

[`FiniteRadiusTorsionEnergy.lean`](FiniteRadiusTorsionEnergy.lean) applies
this identity to the existing primitive torsion orbits. Writing `T°_r` for
energy with coincident pairs removed, `c(m,n)` for their number, and
`C(m,n)=Σ_{z≠w}|z−w|⁻²`, it proves

`T°_r(m,n)+c(m,n)log(r)/2 = −I(m,n)−R_r(m,n)`,

`0 ≤ R_r(m,n) ≤ (1−r)² C(m,n)/(2r)`.

For a self-orbit, the removed energy is exactly `−φ(n)log|1−r|`.
For any finite signed pairing, the absolute remainder is bounded by the
same radial factor times `Σ |a(m,n)| C(m,n)`. This is a finite-radius
certificate, stronger than a boundary-limit identity. It provides no sign
for the renormalized pairing and leaves diagonal payment open.

[`ConductorControlledRegularization.lean`](ConductorControlledRegularization.lean)
removes the separation constant from this certificate:

`C(m,n) ≤ (mn)² c(m,n)`.

Here `c(m,n)=φ(m)φ(n)` for `m≠n`, and
`c(n,n)=φ(n)(φ(n)−1)`. The proof uses a vanishing geometric sum to separate
distinct torsion points, then sums the pointwise estimate. Thus

`|Σ a(m,n)(T°_r(m,n)+c(m,n)log(r)/2+I(m,n))|`
`≤ (1−r)²/(2r) Σ |a(m,n)|(mn)²c(m,n)`.

This is uniform in the finite conductors with an explicit polynomial cost.
Neither this bound nor its quadratic radial rate pays for the divergent diagonal.

[`TorsionChordEnergy.lean`](TorsionChordEnergy.lean) proves the classical exact
energy of the nontrivial `L`-th roots of unity:

`Σ_{u^L=1, u≠1} |1−u|⁻² = (L²−1)/12`, for `L≥1`.

The proof uses the first two logarithmic derivatives of
`1+X+⋯+X^(L−1)` at `1`.
[`SharpTorsionChordBounds.lean`](SharpTorsionChordBounds.lean) applies this
identity to the actual primitive orbits. Each row of distinct ratios embeds
in the nontrivial roots of order `lcm(m,n)`, giving

`C(m,n) ≤ min(φ(m),φ(n)) (lcm(m,n)²−1)/12`.

For a self-orbit this bounds the radial remainder by
`(1−r)²φ(n)(n²−1)/(24r)`. The arithmetic spacing scale can therefore cancel
the quadratic conductor factor; a fixed-radius separation estimate alone
does not exhibit this cancellation.

[`UniformSpacingDiagonal.lean`](UniformSpacingDiagonal.lean) makes that
cancellation uniform over all positive conductors. At the existing arithmetic
spacing radius `r=exp(−2ε/n)`, `ε>0`, it proves

`0 ≤ R_r(n,n) ≤ φ(n) ε² exp(2ε)/6`,

`|T_r(n,n)+φ(n)log(1−r)+I(n,n)| ≤ φ(n) max(ε, ε² exp(2ε)/6)`.

For the actual twisted energy and scalar counterterm, the stronger certificate is

`|twistedEnergy(r,n,n)+log(2ε)−tameDifferent(n)|`
`≤ max(3ε, ε² exp(2ε)/6)`.

The same modulus bounds every finite diagonal quadratic form by its squared
coefficient norm, independently of the support. Thus the known pointwise
diagonal limit has a conductor-uniform quantitative form. Mixed-conductor
control and payment of the removed self-energy remain separate questions;
the indefinite spacing limit is not an arithmetic height.

## Mechanisms and tools

The height mechanism is

`local arithmetic data → product formula → nonnegative naive height
→ controlled parallelogram defect → quadratic Tate limit`.

The topology mechanism is

`prime-star nerve → natural self-map → homotopy invariance
→ local fixed-point indices → cancellation bound`.

The two mechanisms should meet in a quadratic refinement whose signature reads
primitive geometry. Geodesic renormalization of horocycles may compare this
refinement with modular cusp counts; that comparison itself requires proof.

Tools to build are a nonnegative arithmetic function on correspondences,
regularized torsion self-energy at finite radius, an approximate parallelogram
for a log-count, a self-map homotopic to the identity with controlled fixed-point
indices, a cusp realization of the nerve, and its polarized quadratic refinement.

## Questions and open research topics

1. What group carries the probes, or what replaces a group?
2. What arithmetic addition law produces a quasi-parallelogram over `ℤ`?
3. Which local term absorbs torsion self-energy, with what normalization?
4. Which natural map localizes the nerve Euler characteristic to a fixed set
   of square-root size?
5. How can linear Betti mass coexist with square-root Euler cancellation,
   and which differential or action explains that cancellation?
6. Can the nerve be realized in the modular surface with the required modular
   action on cells?
7. Do Hecke correspondences generate the ample cone of the refinement?

These are open construction and estimate problems. No square-root upper bound
for `M(N)`, global arithmetic height, or nerve localization is asserted here.

## Calibration and traps

The height construction must recover Hasse–Weil for curves without taking a
positive form as input. It must fail on Golden and on shifted data with
nonnegative Tate coefficients. The prime complex over `𝔽_q[T]` tests the
fixed-point language; elliptic and hyperelliptic curves test arithmetic heights;
the complex fake and genus-two graph test false positivity mechanisms.

The integer construction must use torsion through `ℤ ⊂ ℝ`, detect a source
beyond its two degrees, and have infinite rank in the limit. A finite-dimensional
norm realization on a window cannot supply it. Ordinary matchings cannot
explain away genuine homology. Natural Frobenius candidates and connected-link
arguments have existing obstructions. A modular-surface analogy must account
for the distinction between cuspidal and Eisenstein contributions.

## Success and contribution criteria

Success means constructing all six named tools, answering the seven questions,
and verifying the curve and countermodel calibrations. It includes the stated
Betti and square-root lower laws, not only an Euler-characteristic identity.
A height defined through `Q`, a conditional height principle, or a reformulation
of RH is not completion.

Contributions must prove unconditional statements about explicitly constructed
arithmetic or topological objects, improve a named foundation or resolve an
open mechanism, and survive Lean's kernel and transitive axiom audit. A no-go
must extract its strongest nontrivial positive statement. Paper proofs and
conjectures must remain distinguishable from formalized theorems.
