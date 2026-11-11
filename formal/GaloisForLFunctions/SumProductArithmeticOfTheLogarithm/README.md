# Sum-product arithmetic of the logarithm

Namespace `GaloisForLFunctions.SumProductArithmeticOfTheLogarithm`;
umbrella [`SumProductArithmeticOfTheLogarithm.lean`](../SumProductArithmeticOfTheLogarithm.lean).

## 1. Motivation

The phase `φ_t(n)=t log n` carries two structures on the same integers.
Multiplication becomes addition of phases; translation changes the phase through
a smooth, curved function. This field studies how these structures constrain
one another at a fixed height, keeping the integer windings discarded on passing
to the circle. Its quantitative object is the number of actual integer products
that nearly coincide at a prescribed logarithmic resolution.

The RH motivation is a missing arithmetic constraint on prime alignment.
Multiplicativity alone permits alignment, and every fixed finite set of primes
returns arbitrarily close to alignment at unbounded heights. Translation,
integer gaps, carries and the prime weights must supply additional information.
The programme originates in §2.9 of the
[Obstacles summary](../../../docs/reports/review-0711/obstacles-summary.md).

The core seeks this information through counts and arithmetic identities,
without assuming the sign of a quadratic form or using an operator spectrum.
Exact identities are a starting point: the existing cut calculus annihilates
zero modes too. A new constraint must bound a count, phase concentration or
carry distribution that those identities leave undetermined.

Two related questions organize the field. How rigid are logarithmic phases on
the ordinary integers? How closely can another positive multiplicative system
imitate the integer count? The first leads to translated products and fine
energy; the second to factorization, carries and count distance. Their common
input is the discrete arithmetic of actual integers.

## 2. Objects and language

All integer supports below are finite and positive. At cutoff `y`, **smooth**
means that every prime factor is `<y`; **rough** means that every prime factor
is `≥y`. The height `t` of an orbit and the resolution parameter `T` of an
energy count are distinct data.

| Object | Meaning |
|---|---|
| Phase level set | Integers in an interval with `t log n` in a specified arc modulo `2π`; height, interval, arc centre and width all matter. |
| Translated product signature | Readings `∏ᵢ(nᵢ+h)` at several integer translations `h`. A mixed collision is equality of all readings, not just one product. |
| Fine multiplicative energy | For `T>0`, `E_T(A,B)=#{(m,p,n,q)∈A×B×A×B : abs(log(mp)−log(nq))≤1/T}`. The diagonal consists of equal products. |
| Winding and carry | An integer `w` in `t log n=θ+2πw+r`, with a chosen small remainder `r`; a carry records the correction between such integer lifts under an arithmetic operation. |
| Reduced ratio height | `H(A)=max({1}∪{m/gcd(m,n) : m,n∈A})`. It measures the largest numerator in the actual reduced ratio set and is unchanged by common integer dilation. |
| First return | Least height `t≥1` satisfying a specified alignment condition. Recurrence gives an upper bound; exclusion below a given height requires a lower bound. |
| Moving jet | A polynomial approximation to `t log n` on a block, with coefficients depending on the block location. Control must survive the whole moving family. |
| Count distance | For a positive-generator Beurling system, `N_B(x)` counts generalized integers with multiplicity and `D_B(x)=N_B(x)−x`. The slope, error scale and generator norms are part of the question. |
| Finite oscillation | The trigonometric leading term associated with a putative finite layer of zeros to the right of the critical line. Its exact dilation annihilator does not by itself give a contradiction. |

A positive-generator system is a free multiplicative monoid on labels whose
norms exceed one. Distinct labels may have the same norm. Integer-norm systems
retain integer gaps and carries; arbitrary real-norm systems need not.

## 3. Mechanisms

**Translation reveals coefficients.** The products `ab` and `(a+1)(b+1)` reveal
`a+b`, hence the unordered pair. For longer tuples, translated products are
values of the monic polynomial `∏ᵢ(X+nᵢ)`. Interpolation converts joint product
data into reconstruction. This is the algebraic source of rigidity.

**Integer gaps turn reconstruction into resolution.** Distinct positive
integer products differ by at least one. Taking logarithms gives separation
at the inverse-product scale. A joint real phase cell can therefore contain only
a bounded number of tuples. To use this on the circle, its winding must also
be retained: many separate real cells can project to the same arc.

**Primitive steps count near-collisions.** A product difference
`mp+h=nq` forces `gcd(m,n)` to divide `h`. After cancelling that gcd, one column
lies in a fixed residue class with an explicit step. Counting quotient labels
and admissible differences gives an incidence bound. Smooth/rough separation
also makes the exact product diagonal unique. Prime restrictions can impose
further coprimality on the difference; recovering their full density is a
separate problem.

**Factorization amplifies count defects.** Two distinct factorizations of the
same norm produce increasingly many factorizations of its powers. If no norm
collides, consecutive integers have disjoint factor supports; cancellation
then turns a missing norm into repeated omissions. These alternatives force a
count discrepancy without an analytic sign argument.

**Carries connect scales.** Floor errors retain information lost in a smooth
count approximation. In a concrete positive model, combining counts at `n`
and `⌊n/2⌋` exposes a ternary digit sum. Averaging its rounding profile leads to
rotation by `log 3` on a circle of length `log 4`; complementary returns control
the average. The pointwise carry problem remains stronger than this average.

## 4. Central questions

| Question | Established boundary | Missing input |
|---|---|---|
| Can multiplication and translation force phase dispersion at one height? | Joint product readings reconstruct tuples; fine real cells have bounded fibres. | Control across winding cells, using actual prime weights. |
| Is smooth × prime energy at its random scale? | Exact diagonal, gcd cancellation, coprime-density refinements and primitive-step envelopes. | Prime-density savings in the off-diagonal count at the required scale. |
| How long can an initial orbit avoid or sustain alignment? | Every fixed finite support recurs; the fixed `log 3/log 4` rotation has polynomial return and exclusion bounds. | Bounds uniform in a growing prime cutoff, with the starting height retained. |
| Can carries contradict a finite right-zero oscillation? | Exact carry identities and signed count excursions exist in a positive model. | A constraint that survives the known zero-mode blindness of linear floor identities. |
| How far must a positive system move to acquire a new right zero? | Nonclassical integer-norm systems have logarithmic count excursions; one positive model has `O(log²x)` error. | Exceptional-zero distance, including arbitrary real norms and finite exceptional zero support. |

## 5. Mathematical foundations

### Joint products and winding occupation

Two translated products determine an unordered pair; `k` distinct translations
determine a multiset of `k` entries. For pairs from `[1,N]`, a real cell of radius
`ε` in both phase coordinates contains at most two ordered pairs when
`2ε(N+1)²<|t|`. Consequently, `M` integers whose phases and successor phases lie
in prescribed arcs require at least `M²/2` pair-winding signatures when
`4ε(N+1)²<|t|`.

This resolution has a sharp scale: the pairs `(n+1,n+4)` and `(n+2,n+3)` have
equal sums and translated products differing by two, with logarithmic gaps of
order at most `n⁻²`. Interpolation alone cannot improve that scale. The winding
bound measures how much integer data an alignment must carry; it does not bound
the total number of available winding signatures.

Sources: [pair reconstruction](ShiftedProductRigidity.lean),
[tuple interpolation](TranslatedTupleReconstruction.lean),
[real cells](LogarithmicCollisionCells.lean),
[winding occupation](WindingOccupancy.lean),
[resolution sharpness](SharpnessOfProductResolution.lean).

### Fine energy and the geometry of reduced ratios

For smooth rows `A` and prime columns `P`, both in `(X,2X]` and separated at the
smoothness cutoff, the energy satisfies

`E_T(A,P) ≤ #A #P + 2 floor(4X²/T) #A²`.

In particular, `T>4X²` leaves exactly the diagonal. For fixed rows of gcd `g`,
each admissible difference has at most `g` column pairs and only multiples of
`g` occur. Summing differences through `L` costs `g floor(L/g)≤L`; no divisor
sum is lost. Keeping coprimality with the reduced row product gives a stronger
finite envelope, though not the desired prime-density law.

For arbitrary positive rows `m,n` and columns in `[1,Z]`, both off-diagonal
orientations at logarithmic width `1/T` obey

`T #C_{m,n} ≤ Z(2Z+m/g+n/g)`, where `g=gcd(m,n)`.

Thus the intrinsic scale is the reduced ratio, rather than an imposed dyadic
row interval. On a support `A`, distinct logarithmic frequencies are separated
by at least `1/H(A)`, and every row-pair cost is at most `2Z(Z+H(A))`.
Common dilation changes neither the logarithmic differences nor `H(A)`.

Sources: [balanced energy](CumulativeSmoothPrimeEnergy.lean),
[coprime difference density](CoprimeSmoothPrimeEnergy.lean),
[rectangular incidence](RectangularProductCollisions.lean),
[primitive steps](PrimitiveProductCollisionCosts.lean),
[reduced ratio height](PrimitiveLogarithmicSeparation.lean).

### Recurrence and its quantitative limits

Every finite positive support `A` aligns to precision `2π/(Q+1)` at a height in
`[L,L(Q+1)^#A]`, for every `L>0` and integer `Q≥1`. There is no last aligned
height. Any eventual exclusion must therefore let the support grow or specify
an initial height window.

For the fixed rotation `α=log 3/log 4`, a complementary return satisfies
`|kα−ℓ−1/2|<1/Q`. Integer separation gives explicit elementary return and
exclusion bounds; the proved two-prime Baker bound improves these to polynomial
orders in precision and index. The constants depend on the fixed scales two
and three. This supplies a quantitative averaging tool, not a uniform
many-prime first-return theorem.

Sources: [finite recurrence](FiniteAlignmentReturns.lean),
[elementary returns](EffectiveLogarithmicHalfTurn.lean),
[discrete exclusion](DiscreteLogarithmicHalfTurnSeparation.lean),
[polynomial returns](PolynomialLogarithmicReturns.lean).

### Count rigidity and a positive test system

A locally finite positive integer-norm system either is the rational-prime
system, has growing multiplicities along powers, or has repeated omissions
forcing a linear count deficit. Hence every nonclassical such system satisfies
`|N_B(n)−n|≥c log n` at arbitrarily large integer thresholds, for some `c>0`.
Count error `o(log n)` at slope one forces a norm-preserving identification of
the generator labels with rational primes.

The complementary construction uses all odd prime labels, an extra label of
norm three, and a label of norm four. Its generalized integers have unique
coordinates `(u,a,b)`, with `u` positive odd and norm `u3^a4^b`. It is
nonclassical and has `N(x)=x+O(log²x)`. Its exact carry law is

`2(N(n)+N(⌊n/2⌋))+s₃(n)=3n`,

where `s₃` is the ternary digit sum. At `n=3^k−1` this forces negative
logarithmic excursions. Its averaged count is sharper: for some fixed `η>0`,

`∫₀ˣ N(t)dt = x²/2 − x log x/(4 log 3) + O(x(log x)^(1−η))`.

The coefficient comes from a complementary rounding profile with average
`1/4`; polynomial return bounds give the error rate. This averaged result does
not close the pointwise gap between logarithmic and quadratic-logarithmic error.

The actual Dirichlet series is
`ζ(s)/((1+2^(−s))(1−3^(−s)))` for `Re s>1`. Its continuation has residue one
and the same zero divisor as `ζ` on `Re s>0`, away from the pole at one.
The construction tests count rigidity and carries; it introduces no new right
zero. Exceptional-zero distance remains a different problem.

Sources: [collision amplification](NormCollisionAmplification.lean),
[count trichotomy](CountDistanceRigidity.lean),
[logarithmic floor](LogarithmicCountFloor.lean),
[positive construction](PositiveNearCountEstimate.lean),
[carry law](PositiveNearCountCarries.lean),
[averaged coefficient](PositiveNearCountExactAverage.lean),
[power rate](PositiveNearCountPowerRate.lean),
[Euler continuation](PositiveNearCountEuler.lean).

For integer-norm Beurling fakes — discrete positive-generator integer-norm
systems other than the rational primes whose cleared zeta continuation across
`Re s>1/2` vanishes at a point `ρ₀≠1` where `ζ(ρ₀)≠0` — every remainder exponent
`β>1/2` in `N_B(x)=Ax+O(x^β)` is realized unconditionally by prime deletions
built from Moreau's necklace identity and short prime intervals. Every fake
exponent satisfies `β≥0`, so the infimum lies unconditionally in `[0,1/2]`;
every fake at `β≤1` omits infinitely many rational primes; every fake at
`β≤1/2` has `A>0`; and every positive-density prime-deletion fake at `β<1` has
a real fake zero `σ_c∈(1/2,1)` dominating the real part of all its fake zeros.
Any zero-free half-plane `Re z>Θ` (`Θ<1`) for `ζ` yields a prime-deletion fake
with `β<1/2` (reaching every `β>1/3` under `RiemannHypothesis`), giving an
unconditional dichotomy between `zetaZeroAbscissa=1` (`AsymptoticAbscissaLaw`)
and sub-`1/2` integer-norm fakes.
Sources: [fake obstructions](IntegerNormFakeObstructions.lean),
[fakes above one-half](IntegerNormFakesAboveOneHalf.lean),
[fakes below one-half](IntegerNormFakesBelowOneHalf.lean).

## 6. Transfer to broader RH research

The arithmetic counts also feed
[TailArithmeticOfThePrimeOrbit](../TailArithmeticOfThePrimeOrbit/README.md).
That transfer uses a positive Fourier majorant and the Montgomery–Vaughan
mean-square inequality, so it belongs to the broader RH programme outside
the restricted arithmetic core.

Let `R(t)=Σ_{m∈A}r_m m^{it}` be a finite smooth head and
`B(t)=Σ_{p∈P}b_p p^{it}` a prime tail with `y≤p≤Y` and `|b_p|≤1`.
Write `R₁=Σ|r_m|`, `R₂=Σ|r_m|²`, `B₂=Σ|b_p|²` and

`C(A,r,Z)=Σ_{m,n∈A}|r_m r_n| Z(2Z+m/gcd(m,n)+n/gcd(m,n))`.

The same invariant controls both arithmetic error and actual normalizing mass:

`C(A,r,Z) ≤ 2Z(Z+H(A))R₁²`,

`∫_{−T}^T |R(U+t)|²dt ≥ (2T−52H(A))R₂`.

For `T≥52H(A)` and `R₂>0`, normalize integration on `[−T,T]` by its actual
head mass: `dμ_U(t)=|R(U+t)|²dt/∫_{−T}^T|R(U+u)|²du`. For every integer
`k≥0`, the tail moment `∫|B(U+t)|^(2k)dμ_U(t)` is at most

`(5π/2)(k! B₂^k + C(A,r,Y^k)(k!)²/(T R₂))`,

uniformly in the interval centre `U`. For `V>0`, dividing by `V^(2k)` bounds
the normalized head mass where `|B|≥V`. Full smooth heads are included; no
dyadic row restriction is needed.

This is a finite quantitative interface: it preserves the arithmetic cost
through normalization. It does not supply a Gaussian limit, a growing
Euler-head limit, or exclusion of every exceptional height.
Source: [normalized arithmetic moments](../TailArithmeticOfThePrimeOrbit/TheNormalizedMomentsRetainTheArithmeticCost.lean).

## 7. Open research topics and tools still needed

**Prime-weighted dispersion at every large height.** A concrete first target is
to find fixed `K>1`, `c>0`, `T₀` such that, for every `t≥T₀` and
`y=(log t)^(2K)`,

`Σ_{p≤y}p^(−1/2)(1−cos(t log p)) ≥ c Σ_{p≤y}p^(−1/2)`.

This remains open here. A density-one result in height does not meet its
quantifiers. The missing tool must connect winding occupation to prime
amplitudes and retain precision as the cutoff grows.

**Fine energy at the random scale.** The incidence envelopes retain integer
cutoffs and reduced ratios. The next question is whether smoothness,
primality and coprime difference density give the missing off-diagonal saving.
An archimedean polynomial method would need to improve an actual count at
the stated resolution, rather than re-express exact reconstruction.

**Moving blocks beyond the polynomial-phase ceiling.** The relevant family
consists of Taylor approximations at moving centres, including regimes where
the required degree exceeds `(log length)²`. A useful estimate must improve
the family bound, retain the original orbit and state its range beyond the
existing Vinogradov–Korobov mechanism.

**Carries against finite oscillation.** Over the integers, a dilation of the
count is an average of translations. What arithmetic constraint can replace
the role of Frobenius? A finite-zero contradiction must use carry information
not already annihilated by exact linear cut identities. This target is
independent of the growing-height dispersion target above.

**Count-distance geometry.** Determine the optimal pointwise distance of a
nonclassical positive integer-norm system, then distinguish that problem from
the distance needed to insert a new right zero. An exceptional-zero statement
must keep positivity of generator multiplicities, integer versus real norms,
and finite versus infinite exceptional zero support explicit.

## 8. Calibration and neighbouring fields

| Neighbour | Interface |
|---|---|
| [PrimeTorusTheory](../PrimeTorusTheory/README.md) | Integer-log separation, finite-time recurrence, non-alignment estimates and word/polynomial-phase ceilings. Translation of the integer argument is the additional structure studied here. |
| [RigidArithmeticOfCuts](../RigidArithmeticOfCuts/README.md) | Exact carries, dilation averages, zero-mode blindness, parity/strip equivalence and Beurling isolation. These identify what a new inequality must detect. |
| [TailArithmeticOfThePrimeOrbit](../TailArithmeticOfThePrimeOrbit/README.md) | Analytic transfer of finite collision counts to actual weighted moments and large-tail bounds. |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md), [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | Spectral receivers and impure models; their positivity mechanisms lie outside the core's inputs. |

Finite-field calibration asks for Hasse–Weil in counting language through
Stepanov. The corpus proves the sharp bound for squarefree odd-degree
hyperelliptic curves over finite fields of odd characteristic, including finite
extensions through splitting-field descent; see
[`HyperellipticDescent.lean`](../RHTower/HyperellipticDescent.lean).
General curves remain beyond this calibration. Tests also include Burgess,
smooth moduli and depth aspect, where arithmetic differencing can be exact.

Continuous Beurling systems test whether an argument uses integer carries at
all. The positive norm-three/norm-four system tests whether count precision
really isolates rational primes. The Golden discrete model supplies a further
discrete comparison. A theorem about all integer sets cannot by itself
distinguish rational primes; the prime amplitude must enter that distinction.

The [bounded-count new-zero construction](../RigidArithmeticOfCuts/ABoundedCountWithANewZero.lean)
has nonnegative integral multiplicative coefficients, but negative
multiplicities among its Euler generators. Its new zeros form vertical
progressions. It is therefore neither a positive-generator counterexample nor
a model with a single exceptional zero pair.

## 9. Traps

| Tempting inference | Obstruction |
|---|---|
| Joint product reconstruction forces one large projection. | Injectivity of the combined signature controls neither projection separately. General real-set examples also preclude a universal near-quadratic projection-growth principle. |
| Small real cells exclude circle alignment. | Different windings project to the same arc. Fixed finite supports return at unbounded heights. |
| Exact diagonal energy proves the required cancellation. | The diagonal regime can lie beyond the relevant scale; off-diagonal prime-density savings are still needed. |
| A factorization supplies a Type II saving. | Complete multiplicativity can leave the purported bilinear structure unchanged. The saving needs an additional arithmetic input. |
| One word, diagonal moments or one Taylor polynomial control the orbit. | Their proved ceilings do not disappear when the same information is repackaged. |
| An exact carry identity contradicts a zero mode. | The existing linear cut identities already hold on those modes. |
| Average control excludes an exceptional height or finite zero layer. | The required quantifiers are stronger than typical-height or integrated estimates. |
| Positive coefficients imply positive Euler generators. | The bounded-count new-zero construction separates these conditions. |
| Integer-norm count rigidity settles all Beurling systems. | Its factorization and gap arguments use integer norms and slope-one normalization. |
| A power-saving parity statement avoids the strip problem. | Its zero-free-strip consequence must be stated and proved. |

For the real-set projection limitation, the existing background references are
[Rudnev–Shkredov–Stevens](https://arxiv.org/abs/1607.05053) and
[Roche-Newton–Schildkraut–Warren](https://arxiv.org/abs/2606.24583).
Any stronger integer-phase claim must expose the extra arithmetic input.

## 10. What counts as progress

A contribution specifies an unconditional mathematical statement, its
arithmetic input, resolution and quantifiers, and a dependency-closed Lean
proof. Source declarations provide the detailed theorem catalogue; this
document records the field's objects, mechanisms and boundaries.

Structural identities, sharp resolution boundaries, exact classifications and
new invariants are foundations. An advance on the open RH-facing core must
also improve a named quantitative estimate or exclude a named obstruction,
and survive the relevant model tests. A failed route should expose its strongest
positive consequence, such as a rigidity law or exact boundary.

The programme is not complete with reconstruction alone. Its remaining tests
are fine-energy savings, growing-cutoff return bounds, moving-block control,
a carry constraint on finite oscillation, exceptional-zero count distance and
broader finite-field calibration. No improvement beyond Vinogradov–Korobov,
exclusion of a finite right-zero layer, or proof of RH is asserted here.
