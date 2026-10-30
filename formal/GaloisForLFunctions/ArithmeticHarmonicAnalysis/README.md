# Arithmetic Harmonic Analysis at Critical Resolution

Namespace `GaloisForLFunctions.ArithmeticHarmonicAnalysis`; umbrella
`ArithmeticHarmonicAnalysis.lean`.

## Why

The ring of integers has an additive and a multiplicative harmonic analysis.
The additive characters live on the circle; the multiplicative characters live
on the prime gauge torus. Successor relations connect them. The complete Weil
form also involves the archimedean term and both poles. At bounded atomic
overlap, the corpus identifies a positive Fourier remainder after the
successor shells have been assembled. At growing overlap that remainder
shrinks, and estimates with a fixed loss cease to decide the sign.

This programme studies identities coupling these structures, their resolution
cost, and the arithmetic information they retain at the trivial gauge point.
Its intended endpoint includes RH. That endpoint, a quadratic arithmetic
section count, and a producer beating the divisibility ledger remain open.
Naming them does not provide their proofs.

## Objects and language

Write `G` for the product of circles indexed by primes. A point `x` gives a
completely multiplicative unit-modulus function `χₓ` on positive integers.
The identity `0` has `χ₀(n)=1`; the Liouville point has value `−1` at every
prime. Adams operations multiply prime phases: `χ_{ψᵏx}(n)=χₓ(n)^k`.
The corpus's `ArithmeticCorrelationGeometry.GaugeTorus` is indexed by all
natural numbers and ignores non-prime coordinates. Statements of uniqueness
here concern its arithmetic twists, equivalently its quotient by those unused
coordinates.

| Object | Mathematical role |
|---|---|
| Successor defect `χₓ(n+1)−χₓ(n)` | Additive compatibility of multiplicative phases |
| Finite prime coordinates and integer observations | Two different notions of resolution |
| Adams fixed loci | Torsion constraints on phases; possible auxiliary vanishing loci |
| Finite Dirichlet polynomials | Arithmetic auxiliaries and harmonic probes |
| Dirichlet points and vertical shifts | Special locus, conductor and height |
| Ramanujan sums and successor lattices | Additive major arcs of multiplicative charge |
| Complete atomic Weil forms `W(φ,c,N)` | All mixed entries, prime powers, Gamma and both poles |
| Conductor energies `E_m(c)` and margin `E(c)` | Positive Fourier tails at bounded overlap |
| Gauge exponent `θ_a(x)` | Growth of twisted arithmetic partial sums |
| Section multiplicities and negative index | What a producer or arithmetic ceiling must control |

*Gauge-invariant* means unchanged by every gauge translation. *Finite prime
dependence* means determined by one fixed finite set of prime coordinates.
*Resolution* must name its observations: integer cutoff, conductor, atomic
overlap and Fourier bandwidth are not interchangeable. *Critical* means that
the available positive margin and the unpaid arithmetic or boundary term have
comparable size, with a specified normalization.

Two finite quotients must be distinguished. Order-`d` Adams torsion reads
`v_p(n) mod d` at each sampled prime. Dirichlet characters of conductor `Q`
read `n mod Q` on integers coprime to `Q`. The first groups frequencies by
power classes; the second groups them by additive congruences. A root order
is not a conductor. In particular, the full independent torsion grid can
contain far more points than a Dirichlet character family.

## Questions

1. Which additive defects quantitatively determine a gauge point? What is lost
   when only finitely many integers or primes are observed?
2. What does vanishing on an Adams fixed locus cost in support, degree and
   multiplicity? Which additive constraints can improve that cost?
3. Which values at `0` follow from exact arithmetic identities, and which
   require discrepancy estimates? What class of statistics could admit a
   meaningful typicality theorem at `0` after its pole is removed?
4. How far does complete Weil positivity persist on explicit growing overlap
   schedules? Is its transition governed by `E(c) log N`, or by a different
   invariant involving the boundary and conductor gaps?
5. How does overlap distinguish a prime flip, a finite or cofinite flip set,
   a twin tail, and the Liouville point? How does that resolution compare with
   integer and conductor observations?
6. What two-dimensional arithmetic object has an independently defined
   quadratic section count? Can that count bound the complete negative index?

## Mechanisms and tools

**Additive rigidity.** Multiplicativity determines phases from primes;
successor compatibility propagates the value at `1` through all integers.
For `D_N(x)=max_{1≤m<N}|χₓ(m+1)−χₓ(m)|`, multiplicative halving gives

`|χₓ(n)−1|≤2k D_N(x)` whenever `1≤n≤N` and `n≤2^k`.

The reconstruction loss is logarithmic in the observed integer. Moreover,
`D_N(x)=0` exactly when `χₓ(p)=1` for every prime `p≤N`.
[DyadicSuccessorRigidity.lean](DyadicSuccessorRigidity.lean) proves both
statements. Prime phases above `N` remain free; finite rigidity supplies
no asymptotic cancellation estimate.
For two gauges the same estimate is
`|χₓ(n)−χᵧ(n)|≤2k D_N(x−y)`, with zero relative defect exactly when their
prime values through `N` agree.

**Adams vanishing.** A fixed-point condition gives root-of-unity identities on
each prime coordinate. Auxiliaries must distinguish vanishing of values from
vanishing of jets, and finite coordinate quotients from vanishing on the
entire gauge torus. The desired tool compares their exact algebraic cost
with Stepanov's finite-field mechanism.

**Poisson repayment.** Assemble successor shells with their Ramanujan weights
before estimating. The bounded-overlap positive remainder is a Fourier
square. A critical-window calculus must retain conductor dependence, the
top-row boundary and the complete archimedean contribution.

**Poisson–Weil decomposition.** The target is an exact arithmetic construction
`W=P+Z`, with a positive `P` containing every legitimately paid term and an
explicit residual `Z`. Bounding `Z` by `o(E(c))` on an RH-complete schedule is
an open theorem, not a permissible hypothesis of a claimed solution.

**Exponent and approximation theory.** Haar-typical square-root cancellation
is an averaged calibration. Transferring it to `0` requires point-specific
structure. Convolution identities and Adams operations must be audited for
their fixed points: a bootstrap whose endpoint is exponent `1` produces no
zero-free strip.

**Quadratic counting.** A tensor product of linear section spaces already
has a quadratic dimension. A useful surface requires more: arithmetic
sections, nonnegative intersection of effective divisors, and a count that
pays the complete form. Dimension multiplication alone supplies no Hodge
index.

## Foundations and intended pillars

The first exact resolution law concerns the full order-`d` prime torsion
grid. For a finite prime set `P`, write

`F(t)=Σ_n a_n exp(2πi Σ_{p∈P} t_p v_p(n)/d)` and
`A(r)=Σ_{v_P(n)≡r (mod d)} a_n`.

Then

`Σ_t F(t) conj(exp(2πi⟨t,r⟩/d)) = d^|P| A(r)`,

`Σ_t |F(t)|² = d^|P| Σ_r |A(r)|²`.

Thus every collision is explicit: vanishing means cancellation within each
valuation-residue fibre. Below integer support `2^d`, there are no collisions
among positive integers when all their prime factors are sampled. The
resulting arithmetic auxiliary vanishes on the entire `ψ^(d+1)` fixed locus
exactly when all its coefficients vanish. At the boundary, `χ(2^d)−1`
vanishes there. Fourier inversion also recovers every individual coefficient
below that boundary.

The statements are in
[TorsionFourierResolution.lean](TorsionFourierResolution.lean),
[TorsionArithmeticResolution.lean](TorsionArithmeticResolution.lean), and
[AdamsFixedLocusResolution.lean](AdamsFixedLocusResolution.lean).
This imports classical finite Fourier inversion into the arithmetic support
filtration and identifies its exact first obstruction. It bounds support
length; coefficient height, evaluation size and prime counting require
different inputs.

Higher resolution separates each valuation as `v_p(n)=b_p+d k_p(n)`,
`0≤b_p<d`. Define the explicit Newton coordinates

`J(b,α)=Σ_{v(n)≡b (mod d)} a_n ∏_p binom(k_p(n),α_p)`.

At integer support `n<2^(dr)`, all quotient multiindices have total order
below `r`: unique factorization gives `2^(d Σ_p k_p(n))≤n`. A maximal
quotient monomial is detected by its own Newton coefficient, because a
nonzero binomial product requires componentwise domination. Consequently
the coordinates `J(b,α)`, `|α|<r`, determine the entire coefficient array.
Their Fourier sampling formula is the same residue inversion with weights
`∏_p binom(k_p(n),α_p)`.

[ResidueNewtonDetection.lean](ResidueNewtonDetection.lean) contains the
triangular detection theorem;
[ArithmeticNewtonResolution.lean](ArithmeticNewtonResolution.lean) supplies
the arithmetic length bound.

The differential bridge is explicit. Set `E_p=z_p ∂/∂z_p` and
`L_(b,α)=∏_p ∏_{j<α_p}(E_p−b_p−dj)`. Then

`Σ_t conj(χ_b(t)) L_(b,α)F(t)`
`= d^|P| d^|α| (∏_p α_p!) J(b,α)`.

Euler operators act diagonally on monomials. Fourier averaging selects the
residue, and falling factorials give the normalization. A word of `k` Euler
factors lowers any point-ideal multiplicity by at most `k`, by Leibniz.
Centered Taylor coefficients identify these ideal powers with vanishing
of ordinary analytic mixed derivatives.

Consequently a nonzero arithmetic auxiliary with full multiplicity at least
`r` on the entire `ψ^(d+1)` fixed locus must reach integer support `2^(dr)`.
Here full multiplicity means all complex prime-coordinate mixed derivatives
of total order below `r`; the polynomial evaluates to the original arithmetic
twist sum. The integer polynomial `(z₂^d−1)^r` attains the threshold: its
largest arithmetic frequency is exactly `2^(dr)`, its top coefficient is
one, and every `d`th root has multiplicity exactly `r` in that coordinate.

The mechanism is formalized in
[EulerOperatorsLowerMultiplicity.lean](EulerOperatorsLowerMultiplicity.lean),
[TorsionEulerJetExtraction.lean](TorsionEulerJetExtraction.lean), and
[MixedJetMultiplicity.lean](MixedJetMultiplicity.lean). The arithmetic
theorem and boundary are
[AdamsMultiplicityResolution.lean](AdamsMultiplicityResolution.lean) and
[TorsionMultiplicityBoundary.lean](TorsionMultiplicityBoundary.lean).
This sharp support law gives no coefficient-height gain and does not produce
an auxiliary beating the divisibility cost. Classification of all auxiliaries
attaining the minimum support is a further rigidity question.

Vertical derivatives alone have a different cost. The auxiliary
`log(3)(z₂−1)−log(2)(z₃−1)` has zero value and first derivative on the
logarithmic line at the identity, but nonzero derivative in the `z₂`
coordinate. Its support ends at `3`, below `2²`.
[VerticalJetsMissTransverseDirections.lean](VerticalJetsMissTransverseDirections.lean)
checks the distinction. Its real logarithmic coefficients do not settle
the integer-coefficient auxiliary problem. In fact, at an algebraic torus
point an algebraic-coefficient polynomial satisfies

`d/ds F(x_p exp(s log p))|_(s=0)=0 ⇔ ∂_p F(x)=0 for every p`.

The chain rule gives `Σ_p x_p ∂_p F(x) log p`; Baker's independence over
the algebraic numbers forces each coefficient to vanish. This exact
first-order distinction is proved in
[AlgebraicVerticalFirstJets.lean](AlgebraicVerticalFirstJets.lean).

For two distinct primes, every fixed-degree homogeneous family
`(log p)^j(log q)^(T−j)`, `0≤j≤T`, is independent over the algebraic
numbers. Dividing by `(log q)^T` reduces this to Gelfond–Schneider
transcendence of `log p/log q`.
[TwoPrimeHomogeneousLogRigidity.lean](TwoPrimeHomogeneousLogRigidity.lean)
proves this classical consequence. It excludes homogeneous relations of
each degree separately; it does not establish algebraic independence of
the two logarithms or a uniform height bound. The higher-order analytic
jet application remains separate.

These finite laws use the same prime-exponent lattice in two ways. Torsion
reduces valuations modulo its order; successor ratios read differences of
valuation vectors. Unique factorization supplies the arithmetic support
bound, while multiplicative halving makes successor reconstruction
logarithmic. This is an exact coupling of additive and multiplicative
observations. Its finite scope explains both its force and its unresolved
prime tail.

The existing foundations belong to their original programmes: the gauge
torus, its Haar laws, exponent dictionary and Adams operations; complete
bounded-overlap positivity and its Fourier margin; arithmetic Bézout and
linear Riemann–Roch; scaling-surface signature and tower laws. Their exact
Lean statements, rather than report summaries, govern every use here.

Single-prime overlap resolution already has quantitative bounds in
[TheFlipThresholdGrowsLikeAPowerOfThePrime.lean](../RenormalizedArithmeticPotentialTheory/TheFlipThresholdGrowsLikeAPowerOfThePrime.lean).
For universal positive constants `κ,K` and sufficiently large primes `p`,
the complete flipped form is eventually positive on every nonzero atomic
family when `max(c,1)^8 log p≤κ√p`. It is eventually negative on the
prime-square trial when `c≥K` and `c^7≥Kp`. These are two sufficient
regions, with fixed `p,c` before the horizon tends to infinity. They do not
give a uniform growing-horizon law or a sharp transition exponent.

New pillars sought here are quantitative additive rigidity, exact Adams
auxiliary costs, a resolution–distance law, an explicit growing positive
window, a margin-based receiver, and a quadratic section mechanism. A theorem
becomes a pillar only after its full statement and transitive dependencies
are checked in Lean. Open pillars are not counted as established results.

## Traps

| Tempting inference | Missing mathematical content |
|---|---|
| Every non-invariant, infinitely dependent statistic is typical at `0` | Those restrictions do not control a statistic at a distinguished point; an admissible class is essential |
| The unique Adams fixed point has a typical exponent | Algebraic uniqueness gives no cancellation estimate |
| Small successor defects at one cutoff determine the whole point | Prime coordinates above the cutoff remain invisible |
| Root-of-unity vanishing supplies high multiplicity for free | Value constraints and derivative constraints have different costs |
| Every fixed overlap is positive, so a prescribed growing schedule is positive | Uniform rates and the shrinking margin are required |
| A positive part pays the complete form | Mixed terms, boundary terms and the same reserve may be unpaid or counted twice |
| A quadratic dimension is an arithmetic surface | Effectivity and its intersection law are missing |
| An equivalence with RH is a new inequality | A new inequality needs an independently proved arithmetic input |

## Place in the wider research

| Programme | Interface |
|---|---|
| ArithmeticGaugeTheory | Gauge space, special points, exponents, Adams operations, divisibility constraints |
| CriticalArithmeticCorrelationTheory | Successor shells, conductor spectrum, bounded-overlap positivity |
| RenormalizedArithmeticPotentialTheory | Margins, gauge charge and flip thresholds |
| SquareRootThreshold | Complete receivers and the overlap needed to detect zeros |
| ArithmeticCastelnuovoSeveri | Section effectivity, quadratic counting, Hodge index and finite-field calibration |
| ArithmeticOrientationGeometry | Orbit correlations, rates, complete index and theta Riemann–Roch |
| CompletedArithmeticForms | Exact completion of arithmetic and boundary terms |
| BiarithmeticGeometry, SignedSuccessorArithmetic | Simultaneous additive and multiplicative constraints |

This programme owns the coupling of additive compatibility, multiplicative
phase resolution and critical margins. It imports existing constructions
instead of making parallel versions of them.

## Contribution and success criteria

A contribution gives a new unconditional identity, classification, paid
inequality, count or sharp obstruction with a nontrivial positive survivor.
It states its resolution and normalization, identifies its arithmetic input,
and explains what it changes in one of the six questions. An abstract bound
with the missing estimate as a premise does not qualify as production.

A proposed sufficient mechanism must be tested against Liouville and prime
flips, cofinite flips and twin tails, perturbed von Mangoldt sources, the
golden datum, over-regular Beurling systems, Davenport–Heilbronn examples and
Haar-random gauges wherever those examples inhabit its domain. Passing a
test means proving selectivity, not declaring the example inadmissible.
Finite-field counting, bounded-overlap positivity, flip thresholds, the
two-thirds census and Siegel's theorem are calibration targets.

The first decisive successes would be an explicit unconditional growing
positive window; an RH receiver controlled by the profile's Fourier margin;
an auxiliary gaining multiplicity beyond its divisibility cost; or a
point-specific exponent bound below `1`. Complete success additionally
requires the critical positivity identity, the producer and the quadratic
count. All proofs require kernel-checked Lean closure with no extra analytic
premises. RH and the other unresolved endpoints must remain visibly open
until those proofs exist.
