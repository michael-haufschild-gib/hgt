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
The useful refinement is a quantitative, finite-resolution law with exact
defects, including a description of its unresolved tail.

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

The existing foundations belong to their original programmes: the gauge
torus, its Haar laws, exponent dictionary and Adams operations; complete
bounded-overlap positivity and its Fourier margin; arithmetic Bézout and
linear Riemann–Roch; scaling-surface signature and tower laws. Their exact
Lean statements, rather than report summaries, govern every use here.

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
