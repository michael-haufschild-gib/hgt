# Arithmetic Counting Positivity

**Central problem.** Produce positivity from arithmetic counts, with multiplicativity
selecting the untwisted source. A positive representation assumed at the outset does
not solve this problem. Neither does an identity that transfers an unproved sign.

Over finite fields, an independently proved point count can supply the Hodge
inequality. Over the integers, the complete Weil form has an exact arithmetic
description, but its global sign remains unproved. This programme studies what a
count must retain to produce that sign: arithmetic incidence, signed correlations,
the archimedean contribution, and the two poles.

Namespace: `GaloisForLFunctions.ArithmeticCountingPositivity`.
Umbrella: `ArithmeticCountingPositivity.lean`.

## 1. Motivation and scope

The explicit formula separates the complete form into Gamma, poles, and the prime
source. Replacing signed arithmetic by a majorant discards information that
distinguishes the von Mangoldt source from its Liouville twist. Multiplicativity
alone also permits that twist. A successful count must use a compatibility that
changes under twisting, and prove an inequality from that compatibility.

The discrete multiplicative walk provides a concrete starting point: its sharp
gap on the harmonic hyperplane is `2 log 2`, while the Liouville twin has zero gap.
The unresolved passage is from discrete energy to continuous overlapping sources
and then to a source-complete exhaustion. Finite-field counting, arithmetic
incidence, and signature counts are complementary models of how to make that
passage without assuming the desired positivity.

The programme includes RH-strength endpoints. A finite counting theorem, a
calibration, and an exhaustion theorem are distinct results; none substitutes for
the others. RH, finite off-line support, and the complete overlap transfer remain
open until their arithmetic inputs are proved.

## 2. Objects and language

| Object | Information retained |
|---|---|
| Complete Weil form `W = Gamma + poles - P` | Both poles, every prime power, all mixed entries and multiplicities |
| Twisted forms `W_lambda` | Which steps distinguish the actual arithmetic source from bounded twins |
| Multiplicative incidence and walk energy | Divisibility, prime-power edges, harmonic mass and signed edge correlations |
| Auxiliary sections | An explicit arithmetic construction, vanishing orders, dimension and complexity |
| Orbit Toeplitz forms | Every difference of translation indices, including cross-level entries |
| Signature counts | Positive and negative indices, trace and Frobenius energy, with multiplicities specified |
| Exhaustions | Source maps, domains, growing parameters, topology and uniform error bounds |

A **selective inequality** fails for at least one specified bounded twin. A
**parity-breaking input** changes under Liouville twisting. These are necessary
tests, not sufficient conditions for RH. A **counting producer** constructs the
objects being counted and proves their bound independently of the output sign.
A **receiver** translates an already supplied bound into a sign or index bound.
An **arithmetic Herglotz theorem** would be a producer for a particular
prime-generated Toeplitz form, beyond the abstract equivalence between positive
definiteness and positive representing measures.

Finite incidence cardinalities are exact counts. A count that supplies the
complete Weil sign must additionally reach square-root precision in the relevant
arithmetic error. These uses of the word count must not be conflated.

## 3. Mechanisms and tools to develop

1. **Counting and signed incidence.** Derive positive quadratic forms from explicit
   arithmetic fibres, retain their exact mixed entries, and identify which
   correlations change under multiplicative twists. Classify the information
   lost by using only cardinalities, ranks or absolute values.
2. **Selective overlap transfer.** Carry the discrete harmonic-complement gap into
   continuous atomic families beyond the Robin–Euler threshold. Pay the affine
   pole direction separately. An eigenvalue calculation on fixed arithmetic
   modes does not bound their whole complement.
3. **Arithmetic Herglotz theory.** Construct Toeplitz positivity from prime-side
   data including Gamma and poles. A zero-indexed positive measure cannot serve
   as the independent construction.
4. **Auxiliary vanishing over the integers.** Replace the finite-field lattice
   annihilator by arithmetic sections whose complexity and vanishing can both
   be controlled. Any sieve-based proposal must expose its parity-sensitive
   input before an asymptotic count is claimed.
5. **Finite-rank renormalization.** Produce a uniform index ceiling for the
   complete source. Finite-prime or higher-power estimates must retain their
   dependence on the remaining first prime layer. The endpoint is finite
   off-line support, which already implies a fixed zero-free strip.
6. **Exact inertia counting.** Separate a reflected pair from two critical
   points by an arithmetic observable sensitive to displacement. Trace and
   Frobenius bounds must control the actual signed form rather than replace
   it by an unsigned value moment.

## 4. Foundational pillars and their obligations

The programme is organized around the following mathematical pillars. A named
target in this table is an obligation, not a theorem asserted by this README.

| Pillar | Established input in the corpus | Required advance |
|---|---|---|
| Count before sign | Finite-field square-root counts and Hodge-index dictionary; hyperelliptic Stepanov construction | An independent integer-side construction with the required error |
| Arithmetic selection | Atomic selection theorem; sharp untwisted and Liouville gaps | An inequality paid by the selective input on overlapping complete sources |
| Exact local-to-global assembly | Complete-cell and orbit identities | Uniform control of every mixed term through exhaustion |
| Signature rather than assumed positivity | Rank–trace census and finite-index receivers | A new displacement-sensitive bound or uniform complete-source index ceiling |
| Obstruction with positive content | Lattice annihilator and parity obstructions | A sharp survivor: classification, retained energy, replacement count or invariant |

New pillar theorems belong here only after their precise statements and transitive
dependencies have passed the Lean kernel. Existing corpus results remain owned by
their original programmes; this programme should import them rather than rename
them as new contributions.

### The pole-angle transfer

For `H_N = sum_{n<=N} 1/n`, `S_N = sum_{n<=N} omega(n)/n` and a sign gauge
`omega(n)^2 = 1`, set `c_N = S_N/H_N`. Every vector `x` on the fixed harmonic
hyperplane satisfies

`Var_{1/n}(sqrt(n) omega(n) x_n) >= c_N^2 sum x_n^2`.

The projection of the gauged pole onto the original pole hyperplane attains
this geometric bound. Combining it with the corpus's sharp multiplicative
Poincaré inequality gives, for every positive `epsilon` and every sufficiently
large `N`,

`P_N(omega x) <= (log N - gamma - (2 log 2)c_N^2 + epsilon) sum x_n^2`.

The horizon is uniform over **all** sign gauges, including gauges depending on
`N`. No limit of the harmonic correlation is required. This is a quantitative
way to convert a signed harmonic count into a paid prime gap. Its domain is
the atomic prime form; carrying that payment into the complete overlapping
Weil form remains a separate analytic problem.

Lean: `harmonicCorrelation_sq_mul_mass_le_variance`,
`gaugeWitness_attains_variance_bound`,
`eventually_prime_gap_ge_squared_correlation` in
[`HarmonicCorrelationPaysThePrimeGap.lean`](HarmonicCorrelationPaysThePrimeGap.lean).

### Prime parity as an exact counting producer

Let `omega_p(n) = (-1)^(v_p(n))`. Every negative coordinate is `p` times a
positive coordinate, with harmonic weight divided by `p`. Writing `S_N` for
its signed harmonic count gives the exact identity

`p(H_N - S_N) = H_floor(N/p) + S_floor(N/p)`.

The right side counts positive parity fibres inside a smaller interval. Its
monotonicity yields

`S_N/H_N >= (p-1)/(p+1)`.

The excess is itself a count:

`(p+1)S_N - (p-1)H_N = sum_{N/p < n <= N} (1+omega_p(n))/n`.

It lies between zero and `2(1+log p)`, so `S_N/H_N` tends exactly to
`(p-1)/(p+1)`. The pole-angle transfer pays the unconditional gap

`2 log 2 ((p-1)/(p+1))^2`.

This is a concrete passage from arithmetic pairing to an energy inequality.
At `p=2` it pays `2 log 2/9`, whereas the Liouville twist at every prime has
zero positive hyperplane gap. The counting floor is sharp; optimality of the
resulting arithmetic gap is a different question.

Lean: `prime_parity_pairing`, `prime_parity_boundary_identity`,
`prime_parity_boundary_bounds`, `primeFlip_harmonicCorrelation_tendsto`,
`primeFlip_hasHyperplaneGap`, `two_adic_parity_has_gap_but_liouville_does_not` in
[`PrimeParityPairing.lean`](PrimeParityPairing.lean).

### A positive gap is weaker than selection

For every `a < 2 log 2`, a nontrivial single-prime flip has hyperplane gap at
least `a`, is completely multiplicative, and has the same polar matching
coefficient as the untwisted source. Its negative coefficients lie among
multiples of a prime of arbitrarily large size; the elementary count
`sum_{p|n, n<=N} 1/n = H_floor(N/p)/p` already suffices to prove this statement.

Thus separating zeta from Liouville by a positive margin does not identify
zeta among multiplicative twins. A transfer mechanism must retain further
source information, such as the finite-part rigidity studied by
Renormalized Arithmetic Potential Theory. Whether the **maximal** gap
`2 log 2` itself is rigid among completely multiplicative gauges remains
open; the squared-angle lower bound does not settle it.

Lean: `harmonicMass_multiples`,
`every_submaximal_gap_has_a_nontrivial_multiplicative_twin` in
[`SparsePrimeFlipsRetainPositiveGaps.lean`](SparsePrimeFlipsRetainPositiveGaps.lean).

### The boundary is a failure of the complete sign

The actual arithmetic weights `lambda_p(n) = omega_p(n) Lambda(n)` satisfy
`|lambda_p(n)| = Lambda(n)`. Each nevertheless has a compactly supported `C²`
test whose complete Weil functional is negative. Gamma, both poles and every
prime-power contribution remain in that functional.

The proof uses full-cone uniqueness: a full-Weil-positive weight must equal
`Lambda` at every integer at least two. But `lambda_p(p) = -log p`, with
`log p > 0`. Combining this with the preceding count proves that **no fixed
gap threshold below `2 log 2`, even together with multiplicativity and polar
matching, forces complete Weil positivity**.

The positive survivor is the exact parity count and its paid gap. It supplies
a useful energy estimate while locating a missing ingredient in any proposed
transfer: the transfer must read more of the source than these data.

Lean: `primeFlip_exists_negative_complete_test`,
`prime_parity_gap_and_complete_source_failure`,
`near_maximal_gaps_do_not_force_weil_positivity` in
[`NearMaximalGapsDoNotForceWeilPositivity.lean`](NearMaximalGapsDoNotForceWeilPositivity.lean).

## 5. Relation to the rest of the research

| Programme | Interface |
|---|---|
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | Intersection theory, effectivity, section counts and finite-field calibration |
| [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | Orbit correlation, Toeplitz index, orientation and finite-support receivers |
| [ArithmeticCorrespondencePositivity](../ArithmeticCorrespondencePositivity/README.md) | Sparse annihilators and the precise lattice requirement of Stepanov's mechanism |
| [SelectiveMultiscaleArithmeticPositivity](../SelectiveMultiscaleArithmeticPositivity/README.md) | Selective discrete margin and the continuous multiscale transfer problem |
| [RenormalizedArithmeticPotentialTheory](../RenormalizedArithmeticPotentialTheory/README.md) | Sharp multiplicative Poincaré inequality, prime-defect identity and finite-prime gauge constructions |
| [MultiplicativePositivityGeometry](../MultiplicativePositivityGeometry/README.md) | Arithmetic positive definiteness on the boundary and its limits as an interior forcing mechanism |
| [ArithmeticIncidencePositivity](../ArithmeticIncidencePositivity/README.md) | Actual prime incidence, atomic forms and allocation of surplus |
| [SignedArithmeticHodgeTheory](../SignedArithmeticHodgeTheory/README.md) | Complete source coordinates, Gamma payments and cross-level interactions |
| [ArithmeticIndexDescent](../ArithmeticIndexDescent/README.md) | Uniform index bounds for prime layers and the first-layer obstruction |
| [BezoutValuationIncidence](../BezoutValuationIncidence/README.md) | Divisor incidence and arithmetic correlations unavailable in arbitrary Beurling systems |

These programmes supply geometry, receivers and local estimates. Arithmetic
Counting Positivity owns independent counting constructions and the exact tests
of what information their positivity preserves.

## 6. Research questions

1. Why does the smallest prime determine both the dyadic generator and the
   sharp selective gap? Which counting identity singles out this scale?
2. What positive, quantitative content survives the parity barrier? Is the
   surviving quantity the harmonic-complement gap or a stronger invariant?
3. What replaces Frobenius's lattice spectrum for an integer-side auxiliary
   vanishing construction?
4. Which arithmetic observable distinguishes reflected pairs at depth of order
   `1 / log T`, where value moments and pair-correlation information can lose
   their displacement?
5. What arithmetic structure explains the heat-flow reality horizon
   `exp((27/40 + epsilon) / t)` and could control its degeneration as `t` tends
   to zero?
6. Which topology preserves the complete inequalities under source exhaustion
   despite the failure of uniform exponential graph control?
7. Can counting pay the first prime layer with a uniformly finite residual
   index, or pay the pole complement beyond the Robin–Euler threshold?
8. Is the maximal discrete gap rigid among multiplicative gauges? A positive
   gap, and even every fixed threshold below the maximum, is not rigid.

## 7. Traps and countermodels

| Temptation | Required correction |
|---|---|
| A Gram representation settles the Weil sign | Prove equality with the literal complete form; an unrelated positive form is insufficient |
| Multiplicativity breaks parity | Liouville is completely multiplicative; specify additional compatibility |
| A positive selective gap identifies the source | Single-prime flips have gaps arbitrarily close to `2 log 2` and preserve polar matching |
| Positive arithmetic weights select zeta | Test scalings, mixtures, golden data and Beurling systems |
| Finite counts or ranks retain signs | Record exact correlations and the information lost under reweighting |
| A fixed arithmetic mode controls a full spectrum | Bound its orthogonal complement uniformly |
| Finite-horizon positivity passes to the limit | State and prove the topology, error currency and uniformity |
| Positive measures explain arithmetic Herglotz | Construct their positivity from arithmetic, without using zeros as input |
| A conditional interface closes a proof | Discharge its mathematical input; do not store a missing estimate in a structure field |
| A no-go completes a route | Extract and formalize its strongest nontrivial positive survivor |

The battery consists of the Liouville twin, scaled von Mangoldt sources,
quadratic mixtures, the golden curve, Beurling over-regular systems and
Davenport–Heilbronn functions. A sufficient mechanism must identify the step
that excludes each applicable model. Elementary tools valid on the battery are
still useful, but must not be advertised as sufficient mechanisms.

## 8. Contribution and success criteria

A contribution supplies a new unconditional count, paid sign, energy bound,
index ceiling or sharp structural classification. It identifies its arithmetic
construction, the complete domain of validity, exact dependence on growing
parameters, its battery behaviour and its relation to an open mechanism.
Numerical experiments, renamed results, equivalences and hypotheses containing
the desired estimate do not meet the producer criterion.

Formal closure requires ordinary kernel-checked Lean proofs, audited transitive
axioms, no unproved analytic inputs and no trusted computation shortcuts. Each
finished module is wired into this programme's umbrella. Research records and
unproved arguments belong in pipeline cards rather than this foundational text.

First decisive success is selective positivity past the Robin–Euler point, a
new unconditional census bound from displacement-sensitive arithmetic, or a
uniform finite-index bound for the complete source. Full success also requires
the integer-side counting producer, arithmetic Herglotz construction, faithful
exhaustion, and answers to the structural questions above.
