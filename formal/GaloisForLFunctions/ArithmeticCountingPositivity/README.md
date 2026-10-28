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

## 5. Relation to the rest of the research

| Programme | Interface |
|---|---|
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | Intersection theory, effectivity, section counts and finite-field calibration |
| [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | Orbit correlation, Toeplitz index, orientation and finite-support receivers |
| [ArithmeticCorrespondencePositivity](../ArithmeticCorrespondencePositivity/README.md) | Sparse annihilators and the precise lattice requirement of Stepanov's mechanism |
| [SelectiveMultiscaleArithmeticPositivity](../SelectiveMultiscaleArithmeticPositivity/README.md) | Selective discrete margin and the continuous multiscale transfer problem |
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

## 7. Traps and countermodels

| Temptation | Required correction |
|---|---|
| A Gram representation settles the Weil sign | Prove equality with the literal complete form; an unrelated positive form is insufficient |
| Multiplicativity breaks parity | Liouville is completely multiplicative; specify additional compatibility |
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
