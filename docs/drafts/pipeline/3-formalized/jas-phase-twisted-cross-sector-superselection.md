# JAS phase-twisted cross-sector superselection

- **ID:** JAS-PTCSS-1
- **Stage:** 3-formalized
- **Type:** UNCONDITIONAL THEOREM / HARD ROUTE-CLASS FALSIFIER
- **Source:** read-only `rh-current-frontier-map.md`, surviving nonseparable JAS `ORIENT + COMP` core

## Hard frontier target

The diagonal multiplicity completion is terminal, but RFHM support/history can alter the prime
phase in each completion channel. Let `chi_n(p)` and `psi_m(p)` be arbitrary unimodular prime-phase
families. The `n`-th left channel carries the twisted prime-Poisson measure at `sigma`; the `m`-th
right channel carries the twisted reflected measure at `1-sigma`.

Prove:

1. off wall, every left/right phase-sector pair is mutually singular for arbitrary twists;
2. pairwise disjoint operator families remain disjoint after dependent `ell2` direct-sum completion,
   where Hilbert fibre and operator may vary with the channel;
3. therefore no nonzero closed densely-defined `C(PrimeTorus)`-linear sewing exists between the
   countable twisted reflected sums off wall;
4. on wall, classify the exact positive survivor by weighted relative phase defect: summable defect
   gives equivalent sectors, divergent defect gives mutually singular sectors.

Success kills all countable phase/history relabellings of the prime-Poisson carrier, not merely
coefficient-blind multiplicity. Surviving JAS would require a representation whose spectral measure
class itself is changed by genuinely infinite prime--grade incidence, rather than a countable sum of
ordinary phase-twisted sectors.

## Corpus basis

All conjecture-forming searches used `scripts/formal_tools.py research`. Corpus provides:

- exact Kakutani equivalence/singularity for circle-Poisson product measures;
- arbitrary unimodular twisted prime-Poisson parameters and exact one-twist weighted phase defect;
- every right-of-wall twist is equivalent to untwisted/Haar class;
- untwisted left-of-wall prime-Poisson measure is singular to Haar;
- base `C(PrimeTorus)` operator-family disjointness from measure singularity;
- constant-fibre `ell2` amplification stability, but no dependent cross-sector theorem.

Radial norms of twisted parameters do not depend on phase. Thus off-wall pairwise singularity should
be phase-uniform. The dependent block-matrix theorem then tests all countable support/history sectors
simultaneously.

## Conjecture loop

### C1 — phase-uniform reflected singularity

Prove twisted measure is singular to Haar at and left of wall using phase-invariant radial norm
divergence. Transfer across the right-of-wall Haar-equivalent class.

### C2 — dependent cross-amplification disjointness

Construct a uniformly bounded coordinatewise operator on `ell2(n, H_n)`. If every coordinate block
from left `n` to right `m` is an impossible intertwiner, coordinate projections plus single density
kill the entire direct-sum intertwiner.

### C3 — closed-relation no-go

Use adjoint covariance and the general closed-relation splitting theorem to force every output to
zero off wall.

### C4 — sharp critical survivor

Compute the two-twist parameter displacement and apply Kakutani dichotomy. Retain exactly the
weighted square-summable relative phase cocycles as possible critical sewing sectors.

## Hostile falsification

1. Arbitrary phase at every prime and every countable channel.
2. Channel-dependent Hilbert fibres, not repeated copies of one representation.
3. Closed densely-defined single-valued relations, not bounded maps alone.
4. Sharp positive critical classification, not only an off-wall no-go.
5. No Xi zero, RH premise, computation, finite cutoff, or added axiom.

## Novelty status

`[PROVED IN LEAN] [CORPUS-NOVEL CROSS-SECTOR THEOREM] [TARGETED EXTERNAL NO-MATCH]`

Classic substrate is not claimed novel: Kakutani's 1948 product-measure dichotomy supplies the
abstract equivalence/singularity engine, and direct-sum disjointness is standard representation
theory. Corpus also already had the one-sided twist-versus-untwisted defect theorem. Targeted
search found no prior statement combining arbitrary two-sided prime-phase twists, reflected
`sigma ↔ 1-sigma` Poisson sectors, dependent countable Hilbert sums, and closed source-linear JAS
sewing. Novel claim is restricted to that combined route theorem and its exact two-twist critical
classification.

## Formal result

Generic infrastructure:

- `formal/GaloisForLFunctions/HTGeometry/L2DependentOperatorFamilyCrossDisjointness.lean`
- `L2DependentSum`, `l2DependentDiagonal`, coordinate singles and projections;
- `adjoint_l2DependentDiagonal`;
- `operatorFamiliesDisjoint_l2DependentCrossSum`: pairwise cross-disjoint coordinate
  representations remain disjoint after arbitrary dependent Hilbert `ell²` completion.

JAS application:

- `formal/GaloisForLFunctions/RHTower/JointAncestryPhaseTwistedCrossSectorSuperselection.lean`
- `twistedPrimePoissonMeasure_reflection_mutuallySingular_of_ne_half`: every arbitrary left twist
  is singular to every arbitrary reflected right twist off wall;
- `normSq_twistedPrimePoissonParameter_sub_twisted_eq`: exact two-twist local displacement
  `p^(-2 sigma) * ‖chi_p - psi_p‖²`;
- `twistedPrimePoissonMeasure_pair_mutuallyAbsolutelyContinuous_iff`: exact global two-twist
  Kakutani equivalence criterion;
- `twistedPrimePoissonMeasure_half_pair_mutuallyAbsolutelyContinuous_iff`: at `sigma = 1/2`,
  equivalence is exactly summability of `‖chi_p - psi_p‖² / p`;
- `twistedPrimePoissonCrossSumMul_operatorFamiliesDisjoint_of_ne_half`: all countable
  channel-dependent phase/history sums remain cross-disjoint off wall;
- `twistedPrimePoissonCrossSumMul_nonzeroClosedSourceLinearSewing_forces_half`: any nonzero closed
  densely-defined source-linear sewing between those sums forces `sigma = 1/2`.

All four conjectures C1--C4 are proved without weakening.

## RH-route consequence

Countable phase/history relabelling is terminal as an off-wall JAS mechanism. Neither arbitrary
prime phases per channel, different `L²` measure fibres, countable channel mixing through a closed
relation, nor unbounded densely-defined sewing evades the critical wall. A surviving JAS proof must
change spectral measure class through genuinely infinite prime--grade incidence that is not a
countable direct sum of ordinary phase-twisted sectors.

Positive survivor is sharp: critical sectors may communicate precisely across weighted-`ell²`
relative phase cocycles. Divergent critical phase defect is a superselection boundary, not merely a
failure of the proof.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/JointAncestryPhaseTwistedCrossSectorSuperselection.lean`
  passed.
- `lake build GaloisForLFunctions.RHTower.JointAncestryPhaseTwistedCrossSectorSuperselection`
  passed as exact leaf build.
- Both modules wired into their umbrellas; umbrella builds intentionally not run.
- Axiom probes for reflected singularity, critical two-twist equivalence, dependent cross-sum
  disjointness, and closed-sewing wall theorem report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Formal lint reported no error in either new module; repository-wide failure consists of unrelated
  concurrently unwired modules.
- No premise about Xi zeros, RH, numerical experiment, finite cutoff, or added axiom occurs.

## Log

- 2026-08-28 — selected after countable constant-multiplicity JAS completion was proved terminal.
  Frontier map read-only; conjecture derived from corpus twist/Kakutani theorems.
- 2026-08-28 — C1--C4 proved and exact leaf audited. Route class killed off wall; weighted critical
  relative phase cocycle retained as exact positive survivor.
