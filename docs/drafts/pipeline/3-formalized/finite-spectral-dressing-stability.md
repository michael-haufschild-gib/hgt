# Finite-spectral dressing stability

- **ID:** `finite-spectral-dressing-stability`
- **Status:** `[PROVED IN LEAN] [BRIDGE] [CORPUS-USEFUL] [POSITIVE RESIDUE]`
- **Scope:** general hypertranscendental geometry, finite quantum clocks, finite Gibbs sectors,
  meromorphic source responses

## Statement

Let `f : C -> C` have infinite constant-coefficient spectral complexity: no nonzero polynomial
`L` satisfies `L(D)f = 0`.

If `f` is globally smooth and

`g(z) = sum_(i in S) a_i exp(c_i z)`

is any finite spectral response, then `f+g` again has infinite constant-coefficient spectral
complexity.

There is a second, source-facing form.  If `f` is meromorphic with a simple pole at one point, the
same conclusion holds with no global smoothness assumption: the finite spectral response is
entire and cannot cancel the pole.

Consequently, adding any finite-level Gibbs partition function to such a source cannot turn the
result into any finite-level Gibbs partition function.

## Positive mechanism

The theorem is not merely another finite-Hamiltonian no-go.  It proves a closure property of the
larger class already isolated by the corpus:

`infinite constant-coefficient spectral complexity`.

Let `A(D)` be the characteristic annihilator of the finite spectrum `g`.  If `L(D)(f+g)=0`, then
composition gives

`(A L)(D)(f+g)=0`.

The `g` term vanishes because `A(D)g=0`; hence `(A L)(D)f=0`.  Infinite spectral complexity forces
`A L=0`, and the monic nonzero polynomial `A` can be cancelled, giving `L=0`.

Thus every finite spectral dressing acts inside the infinite-complexity class.  A finite clock,
finite ancilla, finite Gibbs sector, or finite counterterm cannot erase the source's infinite
derivative-observation rank.

## Physics relation

For a finite-dimensional Hamiltonian with energies `E_a`, the complex-temperature partition
function is

`Z(z) = sum_a exp(-E_a z)`.

Its spectrum supplies the characteristic differential operator `prod_a (D+E_a)`.  The new result
shows that coupling this finite spectral response additively to an infinitely complex response
cannot make the combined clock finite-spectral.

This fits the relational-clock motif precisely: the invariant is the rank/recurrence structure of
the complete family of derivative readings.  No external time evolution is used.

Physics sources:

- A. Jackson, T. Kapourniotis, and A. Datta, *Partition Function Estimation: Quantum and
  Quantum-Inspired Algorithms*, arXiv:2208.00930, treats quantum partition functions at complex
  temperatures.
- Finite-dimensional Page--Wootters clocks encode histories in a stationary constrained state;
  the finite clock spectrum is the relevant finite recurrence, not an external evolution law.

## Formalization

Module:

- `formal/GaloisForLFunctions/HTGeometry/FiniteSpectralDressingStability.lean`.

Principal declarations:

- `constantCoeffDifferentialOperator_comp`;
- `constantCoefficientDifferentiallyTranscendental_add_finset_expSum`;
- `constantCoefficientDifferentiallyTranscendental_add_finset_expSum_of_simplePole`;
- `constantCoefficientDifferentiallyTranscendental_add_finiteComplexGibbsPartition`;
- `constantCoefficientDifferentiallyTranscendental_add_finiteComplexGibbsPartition_of_simplePole`;
- `add_finiteComplexGibbsPartition_ne_finiteComplexGibbsPartition`;
- `add_finiteComplexGibbsPartition_ne_finiteComplexGibbsPartition_of_simplePole`.

## Corpus value

1. Promotes the finite-Gibbs boundary from a one-shot exclusion to a stable positive class.
2. Applies directly to every corpus source whose infinite spectral complexity is certified by a
   simple meromorphic pole.
3. Removes repeated downstream obligations to prove that a finite spectral counterterm cannot
   cancel the source obstruction.
4. Extends beyond hypertranscendence: the stable class also contains differentially algebraic
   simple-pole functions such as the reciprocal function.
5. Supplies the exact algebra needed for finite system/clock/ancilla couplings without adding a
   temporal flow.

## RH impact and boundary

The result does not prove RH.  It strengthens the search filter:

- no finite-dimensional quantum-clock or finite Gibbs dressing can create the missing
  prime--archimedean orientation information;
- finite counterterms cannot remove infinite source complexity, so any viable physics route must
  use an infinite/source-selected state or energy rather than a finite spectral surrogate;
- for pole-bearing Xi-derived responses, the finite-dressing hypothesis can now be discharged
  mechanically.

The remaining RH-facing positive target is a source-derived infinite-state energy whose zero set
selects critical orientation.  The universal dephasing--Hamming theorem gives the finite model;
this theorem proves that replacing the source by a finite spectral clock cannot supply the missing
selection law.

## Boundary attacks

1. **No-go-only attack.**  The central result is closure of a strictly larger positive class under
   all finite spectral dressings.
2. **Hypertranscendence-only attack.**  The proof uses the weaker constant-coefficient spectral
   property and has a separate simple-pole route.
3. **Dynamics attack.**  Every identity is stated in derivative-observation and annihilator values;
   no Hamiltonian time propagation is assumed.
4. **Finite-wrapper attack.**  The new composition law and cancellation theorem remove a real
   repeated proof obligation; the result is not a renamed finite-Gibbs exclusion.

## Verification

- Exact target: `GaloisForLFunctions.HTGeometry.FiniteSpectralDressingStability`.
- Direct source check: touched Lean module.
- Axiom audit: expected only Lean/mathlib logical foundations.

## Direct RHTower application

Module:

- `formal/GaloisForLFunctions/RHTower/XiLogDerivFiniteSpectralDressing.lean`.

The existing unconditional simple-pole theorem for `xi'/xi` at each chosen actual Xi divisor point
instantiates the meromorphic closure law directly.  Therefore, for every finite dressing spectrum,

`xi'/xi + Z_dressing`

has infinite constant-coefficient spectral complexity and cannot equal any finite Gibbs partition
function `Z_target`.  This consumer uses the actual Xi divisor already formalized in the corpus and
requires no RH assumption or zero-simplicity assumption.

Declarations:

- `xiLogDeriv_add_finiteComplexGibbsPartition_constantCoefficientDifferentiallyTranscendental`;
- `xiLogDeriv_add_finiteComplexGibbsPartition_ne_finiteComplexGibbsPartition`.
