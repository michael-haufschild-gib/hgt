# Möbius--Witt diagonal counterdivisor

- **ID:** `ULF-MWDC-1`
- **Stage:** 5-failed
- **Type:** conjecture killed; positive survivor promoted

## 1. Big-picture interpretation aimed for

ULF-CIT-2 forces a negative cofinal counterdivisor. The most literal source-native candidate is
Möbius inversion on integer divisibility: use signed Möbius weights to cancel the residue-cell
cyclotomic torsions before taking the entire completion. If this yielded a nonzero divisor-bearing
secondary determinant from ordinary integer formation, it would supply the missing completion
mechanism rather than another static addition--multiplication coherence law.

## 2. Corpus audit before conjecture

Search used `scripts/formal_tools.py research` for Möbius/Witt ghost products, cyclotomic torsion,
integral descent, Deninger completion, cross-prime compensation, and holomorphic unitization.

- Big-Witt ghost reconstruction and multiplication are already exact in `DeningerBigWittGhost`.
- Rational-Witt cyclotomic stages are exhausted in
  `DeningerRationalWittCyclotomicExhaustion`.
- A genuine off-diagonal degree-two compensator already exists in
  `DeningerBigWittFrobeniusCrossPairCoherentCompensator`.
- Scalar holomorphic unitizations already fail compact-open Xi landing.
- ULF-CIT-2 proves that preserving local cyclotomic torsion needs a negative counterdivisor.

No corpus theorem supplied the Möbius-weighted all-depth cancellation or checked its integrality.

## 3. Exact RH closure that was tested

The candidate would have closed RH only through this chain:

1. ordinary integer divisibility canonically generates Möbius counterweights;
2. their completed determinant cancels the cofinal local cyclotomic divisor while retaining a
   nonzero entire secondary torsion;
3. source properness confines that secondary torsion to the reflection-fixed locus;
4. exact Krein--Langer inertia then gives zero off-line multiplicity and RH.

Step 2 is false.

## 4. Killing theorem

The unique rational Euler weights whose ghost is supported only at the vacuum degree are

`q_n=lambda mu(n)/n`.

Their analytic product on the unit disc is exactly

`product_(n>=1)(1-z^n)^(q_n)=exp(-lambda z)`.

It is zero-free and retains no divisor. For nonzero integral `lambda`, infinitely many `q_p` are
nonintegral, so this is not an integral determinant/cyclotomic divisor decomposition. Conversely,
no nontrivial integral Euler product has finitely supported ghost sequence: Dold congruences force
every nonzero ghost through infinitely many prime extensions.

Dependency-closed proof: `pipeline/2-fully-proven/universal-law-field/
completion-index-transgression-mechanics/
integral-witt-ghost-infinite-tail-and-rational-vacuum-collapse-law.md`.

## 5. Strongest positive survivor

The obstruction is an integrality anomaly, not absence of a formal inverse. Rational completion
can isolate the vacuum only by leaving the integral divisor lattice and erasing all torsion.
Integral completion forces an infinite ghost tail. Hence the missing source object must redistribute
cyclotomic divisor through an all-depth interaction before determinant evaluation.

## 6. Verdict

- **Diagonal Möbius counterdivisor:** retired.
- **Finite-ghost integral completion:** impossible unless trivial.
- **Survivor:** integral all-depth interaction torsion and its `Q/Z` lifting anomaly.
- **RH gate discharged:** none.

