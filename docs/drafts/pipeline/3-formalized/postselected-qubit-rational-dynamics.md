# Postselected-qubit rational dynamics

- **ID:** `postselected-qubit-rational-dynamics`
- **Stage:** 3-formalized
- **Type:** THEOREM PACKAGE (Lean 4) / MEASUREMENT-CONDITIONED QUBIT ALGEBRA
- **Scientific status:** `[FORMALIZED] [UNCONDITIONAL] [COHERENT PURE-STATE DYNAMICS]`
  `[DOES NOT FORMALIZE EXTERNAL RITT CLASSIFICATION]`
- **Paper theorem:**
  `../2-fully-proven/needs-audit/postselected-qubit-clock-integrability-fracture.md`
- **Lean module:**
  `formal/GaloisForLFunctions/HTGeometry/PostselectedQubitRationalDynamics.lean`

## Formalized objects

The module represents a real pure-qubit ray by the unnormalized amplitude pair `(z,1)`.  It
formalizes XOR plus successful zero-outcome postselection as

```text
(z,1) |-> (z^2,1)
```

and the balanced one-qubit rotation as

```text
(a,b) |-> (a+b,b-a).
```

Their composition is the homogeneous projective map

```text
(a,b) |-> (a^2+b^2,b^2-a^2),
```

with affine rational form `(z^2+1)/(1-z^2)`.

The module also formalizes the experimentally realized orthogonalizer by the homogeneous map

```text
(a,b) |-> (2ab,a^2+b^2),
```

whose affine form is `2z/(1+z^2)`.

## Unconditional theorem surface

For the balanced XOR protocol, the module proves:

- exact factorization through amplitude squaring and balanced rotation;
- primitive numerator `X^2+1` and denominator `1-X^2` have no common complex zero;
- exact derivative cross-numerator `4X`;
- projective orbit `0 -> 1 -> infinity`;
- projective critical cycle `infinity -> -1 -> infinity`;
- the reciprocal-coordinate displacement from `-1` has quadratic numerator `2X^2`;
- its second derivative at zero is exactly four;
- one exact affine step sends `2` to `-5/3`.

For the experimental control, it proves:

- the projective coordinate `(a,b) |-> (a+b,b-a)` sends the map exactly to coordinatewise
  squaring;
- the two orthogonal projective rays `+1` and `-1` are fixed;
- the derivative cross-numerator is `2(1-X^2)`, exposing those two critical points.

For quantum-state noncommutativity, define the unnormalized real pure-ray projector

```text
P(z)=[[z^2,z],[z,1]].
```

The module proves the exact commutator entry

```text
(P(z)P(w)-P(w)P(z))_(0,1)=(z-w)(zw+1)
```

and discharges it at the adjacent balanced-protocol orbit values `2` and `-5/3`.  Hence those
successive physical projectors do not commute.

## Verification

The smallest touched-file check passed:

```text
lake env lean GaloisForLFunctions/HTGeometry/PostselectedQubitRationalDynamics.lean
```

The exact-module cached build passed:

```text
lake build +GaloisForLFunctions.HTGeometry.PostselectedQubitRationalDynamics
```

An external scratch-file `#print axioms` audit covered the physical amplitude factorization,
primitive noncancellation, critical polynomial, infinity orbit and local quadratic criticality,
experimental squaring conjugacy, and noncommuting projector witness.  It reported only:

```text
propext, Classical.choice, Quot.sound
```

No aggregate build or repository-wide lint was run in the shared active tree.

## Formal boundary

The following remain paper-level external inputs:

- complex hyperbolicity from the critical orbit capture;
- existence and normalization of Poincare linearizers at repelling fixed points;
- invariance of critical preperiod/period under Moebius conjugacy;
- critical portraits of power, reciprocal-power, Chebyshev, and Lattes maps;
- the Ritt--Becker--Bergweiler DA/HT classification;
- the autonomous stable-tail classification and its orbifold-current reconstruction;
- the physical success probabilities and ensemble-resource accounting.

None is inserted as an assumption.  The formal package is unconditional projective, polynomial,
and matrix algebra.

## Gates

- [x] Existing HTGeometry and generated declaration index checked first.
- [x] Physical two-copy amplitude factorization formalized.
- [x] Balanced conditional rational map formalized projectively and affinely.
- [x] Primitive noncancellation formalized.
- [x] Finite and infinite critical algebra formalized.
- [x] Exact projective critical orbits formalized.
- [x] Experimental control map and squaring conjugacy formalized.
- [x] Experimental critical fixed rays formalized.
- [x] Exact noncommuting adjacent-projector witness formalized.
- [x] Touched-file check passed.
- [x] Exact-module build passed.
- [x] Axiom audit passed.
- [ ] External complex-dynamical classification internalized in Lean.
- [ ] Quantum instrument and success-probability model internalized in Lean.
